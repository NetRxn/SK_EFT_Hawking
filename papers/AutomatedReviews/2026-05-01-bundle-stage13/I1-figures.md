# I1 Bundle Stage-9 Figure Review (Round 2)

**Bundle:** I1 — Verification methodology with worked cases
**Tier:** 3 (software/methodology — CPC | Phys. Rep.)
**Review date:** 2026-05-01T16:30:00Z
**Round:** 2 (round-1 stub at 2026-05-01T13:40:02Z established the 6-figure recommendation set; all 6 figures now authored and reviewed)
**Reviewer:** physics-qa:figure-reviewer (bundle-aware mode, bundle_target=I1)
**Output paths:**
- `papers/I1/figures/figure_review_report.json` (JSON-structured per-figure verdict)
- `papers/AutomatedReviews/2026-05-01-bundle-stage13/I1-figures.md` (this document)

---

## 1. Summary

All six figures recommended in the round-1 stub review have been authored
and pass Stage-9 review at the round-2 pass. Four figures pass cleanly;
two carry minor advisories that are Stage-9 → Stage-10 handoff items, not
blockers.

| Figure | Section | Round-1 Rec | Status | Aristotle Run / Type |
|--------|---------|-------------|--------|----------------------|
| `i1_fig1_three_layer_architecture.png` | §2 | I1-FIG-1 (P0) | **PASS** | Architecture schematic |
| `i1_fig2_pipeline_14_stages.png` | §6 | I1-FIG-2 (P0) | **PASS w/ advisory** | Process flow |
| `i1_fig3_sentence_state_clusters.png` | §8 | I1-FIG-3 (P1) | **PASS** | Schematic (validate.py CHECK 21) |
| `i1_fig4_firstorderkms_grid.png` | §3 | I1-FIG-4 (P1) | **PASS** | Worked case — Aristotle run `270e77a0` |
| `i1_fig5_gap_counterexample.png` | §4 | I1-FIG-5 (P2) | **PASS** | Worked case — Aristotle run `79e07d55` |
| `i1_fig6_chirality_wall_tree.png` | §5 | I1-FIG-6 (P2) | **WARNING** | Worked case — batch-level only |

**Overall verdict:** PASS with two non-blocking advisories
(`I1-FIG-2-ADV`, `I1-FIG-6-ADV`). Recommend
`bundle_metadata.json: stage9_status = "yellow"` to reflect the open
advisories, with promotion to `green` after the Stage-10 round-2 pass
resolves the fig6 caption/labeling and Aristotle batch-ID pinning.

---

## 2. Round-1 Recommendation Disposition

| Round-1 ID | Round-1 Priority | Title | Round-2 Status |
|------------|-------------------|-------|----------------|
| I1-FIG-1 | P0 | Three-layer architecture diagram | Authored, PASS |
| I1-FIG-2 | P0 | 14-stage pipeline diagram | Authored, PASS w/ advisory |
| I1-FIG-3 | P1 | Sentence-state cluster diagram | Authored, PASS |
| I1-FIG-4 | P1 | FirstOrderKMS counterexample grid | Authored, PASS |
| I1-FIG-5 | P2 | Gap-equation counterexample plot | Authored, PASS |
| I1-FIG-6 | P2 | Chirality-wall decomposition tree | Authored, WARNING |

All 6/6 round-1 recommendations addressed. 0 P0/P1 blockers remain.

---

## 3. Per-Figure Findings

### 3.1 `i1_fig1_three_layer_architecture.png` — PASS

**§2, paper_draft.tex line 240–254. Round-1 rec: I1-FIG-1 (P0).**

Three stacked colored bands (Layer 1 Python — steel blue; Layer 2 Lean
— amber; Layer 3 Aristotle — sage). Vertical labels "formalize" /
"automate" annotate the downward arrows; the curved carmine arrow on
the right marks "counterexample or refinement" feedback flow back to
Layer 1. Each band's metadata strip lists canonical-module pointers
consistent with CLAUDE.md Pipeline Invariants #1–4:
- Layer 1: `formulas.py (canonical) · constants.py · visualizations.py · tests/ · domain modules (wkb/, adw/, vestigial/)`
- Layer 2: `lean/SKEFTHawking/*.lean · zero sorry · 1 axiom · 5229 theorems · ExtractDeps.olean axiom-closure graph`
- Layer 3: `submit_to_aristotle.py · ARISTOTLE_THEOREMS registry · priority batch plan · zero-sorry closures (e.g. run 270e77a0)`

The 5229 / 1 axiom / zero sorry counts match the Phase 7a.0.2 counts.json
regen baseline (memory: 5229 theorems / 5204 substantive / 0 sorry / 1
axiom). The Layer 3 cross-reference to run `270e77a0` ties the figure
to §3's worked case. **No rendering, physics, style, or caption issues.**

### 3.2 `i1_fig2_pipeline_14_stages.png` — PASS w/ advisory

**§6, paper_draft.tex line 550–564. Round-1 rec: I1-FIG-2 (P0).**

5×3 grid layout shows all 15 cells (S1, S2, S3a, S3b, S4–S14). New
stages (3a Lean MCP loop, 13 Adversarial review, 14 Meta-process QI)
correctly highlighted in amber per the legend; existing stages in steel
blue. Stage labels match WAVE_EXECUTION_PIPELINE.md.

**Advisory `I1-FIG-2-ADV` (rendering — minor):** Several gate-text
strings appear truncated at cell boundaries:
- S1 "Constants & param[s]"
- S2 "Lean-theorem ref pre[…]"
- S8 "[ga]te: fig functions registered" (left edge crowded)
- S10 "claims-reviewer pas[s]"
- S12 "Inventory + Heatmap" (acceptably tight)

The truncation is a layout-tightness issue, not a missing-content issue.
Mitigation: Table 1 (`tables/table1_stages.tex`, `\input` on line 569)
is auto-generated from `WAVE_EXECUTION_PIPELINE.md` and carries full
gate text — figure plus table together carry the load. **Non-blocking.**

**Suggested fix (deferrable):** widen each cell ~12% or shorten gate
strings ("Constants & params" → "Constants", "claims-reviewer pass" →
"claims pass").

### 3.3 `i1_fig3_sentence_state_clusters.png` — PASS

**§8, paper_draft.tex line 801–816. Round-1 rec: I1-FIG-3 (P1).**

Three-paper layout (Paper A Tier 1, Paper B Tier 1, Paper C Tier 2)
with six sentences each. Cluster C2 (amber, `cross_bundle: true`)
spans all three papers per the §8 caption claim. Single-bundle
clusters C1 (steel blue, paper A internal) and C3 (sage, paper B
internal) are distinct. Edge style (dashed for single-bundle, solid
for cross-bundle) helps disambiguate the `cross_bundle: true` semantic.

Faint-grey "unclustered sentence" nodes (B2, B5, A4, A6, C5, C6) match
the legend's fourth row — intentional encoding, not a rendering issue.

Schematic figure (caption explicitly says "schematic") so no specific
Aristotle run ID is required. **No issues.**

### 3.4 `i1_fig4_firstorderkms_grid.png` — PASS

**§3, paper_draft.tex line 322–336. Round-1 rec: I1-FIG-4 (P1).
Worked-case figure — Aristotle run `270e77a0` cited.**

Two 3×3 grids of nine real coefficients `{r1..r6, i1, i2, i3}`:

- **Left panel (original weak axiom, "4 constrained / 5 unconstrained,
  counterexample c = (0,0,0,0,0,0,0,1,0)"):** four cells colored
  steel-blue ("constrained"): r1, r2, i1, i2. Five cells in grey
  ("free"): r3, r4, r5, r6, i3. Cell i2 highlighted in carmine with
  "counterexample i2 = 1" annotation.
- **Right panel (corrected FirstOrderKMS, "all 9 constrained, i3 = 0
  explicit"):** all nine cells amber ("constrained").

The Aristotle run ID `270e77a0` is cited in the figure title, which
satisfies the Tier-3 reproducibility anchor requirement ("each worked
case must trace to a reproducible Aristotle run ID"). **No issues.**

### 3.5 `i1_fig5_gap_counterexample.png` — PASS

**§4, paper_draft.tex line 403–418. Round-1 rec: I1-FIG-5 (P2).
Worked-case figure — Aristotle run `79e07d55` cited.**

Single-curve plot of Δ(G) on G ∈ [0, 12] with parameterization
N_f = 1, Λ = 1, c_4 = 1 stated in the title:
- Trivial branch Δ = 0 for G < G_c (dotted grey, near origin).
- Non-trivial branch (steel-blue solid) rises monotonically.
- Cutoff line Λ = 1 (dashed black horizontal).
- Saturation marker at G* ≈ 6.518 = 2/(1 - log 2) where Δ = Λ
  (amber filled circle).
- Amber-shaded region G ≥ G* with annotation "folklore claim Δ < Λ
  fails for G ≥ G*" and subtitle "Aristotle run 79e07d55: corrected
  statement adds G < G* hypothesis."

The numerical value G* = 2/(1 - log 2) ≈ 6.518 matches the saturation
point shown on the plot. Aristotle run ID `79e07d55` cited in caption
— Tier-3 anchor met. **No issues.**

This is the only literal physics-data plot in the bundle (per
round-1's note that this "carries disproportionate weight in
establishing the paper's empirical character").

### 3.6 `i1_fig6_chirality_wall_tree.png` — WARNING

**§5, paper_draft.tex line 502–518. Round-1 rec: I1-FIG-6 (P2).
Worked-case figure — batch-level Aristotle citation only.**

Treemap (nested-rectangles) layout. Root: carmine bar
`sm_no_nu_R_ewbg_doubly_forbidden`. Two amber obstruction blocks:
"Z₁₆ chirality wall" (left+center) and "Crossover (sphaleron
suppression)" (right). Three sage-green pillar boxes:
- Pillar A — anomaly (containing Sublemma A.1 "z16-anomaly orthogonality")
- Pillar B — fermion content (containing Sublemma B.1 "no-vR ⇒ Pillar B intact")
- Pillar C — wall form (containing Sublemma C.1 "wall-form ⇒ EWBG forbidden")

The Crossover obstruction contains three steel-blue sublemma boxes
(2.1 sphaleronSuppression ∈ [0,1], 2.2 ¬viable ⇒ EWBG forbidden, 2.3
wall ∨ ¬viable ⇒ EWBG forbidden).

**Substantive content correct.** The figure successfully conveys
"monolithic root → two obstruction layers → three structural pillars
+ crossover side → tractable sublemmas" which is the §5 claim.

**Advisory `I1-FIG-6-ADV` (style — three sub-issues):**

1. **Layout deviation from round-1 spec.** Round-1 recommended
   "Top-down tree; root labeled with the original opaque axiom; leaves
   labeled with the 4 focused hypotheses + 1 dimensional assumption."
   The implementation chose a treemap layout instead. Treemap is a
   reasonable visualization for hierarchical decomposition data; the
   caption explicitly says "treemap layout" so the deviation is
   disclosed. **Acceptable but flagged.**

2. **Visible-vs-stated leaf count mismatch.** §5 prose (line 498–500)
   and the figure caption both reference *nine* sub-lemmas. The figure
   exposes only six labeled leaves (A.1, B.1, C.1, 2.1, 2.2, 2.3). The
   gap appears to be that Pillar C contains a large unlabeled region
   that may represent two further sublemmas (C.2, C.3) and Pillar A or
   B may absorb a third. Either:
   - **(a)** annotate the 3 currently-unlabeled treemap regions with
     their sublemma names; or
   - **(b)** revise the caption to read "9 sub-lemmas across 6 labeled
     leaf groups" or equivalent.

   The Tier-3 reproducibility claim ("all 9 sub-lemmas closed in a
   single Aristotle priority batch") is intact in the prose; only the
   figure-caption visual contract is loose.

3. **Aristotle batch-ID pinning.** The caption says "all 9 closed in
   a single Aristotle priority batch" without pinning a specific run
   ID. Tier-3 profile permits batch-level citation when the batch is
   registry-resolvable; flag for Stage-10 claims-reviewer (round 2)
   to pin a specific batch identifier from `ARISTOTLE_THEOREMS` if
   available, else leave batch-level.

**Non-blocking.** Recommend fix at Stage 10 round 2.

---

## 4. Tier-3 Reproducibility Audit

Per the Stage-13 anchor profile for I1: "each worked case must trace
to a reproducible Aristotle run ID OR commit-pinned counterexample."

| Figure | Type | Run ID / Source | Status |
|--------|------|-----------------|--------|
| fig1 | Architecture schematic | n/a (illustrative cross-ref to 270e77a0 in metadata strip) | PASS |
| fig2 | Process flow | n/a | PASS |
| fig3 | Provenance schematic | n/a (validate.py CHECK 21 reference in caption) | PASS |
| fig4 | Worked case 1 | Aristotle run `270e77a0` (cited in title) | PASS |
| fig5 | Worked case 2 | Aristotle run `79e07d55` (cited in caption) | PASS |
| fig6 | Worked case 3 | Batch-level only — specific run ID not pinned | ADVISORY (Stage-10 to resolve) |

Schematic figures (fig1, fig2, fig3) appropriately do not cite
Aristotle run IDs (their content is architecture/process, not
worked-case proof artifacts). The Tier-3 anchor scopes the run-ID
requirement to worked-case figures.

---

## 5. Cross-Bundle Consistency Walk

I1 is a Tier-3 single-paper bundle (no parallel bundle members), so
intra-bundle figure-claim drift checks are vacuous. Cross-bundle
checks are limited to the worked-case anchors that overlap with other
bundles:

- **§3 FirstOrderKMS (Phase 1):** numerical claim i_3 = 0 in the
  noise-floor formula referenced in Tier-1 D2/D3 deep papers. Stage-10
  round 2 should verify the noise-floor constant in fig4 caption ↔
  D2/D3 §6 numerical content via `validate.py` CHECK 21 cluster walk.
- **§4 gap-solution-bounded (Phase 5d):** the saturation coupling
  G* = 2/(1 - log 2) is referenced in Tier-1 deep papers covering the
  gap equation. Stage-10 to confirm cluster cross-reference.
- **§5 chirality-wall (Phase 5h, EWBaryogenesisChiralityWall):** the
  9-sublemma decomposition is cited in Phase 6c.1/6c.2 papers (paper33
  EWBG); Stage-10 to confirm cluster cross-reference for the
  sphaleron-suppression hypothesis surfaced in §5.

No `BundleFigureMismatch` findings detected at the figure-rendering
level. Numerical-content cross-bundle consistency is the Stage-10
claims-reviewer's domain.

---

## 6. Recommendations and Next Actions

1. **Stage-10 round-2 hand-off (claims-reviewer, bundle_target=I1):**
   - Verify fig4 caption ↔ ARISTOTLE_THEOREMS registry consistency
     for run `270e77a0`.
   - Verify fig5 caption ↔ ARISTOTLE_THEOREMS registry consistency
     for run `79e07d55`.
   - Attempt to pin fig6 to a specific Aristotle batch ID from
     `ARISTOTLE_THEOREMS`; if not available, accept the batch-level
     citation.
   - Walk validate.py CHECK 21 (`bundle_consistency`) to confirm
     fig4 i_3 = 0 ↔ D2/D3 noise-floor cluster, fig5 G* ↔ Tier-1
     gap-equation cluster, fig6 sphaleron-suppression ↔ paper33 cluster.

2. **Optional figure refinements (non-blocking):**
   - fig2: widen cells ~12% or shorten gate strings to eliminate
     truncation.
   - fig6: either label 3 missing leaves OR update caption to read
     "9 sub-lemmas across 6 labeled leaf groups".

3. **Bundle metadata update:**
   - `stage9_status = "yellow"` (advisories only; no blockers).
   - `last_stage9_review = "2026-05-01T16:30:00Z"`.
   - `advisories_open` adjusted to reflect resolution of round-1
     "pending-figures" advisories plus the two new figure-level
     advisories `I1-FIG-2-ADV` and `I1-FIG-6-ADV`.

4. **Promotion path to `stage9_status = "green"`:** resolve fig6
   advisory at Stage-10 round 2 (caption + batch-ID), plus optional
   fig2 cell-width tweak. Both are paper-pass items, not full-redo
   items.

---

## 7. Verdict

**Stage 9 round 2 verdict: PASS with advisories.**

All six round-1 figure recommendations addressed. Tier-3 reproducibility
anchors met for fig4 and fig5 worked-case figures. fig6 carries a
batch-level citation that requires Stage-10 confirmation to upgrade to
a specific run ID. fig2 has minor cell-text truncation that is
non-blocking. Schematic figures (fig1, fig2, fig3) all clear style
checks per CLAUDE.md colorblind-accessibility convention.

Recommend `bundle_metadata.json: stage9_status = "yellow"` (advisories
only). `green` promotion deferred to post-Stage-10 round 2.
