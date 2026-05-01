# I1 Bundle — Stage 9 Figure Review (Stub-Class)

**Bundle:** I1 — Verification methodology with worked cases
**Tier:** 3 (Infrastructure — CPC | Phys. Rep.)
**Reviewer agent:** `physics-qa:figure-reviewer`
**Run mode:** stub-class (bundle has zero figures authored)
**Review date (UTC):** 2026-05-01T13:40:02Z
**Phase / Sub-wave:** Phase 7a, sub-wave 7a.2 (I1 lift execution)

---

## Verdict

`pending-figures` (non-FAIL).

The I1 paper draft (`papers/I1/paper_draft.tex`, 1338 lines, 14 sections) is currently text-only. The `papers/I1/figures/` directory contains no PNG, SVG, or PDF assets. The draft body contains zero `\includegraphics` calls and zero `figure` environments. There is therefore nothing to review for rendering quality, physics accuracy, or style consistency.

This is the expected state for a Phase 7a sub-wave 7a.2 stub-completion. Stage 9 records `pending-figures` and surfaces a recommendations list of figures the bundle should add before Stage 13 sign-off.

## Anchors consulted (per `docs/agents/claims-reviewer-bundle-prompts.md` §I1)

1. FirstOrderKMS Aristotle counterexample case (Phase 1)
2. Gap-solution-bounded counterexample case (Phase 5d)
3. Chirality-wall axiom decomposition case (Phase 5h)
4. The 14-stage Wave Execution Pipeline
5. The supersession ledger pattern + Pipeline Invariant #13 (Wave 6)

Bundle source: paper15 substantially expanded + worked-case curated set. Stage-13 profile is software/methodology — each worked case must trace to a reproducible Aristotle run ID or commit-pinned counterexample (this constrains future caption content for figures I1-FIG-4 through I1-FIG-6).

## Figures reviewed

0.

## Recommendations — figures the bundle should add

Priority labels: **P0** = required for the bundle's central pedagogical claim; **P1** = strongly recommended; **P2** = strengthening (not strictly required by anchor list but materially raises Phys. Rep. readiness).

### P0 — required

- **I1-FIG-1. Three-layer Python ↔ Lean ↔ Aristotle architecture diagram** (§2, line 171)
  Schematic of the bidirectional formula ↔ theorem correspondence. Single most-cited concept in the draft and the canonical entry-point figure for the physicist audience the paper targets. Must encode pipeline invariants #1 (`formulas.py` canonical) and #4 (every formula has a Lean theorem) as labeled edges.

- **I1-FIG-2. 14-stage Wave Execution Pipeline diagram** (§6, line 442)
  Bundle anchor #4. The pipeline is the core methodological contribution and is described over ~150 lines of prose; one figure is essential. Must show feedback loops (Stage 13 BLOCKER → supersession-ledger → Stage 6 redo) and label which stages are LLM-driven vs human-gated vs automated.

### P1 — strongly recommended

- **I1-FIG-3. Sentence-state cluster diagram** (§8, line 677)
  PAPER_STRATEGY.md §2.4 lists this as the third planned figure. Node-link graph showing sentences → formulas → theorems with cross-paper consistency edges in a distinct color. Makes the n-to-many provenance abstraction concrete via one Tier-1 paper's worked example.

- **I1-FIG-4. FirstOrderKMS counterexample 9-component grid** (§3, line 235)
  Bundle anchor #1. 3×3 KMS-component grid; binary coloring (originally-constrained 4 cells vs originally-missing 5 cells). Caption must cite the Aristotle run ID and commit hash per the Stage-13 anchor profile.

### P2 — strengthening

- **I1-FIG-5. Gap-solution-bounded counterexample witness plot** (§4, line 301)
  Bundle anchor #2. Literal data plot of the explicit unbounded-in-G witness function. Only worked-case figure that is a true physics plot rather than a schematic, so it carries disproportionate weight for empirical character. Caption must cite the Aristotle counterexample-extraction run ID + commit hash.

- **I1-FIG-6. Chirality-wall axiom decomposition tree** (§5, line 364)
  Bundle anchor #3. Top-down tree: root = original opaque axiom; leaves = 4 focused hypotheses + 1 4+1D gapped-interface assumption. Each leaf annotated with evidential status (`1+1D verified`, `2+1D verified`, `4+1D conjectural`).

## Style requirements (apply to all six recommended figures)

Per `CLAUDE.md` Key Conventions:

- **Plotly only** (not matplotlib).
- **Colorblind-accessible** palette (blue/amber, not red/green).
- Project canonical palette where applicable (Steinhauer/Rb87 steel-blue `#2E86AB`, Heidelberg/K39 berry `#A23B72`, Trento/Na23 amber `#F18F01`, dispersive sage-green `#5C946E`, dissipative carmine `#E63946`). For abstract/diagrammatic figures (I1-FIG-1, I1-FIG-2, I1-FIG-3, I1-FIG-6) the palette is more flexible but should remain colorblind-safe.
- Serif fonts (CMU/Times family) preferred for axes; sans-serif acceptable for purely schematic diagrams.

## Blockers

None. (Stub-class run; absence of figures is the expected state at sub-wave 7a.2 stub-completion, not a blocker against Stage 9.)

## Advisories

- **I1-ADV-1.** `stage9_status = pending-figures` until at least the three P0/P1 architecture/pipeline/provenance figures (I1-FIG-1, I1-FIG-2, I1-FIG-3) exist and pass rendering + style checks.
- **I1-ADV-2.** Captions for I1-FIG-4 through I1-FIG-6 must cite the corresponding Aristotle run IDs and project commit hashes per the bundle's Stage-13 profile (\"each worked case must trace to a reproducible Aristotle run ID OR commit-pinned counterexample\"). Coordinate with the Stage 10 `physics-qa:claims-reviewer` pass for caption ↔ `ARISTOTLE_THEOREMS` registry consistency.

## Next actions

1. Author I1-FIG-1, I1-FIG-2, I1-FIG-3 (P0/P1 core) into `papers/I1/figures/`.
2. Add `\begin{figure}\includegraphics` blocks at the section anchors above (lines 171, 442, 677).
3. Re-invoke `physics-qa:figure-reviewer` with `bundle_target=I1` for a non-stub Stage 9 review once figures land.
4. Coordinate with Stage 10 `physics-qa:claims-reviewer` so caption claims trace to Aristotle run IDs and commit hashes.

---

*JSON sibling artifact:* `papers/I1/figures/figure_review_report.json`
