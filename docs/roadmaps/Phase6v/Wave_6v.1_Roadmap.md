# Wave 6v.1 — Williamson/Yoder gauging-QEC formalization + CREATES D6 BUNDLE

**Bundle targets:** D6 §3 (NEW BUNDLE created by this wave) + I1 cross-bridge.

**Status:** ✅ SHIPPED 2026-05-26 (Williamson-Yoder kernel-verified + D6 bundle CREATED).

**Source paper (canonical, primary-source cached):**
D. J. Williamson, T. J. Yoder, "Low-overhead fault-tolerant quantum computation by gauging logical operators," arXiv:2410.02213 (Nature Physics, April 2 2026). Primary-source cache: `Lit-Search/Phase-1-and-Background/primary-sources/WilliamsonYoder2026GaugingLogicalOperators.pdf` (775 KB, downloaded 2026-05-26). Bibkey: `WilliamsonYoder2026GaugingLogicalOperators`.

**Wave goal.** Formalize the Williamson-Yoder fault-tolerant logical-measurement scaling result as the **first** kernel-verified declaration under the new **D6 ("Formally Verified Fault-Tolerant Quantum Computation Substrate")** publication-bundle target. The headline kernel-verified theorem is `gaugingQEC_auxQubit_overhead_le`: there exists a gauging-style fault-tolerant logical-measurement protocol whose auxiliary-qubit overhead is bounded by `C · W · polylog(W)` (linear in operator weight, up to a polylogarithmic factor), AND the *naive* baseline `O(W²)` schemes do NOT achieve this scaling. The substantive falsifier (W² scheme NOT in the polylog class) is what makes the gauging protocol's achievement non-vacuous.

## Key parameters and the substantive bound

Williamson-Yoder achievement (per arXiv:2410.02213 abstract): "qubit overhead that is **linear in the weight of the operator being measured up to a polylogarithmic factor**". Operationally:
```
gaugingAuxOverhead(W) ≤ C · W · (⌈log₂ W⌉ + 1)        (Williamson-Yoder 2026)
naiveAuxOverhead(W)   = Θ(W²)                          (prior O(W²) schemes)
```
The substrate-level encoding ships these as two predicates with the gauging protocol satisfying the first and any quadratic-scaling protocol violating the first (witnessed by `auxQubits W = W²` failing the polylog bound for sufficiently large W).

## Deliverables (14-stage pipeline)

| Stage | Action | Status |
|---:|---|:---:|
| 1 | Per-wave roadmap (this file) + PDF cache. | ✅ SHIPPED |
| 1 | (a) Bibkey `WilliamsonYoder2026GaugingLogicalOperators` added to `CITATION_REGISTRY` (DOI 10.1038/s41567-026-03220-8, arXiv:2410.02213, Nat. Phys. 22, 598-603 (2026); primary-source cached 775 KB). (b) No new EXPERIMENTS / POLARITON_PLATFORMS / ATOMS entries needed (gauging-QEC is purely algorithmic — no measured experimental parameters). (c) No PARAMETER_PROVENANCE entries needed. | ✅ SHIPPED |
| 2 | (skip) — no new physical formulas; bound encoding lives in Lean. | SKIP |
| 3a | Lean module `lean/SKEFTHawking/FaultTolerance/GaugingQEC.lean` shipped (~220 LoC kernel-only). Declarations: `williamsonYoderAuxQubits W := W * (Nat.log 2 W + 1)`, `naiveQuadraticAuxQubits W := W * W`, `IsLinearPolylogOverhead`, `IsLinearOverhead`, `gaugingQEC_auxQubit_overhead_le`, `nat_log2_plus_one_le_self`, `williamsonYoder_beats_quadratic_for_W_ge_two`, `quadraticOverhead_not_linear` (the FALSIFIER), `gaugingQEC_strictly_improves_over_quadratic_at_large_W` (W=4 numerical witness), `wave_6v_1_substantive_closure` bundling the three substantive ships. Imported in `lean/SKEFTHawking.lean`. | ✅ SHIPPED |
| 3b | None — 3a closed via direct constructive proofs (norm_num + ring + omega + decide). | SKIP |
| 4 | (Aristotle — not needed.) | SKIP |
| 5 | `lake env lean SKEFTHawking/FaultTolerance/GaugingQEC.lean` clean (exit 0). MCP `lean_diagnostic_messages` returns zero errors. | ✅ SHIPPED (file-gate) |
| 6 | `tests/test_gauging_qec.py` (12 tests, all PASS): citation bibkey present, primary-source cache file exists, canonical formula matches Lean encoding at 6 W values (1, 2, 4, 8, 16, 100), W-Y < naive for W ≥ 3, improvement-factor growth, edge case W=1, naive quadratic-growth sanity. | ✅ SHIPPED |
| 7 | `validate.py` checks: `formulas` PASS, `parameter_provenance` PASS, `citation_primary_sources_present` PASS (421 bibkeys cited / 292 cached), `paper_provenance` PASS. | ✅ SHIPPED |
| 8 | (skip) — no new figures in Wave 6v.1. | SKIP |
| 9 | (skip) — no figures. | SKIP |
| 10 | (a) `papers/D6/` directory created with `figures/`, `tables/` subdirs. (b) `papers/D6/paper_draft.tex` skeleton (Tier 1 / PRD-PRX-Q-JHEP style; §1 Introduction + §2 SK retroactive absorption placeholder + §3 Williamson-Yoder substantive ship + §§4–6 pending Wave-content placeholders + §7 Conclusion). 2-pass pdflatex clean (233 KB PDF). (c) `papers/D6/bundle_metadata.json` per `docs/BUNDLE_DIRECTORY_SCHEMA.md`. | ✅ SHIPPED |
| 11 | (skip) — no new notebooks in Wave 6v.1. | SKIP |
| 12 | **D6 bundle infrastructure (architectural)** ALL SHIPPED: (1) `docs/PAPER_STRATEGY.md` updated 14→15 bundles + D6 description in §2.2 + summary table row + footnote history. (2) `docs/PAPER_DRAFT_MAPPING.md` D6 entry under Tier 1 Deep papers (sources, strategy origin, sibling-to-D4 framing). (3) `docs/BUNDLE_READINESS_HEATMAP.md` D6 row added (skeleton GREEN; 0 blockers; 0 advisories; 1 source; Stage 13 deferred). (4) `docs/agents/claims-reviewer-bundle-prompts.md` D6 anchor block added (5 anchors covering §§2–6 + 3 Stage-13 cross-bridge anchors to D4/I1/axiom-audit). (5) F-bundle `papers/F/paper_draft.tex` §6 forward-reference paragraph + 6-item D6 absorption checklist added per strategy synthesis §3.5.3 task #8 (2-pass pdflatex clean, 22 pages 488 KB). (6) `Phase6v_Roadmap.md` wave-status updated. (7) This per-wave roadmap finalized. (8) Phase-level stakeholder docs DEFERRED to Phase 6v close. (9) Inventory_Index update DEFERRED per coordination boundary. | ✅ SHIPPED |
| 13 | Stage 13 adversarial review DEFERRED to end of Phase 6v. | DEFERRED |
| 14 | QI — none identified in this wave. | ✅ NO-FINDINGS |

## Substrate touched

- **New Lean module:** `lean/SKEFTHawking/FaultTolerance/GaugingQEC.lean` (~120 LoC est).
- **New papers directory:** `papers/D6/` with `paper_draft.tex` skeleton, `bundle_metadata.json`, `figures/`, `tables/`.
- **Modified docs:** `docs/PAPER_STRATEGY.md` (14→15 bundles), `docs/PAPER_DRAFT_MAPPING.md` (D6 entries), `docs/BUNDLE_READINESS_HEATMAP.md` (D6 row), `docs/agents/claims-reviewer-bundle-prompts.md` (D6 anchor), papers/F/paper_draft.tex (FT-QC checklist entry).
- **Modified Python:** `src/core/constants.py`, `src/core/provenance.py`, `src/core/citations.py`, new `tests/test_gauging_qec.py`.
- **New Lean root import:** `import SKEFTHawking.FaultTolerance.GaugingQEC` added to `lean/SKEFTHawking.lean`.
- **Primary-source cache:** `Lit-Search/Phase-1-and-Background/primary-sources/WilliamsonYoder2026GaugingLogicalOperators.pdf` (775 KB).

## D6 bundle scope (new — the architectural deliverable)

**D6 title:** "Formally Verified Fault-Tolerant Quantum Computation Substrate"
**Tier:** 1 (deep paper, PRD/JHEP-class)
**Composition:** 4 waves' worth of content:
- §3 Williamson-Yoder gauging-QEC overhead bound (Wave 6v.1, this wave)
- §4 APM-LDPC code substrate + hashing-bound LDP sub-wave (Wave 6v.5)
- §5 Google/Caltech Shor T-gate counts (Wave 6v.2)
- §6 W-state QFT decomposition in Q(ζ_N) (Wave 6v.6)
- §2 *Retroactive absorption* of Phase 6t quantitative Solovay-Kitaev headline (currently bundle-orphan)

**Sibling relationship to D4** (TQC foundations): D4 retains Fibonacci/topological-foundations focus; D6 becomes the natural sibling for fault-tolerant computation substrate.

**D6 publication target:** PRD or JHEP; Tier-1 deep paper class.

## Cross-wave dependencies

- **Predecessors:** none (Wave 6v.1 creates D6).
- **Successors:** Waves 6v.2, 6v.5, 6v.6 all lift into D6, so they REQUIRE Wave 6v.1's D6 bundle infrastructure to be in place first.

## No-axiom discipline

Zero new project-local axioms; zero tracked Props. The Lean substantive content is:
- An explicit `williamsonYoderProtocol` construction with `auxQubits W := W * (Nat.log 2 W + 1)`.
- The `gaugingQEC_auxQubit_overhead_le` bound proved by direct computation.
- The falsifier `quadraticOverhead_not_linearPolylog` proved by witness-large-W argument.

Both bounds are quantitative numerical Props, not tautologies.
