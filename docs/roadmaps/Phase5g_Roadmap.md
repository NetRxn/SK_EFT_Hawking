# Phase 5g: Matrix-Free CG + Mathlib Contribution + Paper Submission

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Follows Phase 5f (TQFT, emergent gravity bounds, figure-eight knot)*

**Entry state:** 1363 theorems, 96 modules, 36 sorry (Aristotle). L=8 RHMC running (epochs, n_md_steps=80). Braided MTCs + TQFT + knot invariants complete. Wen coupling deficit formalized.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. For matrix-free CG: read deep research `Phase-5g/Sparse staggered fermion matrix.md`
> 4. For Mathlib: read deep research `Phase-5h/Contributing categorical infrastructure to Mathlib4.md`

---

## 0. Motivation

Three bottlenecks block the research program:
1. **Computational:** L=12+ MC impossible with dense CG (220GB). Matrix-free with torch.roll() reduces to ~130MB.
2. **Credibility:** Mathlib PR for PivotalCategory/FusionCategory/etc. starts the credibility flywheel (Lean/Mathlib community → quantum computing → consulting).
3. **Publication:** 14 papers, 1363 theorems, 0 submitted. Ship the work.

---

## Track A: Matrix-Free Staggered Dirac Operator (L=12+ unlock)

**Deep research complete:** `Phase-5g/Sparse staggered fermion matrix.md`
**Key finding:** Matrix-free with `torch.roll()` is the right approach (not explicit sparse). PyTorch sparse is broken on Apple Silicon (MKL dependency). Every production lattice QCD code uses matrix-free.

### Wave 1 — Matrix-Free Operator Implementation
**Goal:** Replace dense A@v with torch.roll()-based stencil.

- [ ] Implement `apply_staggered_dirac(v, U, eta, mass, L)` using torch.roll + einsum
- [ ] Precompute staggered phases η_μ(x) = (-1)^{x₀+...+x_{μ-1}} once per lattice
- [ ] Handle h-field coupling on diagonal (on-site term)
- [ ] Implement D†D application (needed for CG: D†D + σ_k shifts)

**Deliverables:**
- `src/vestigial/stencil_dirac.py` — matrix-free operator (~60 lines core)
- `tests/test_stencil_dirac.py` — verify matches dense matvec at L=4,8 to machine precision

### Wave 2 — CG Solver Integration
**Goal:** Drop-in replacement in existing RHMC.

- [ ] Replace dense matvec in CG loop with matrix-free apply
- [ ] Verify multi-shift CG still works (shifts are diagonal: D†D + σ_k → add σ_k*v)
- [ ] Profile at L=8: matrix-free vs dense time/traj
- [ ] Verify checkpoint/resume unchanged (no matrix stored, rebuilt from h-field)

**Deliverables:**
- Modified `src/vestigial/hs_rhmc_torch.py` — swap dense → matrix-free
- Comparison report: L=8 dense vs matrix-free (should be identical physics, faster)

### Wave 3 — L=12 Production
**Goal:** First L=12 RHMC production.

- [ ] Configure coupling grid with critical region (g=3-5)
- [ ] Run via `run_rhmc_epochs.sh --l 12 --n-md-steps 60`
- [ ] Preliminary analysis
- [ ] Binder crossing: L=8 vs L=12

**Deliverables:**
- L=12 data in `data/rhmc/L12_g*.npz`
- Visualization + comparison with L=8

---

## Track B: Mathlib Contribution

**Deep research complete:** `Phase-5h/Contributing categorical infrastructure to Mathlib4.md`
**Key findings:** Zulip-first, small incremental PRs, strict style (100-char lines, 2-space indent, trailing-prime pattern). PivotalCategory explicitly listed as "future work" in Rigid.Basic. Key reviewers: Joël Riou, Adam Topaz, Johan Commelin.

### Wave 4 — Zulip Engagement + Style Adaptation
**Goal:** Introduce project on Zulip, adapt first PR candidate to Mathlib style.

- [ ] Join leanprover.zulipchat.com, post in #new-members and #mathlib4
- [ ] Describe the categorical infrastructure scope
- [ ] Adapt PivotalCategory to Mathlib conventions (Struct/Full split, trailing prime, aesop_cat auto-params, 100-char lines, module docstrings, copyright headers)
- [ ] Run Mathlib linters locally

### Wave 5 — PivotalCategory PR
**Goal:** First Mathlib PR — fills the gap explicitly listed in Rigid.Basic.

- [ ] Submit PR: PivotalCategory (pivotal = rigid + natural iso Id ≅ double-dual)
- [ ] Include: definition, basic properties, `@[simp]` lemmas, `_assoc` variants
- [ ] Request review via Zulip #PR-reviews
- [ ] Iterate on feedback

### Wave 6 — Follow-up PRs (sequenced)
**Goal:** Build on accepted PivotalCategory with dependent definitions.

- [ ] SphericalCategory (spherical = pivotal + trace condition)
- [ ] CategoricalTrace (trace of endomorphisms via evaluation/coevaluation)
- [ ] RibbonCategory (ribbon = braided + rigid + twist)
- [ ] Sequence via `blocked-by-other-PR` labels

---

## Track C: Paper Submission

**Deep research pending:** `Phase5g_paper_submission_strategy.txt`, `Phase5g_paper14_braided_mtc_scope.txt`

### Wave 7 — Paper 12 (Polariton) to arXiv
**Goal:** Establish experimental priority before LKB Paris measurement.

- [ ] Final theorem count update
- [ ] Human provenance verification via dashboard
- [ ] arXiv formatting (hep-th cross-list cond-mat.quant-gas)
- [ ] Submit

### Wave 8 — Paper 11 (Quantum Group) to arXiv
**Goal:** Establish "first quantum group in proof assistant" priority.

- [ ] Update with Phase 5e braided MTC results
- [ ] Final claims-reviewer pass
- [ ] arXiv formatting (math-ph cross-list cs.LO, quant-ph)
- [ ] Submit

### Wave 9 — Paper 14 (Braided MTCs + Knot Invariants) Draft
**Goal:** New paper on Phase 5e/5f results. Scope from deep research.

- [ ] Determine: single paper or split by audience (math-ph / JAR / quant-ph)
- [ ] Draft paper_draft.tex
- [ ] Claims-reviewer
- [ ] Coordinate timing with Mathlib PR (paper references "infrastructure now in Mathlib")

### Wave 10 — Methodology Paper (Paper 15) Draft
**Goal:** Bridge to consulting/pharma — the pipeline itself as a publication.

- [ ] Scope: 12-stage pipeline, 15 invariants, claims-reviewer, Aristotle, provenance
- [ ] Target: Journal of Automated Reasoning or Computer Physics Communications
- [ ] Connect to regulatory context (FDA SaMD, algorithmovigilance)

---

## Dependencies

```
Track A (Computation):     W1 → W2 → W3 (L=12 production)
Track B (Mathlib):         W4 → W5 → W6 (sequential PRs)
Track C (Papers):          W7,W8 (parallel) → W9,W10 (after deep research)
```

All three tracks are independent and can proceed in parallel.

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | Sparse/matrix-free fermion operator | Phase-5g/Sparse staggered fermion matrix.md | **COMPLETE** |
| 2 | Mathlib PR process + style guide | Phase-5h/Contributing categorical infrastructure to Mathlib4.md | **COMPLETE** |
| 3 | Paper submission strategy | Phase5g_paper_submission_strategy.txt | SUBMITTED |
| 4 | Paper 14 scope (braided MTCs) | Phase5g_paper14_braided_mtc_scope.txt | SUBMITTED |
| 5 | Mathlib PR strategy | Phase5g_mathlib_pr_strategy.txt | SUBMITTED |

---

*Phase 5g roadmap. Created 2026-04-06. Matrix-free CG unlocks L=12+. Mathlib PR starts credibility flywheel. Paper submission ships the work.*
