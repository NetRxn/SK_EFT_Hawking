# Phase 5g: Matrix-Free CG + Mathlib Contribution + Paper Submission

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Follows Phase 5f (TQFT, emergent gravity bounds, figure-eight knot)*

**Entry state:** 2232 theorems (2150 substantive + 82 placeholder), 1 axiom, 94 modules, 33 sorry. Automated counts: `uv run python scripts/update_counts.py` → `docs/counts.json`. Zero heartbeat overrides. L=8 RHMC running (4 workers). Aristotle Batch 2 in flight (Uqsl2AffineHopf + CoidealEmbedding, 7 sorry). Braided MTCs + TQFT + knot invariants complete. Wen coupling deficit formalized. Phases 5h-5j active: GaugingStep, SU3kFusion, FermiPointTopology, PolyQuotQ all zero sorry.

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
3. **Publication:** 14 papers, 2232 theorems, 0 submitted. Ship the work.

---

## Track A: Matrix-Free Staggered Dirac Operator (L=12+ unlock)

**Deep research complete:** `Phase-5g/Sparse staggered fermion matrix.md`
**Key finding:** Matrix-free with `torch.roll()` is the right approach (not explicit sparse). PyTorch sparse is broken on Apple Silicon (MKL dependency). Every production lattice QCD code uses matrix-free.

### Wave 1 — Matrix-Free Operator Implementation — **COMPLETE**
**Goal:** Replace dense A@v with torch.roll()-based stencil.

- [x] Implement `apply_fermion_matrix(v, blocks, L)` using torch.roll + einsum
- [x] Precompute site-dependent 8x8 hopping blocks from h-field and CG bilinears
- [x] Handle antisymmetric backward hop (transpose of block for backward direction)
- [x] Implement `apply_AtA(v, blocks, L)` = -A(A(v)) for CG

**Deliverables:**
- [x] `src/vestigial/stencil_dirac.py` — matrix-free operator (165 lines)
  - `precompute_blocks(h, CG, L)`: h-field → (4, L, L, L, L, 8, 8) hopping matrices
  - `apply_fermion_matrix(v, blocks, L)`: matrix-free A@v via torch.roll
  - `apply_AtA(v, blocks, L)`: A†A = -A² via double application
  - `make_cg_operator(blocks, L)`: callable wrapper for CG solvers
  - `verify_against_dense(h, L)`: cross-validation function
- [x] `tests/test_stencil_dirac.py` — 19 tests, all pass:
  - A@v matches dense to <1e-13 relative error at L=2 and L=4
  - AtA matches dense to <1e-10 at L=4
  - Antisymmetry, PSD, symmetry properties verified
  - CG convergence with matrix-free operator matches dense LU solve
  - Multi-shift CG integration verified (3 shifts, rel error <1e-6)
  - Force computation with stencil_ops matches dense forces
  - Memory scaling: blocks = 42 MB at L=12 vs 220 GB dense (>4000x savings)

### Wave 2 — CG Solver Integration — **COMPLETE**
**Goal:** Drop-in replacement in existing RHMC.

- [x] `batched_cg()` now accepts callable AtA (auto-detects matrix vs function)
- [x] `multi_shift_solve_torch()` supports callable AtA (auto-routes to CG)
- [x] `compute_forces_torch()` accepts `stencil_ops` dict for matrix-free path
- [x] `_solve_asymptotic_shifts()` supports callable AtA
- [x] All 32 existing RHMC tests pass (zero regressions)
- [x] Checkpoint/resume unchanged (blocks rebuilt from h-field at resume)
- [ ] Profile at L=8: matrix-free vs dense time/traj (deferred to next session)

**Deliverables:**
- [x] Modified `src/vestigial/hs_rhmc_torch.py` — backward-compatible matrix-free support
  - Dense path unchanged (all existing callers unaffected)
  - Matrix-free path activated by passing callable to CG or stencil_ops to forces

### Wave 3 — L=12 Production — **BLOCKED** (L=8 workers must free up first)
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

### Wave 4 — Zulip Engagement + Style Adaptation — **NOT STARTED**
**Goal:** Introduce project on Zulip, adapt first PR candidate to Mathlib style.
**Prerequisites:** VecGMonoidal heartbeats: **DONE** (eliminated via @[local instance] caching). Number field consolidation: **BLOCKED** on Phase 5i W4.

- [ ] Join leanprover.zulipchat.com, post in #new-members and #mathlib4
- [ ] Describe the categorical infrastructure scope
- [ ] Adapt PivotalCategory to Mathlib conventions (Struct/Full split, trailing prime, aesop_cat auto-params, 100-char lines, module docstrings, copyright headers)
- [ ] Run Mathlib linters locally

### Wave 5 — PivotalCategory PR — **BLOCKED** (on W4 + number field consolidation)
**Goal:** First Mathlib PR — fills the gap explicitly listed in Rigid.Basic.

**Prerequisites (must complete before submission):**
- VecGMonoidal heartbeat elimination: **DONE** (eliminated via @[local instance] caching)
- Number field consolidation (generic CyclotomicField, not 6 hand-written types) — **Phase 5i Wave 4** — **NOT STARTED**

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

**Deep research complete:** `Lit-Search/Phase-5g/Publishing the first verified braided MTCs and knot invariants.md` (paper strategy), `Lit-Search/Phase-5g/CopyPublishA publication blueprint for an independent researcher across physics and formal verification.md` (publication blueprint)

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
| 1 | Sparse/matrix-free fermion operator | Lit-Search/Phase-5g/Sparse staggered fermion matrix.md | **COMPLETE**, applied (matrix-free CG) |
| 2 | Mathlib PR process + style guide | Lit-Search/Phase-5h/Contributing categorical infrastructure to Mathlib4.md | **COMPLETE** (Mathlib PR guide) |
| 3 | Ising MTC F-symbols + pentagon | Lit-Search/Phase-5g/Ising MTC F-symbols and pentagon equation for Lean 4.md | **COMPLETE**, applied (pentagon fix) |
| 4 | VecGMonoidal heartbeat fix | Lit-Search/Phase-5g/Replacing inferInstance with explicit monoidal constructions for GradedObject.md | **COMPLETE**, applied (VecGMonoidal fix) |
| 5 | Paper strategy (braided MTCs) | Lit-Search/Phase-5g/Publishing the first verified braided MTCs and knot invariants.md | **COMPLETE** (paper strategy) |
| 6 | Publication blueprint | Lit-Search/Phase-5g/CopyPublishA publication blueprint for an independent researcher across physics and formal verification.md | **COMPLETE** (publication blueprint) |

---

*Phase 5g roadmap. Created 2026-04-06. Updated 2026-04-06 (Track A W1-2 COMPLETE, W3 BLOCKED on L=8 workers. Track B W4 NOT STARTED — VecGMonoidal heartbeats DONE, number field consolidation BLOCKED on 5i W4. Note: Track B blocker reassessed — Mathlib PR not blocked by number fields, categorical infrastructure is independent. Track C not started, deep research COMPLETE. Ising pentagon PROVED via native_decide/QSqrt2. Fibonacci pentagon PROVED via native_decide/QSqrt5. Automated counts operational: update_counts.py + counts.json). 2232 theorems, 94 modules, 33 sorry, 1 axiom.*
