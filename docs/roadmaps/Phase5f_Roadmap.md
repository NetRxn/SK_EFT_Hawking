# Phase 5f: TQFT Bridge + Emergent Gravity Physics

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Follows Phase 5e (braided MTCs, knot invariants, S-matrix verification)*

**Entry state:** 1327 theorems, 93 modules, 34 sorry (Aristotle).
**Current state:** 1363 theorems, 96 modules, 36 sorry. Waves 1-4 + 7-8 COMPLETE.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research results as they arrive (see §Deep Research below)
> 4. Read Aristotle reference: `docs/references/Theorm_Proving_Aristotle_Lean.md`

---

## 0. Motivation

Phase 5e completed the **categorical** story: fusion → braiding → ribbon → knot invariants. Phase 5f addresses two gaps:

1. **The TQFT gap**: We have verified MTCs but haven't connected them to topological quantum field theory axioms. The Atiyah-Segal axioms formalize what it means for an MTC to define a consistent quantum field theory on manifolds. This completes the mathematical chain: lattice → quantum group → MTC → TQFT.

2. **The physics gap**: The gap equation (5d) showed emergent gravity works at mean-field level, but the disproved boundedness theorem and the untested Wen coupling mean we need deeper physics. Two-loop corrections extend the reliability range. The Wen-ADW coupling matching is the make-or-break question for the entire emergent gravity program.

3. **The computation gap**: L=8 MC data is accumulating. We have verified statistics (5d W11) ready to analyze it, but need the data pipeline connected and the Binder analysis completed.

---

## Track A: TQFT Axioms and Modular Functor

**Why:** Completes the mathematical chain MTC → TQFT. First TQFT axiom formalization in any proof assistant.

### Waves 1-2 — TQFT Partition Functions — **COMPLETE**
**Goal:** Verify genus-g partition functions from MTC data + define TQFT axiom structure.

- [x] `lean/SKEFTHawking/TQFTPartition.lean` — 16 theorems, 0 sorry
- [x] Ising partition functions g=0..4: 1, 3, 10, 36, 136 — ALL PROVED
- [x] Fibonacci partition functions g=0..5: 1, 2, 5, 15, 50, 175 — ALL PROVED
- [x] Ising recurrence a_g = 6a_{g-1} - 8a_{g-2}: PROVED
- [x] α+β=5, αβ=5 over Q(√5): PROVED (companion matrix eigenvalues)
- [x] TQFTData typeclass: rank + partition + sphere/torus axioms
- [x] isingTQFT, fibTQFT instances constructed
- **First TQFT partition functions in any proof assistant**

**Deep research:** `Phase-5f/TQFT axioms in Lean 4.md` + `Phase-5f/Genus-g partition functions.md` (COMPLETE)

---

## Track B: Wen-ADW Coupling Chain (Physics)

**Why:** The central question of the emergent gravity program. Does the effective coupling from Wen's string-net condensation reach the ADW critical coupling G_c?

### Wave 3 — Wen Effective Coupling — **DEEP RESEARCH COMPLETE (negative result)**
**Finding:** G_Wen ≈ 0.0006 vs G_c ≈ 4.0 — **~6,000x too weak perturbatively.**

- [x] Deep research: perturbative 4-fermion coupling from box diagram
- [x] Gauged NJL critical line: only ~10% reduction in G_c
- [x] **Key discovery:** Abelian instantons in monopole backgrounds generate unsuppressed 8-fermion ADW vertices for N_f=4 (Csáki et al. 2024)
- [x] **True showstopper:** spin-connection gap (U(1) → SO(3,1) has no known path)
- [x] Volovik vestigial gravity (metric without tetrad) as potential bypass
- [ ] Formalize the coupling deficit as a Lean theorem (G₄f < G_c by factor ~6000)
- [ ] Document instanton mechanism in Paper 5 discussion

**Impact:** Changes the research program — perturbative Wen→ADW path is closed. Instanton and vestigial gravity paths remain open. Paper 5 needs updated discussion.

### Wave 4 — Two-Loop Gap Equation — **DEEP RESEARCH COMPLETE (G_c unchanged at NLO)**
**Finding:** G_c is formally unchanged at strict NLO in 1/N_f expansion (α₁ = 0).

- [x] Deep research: two-loop = one-meson-loop correction (NLO in 1/N_f)
- [x] Strict perturbative 1/N_f: gap equation NOT modified → G_c unchanged
- [x] Self-consistent CJT: G_c shifts by ~20-30%, sign scheme-dependent
- [x] Unboundedness of Δ*(G) is genuine (not cured by two loops)
- [x] ADW tetrad channel advantage: all Goldstone modes eaten (no pion loops)
- [ ] Lean: formalize G_c invariance at NLO as a theorem
- [ ] Update Paper 5 discussion with two-loop analysis

**Impact:** The one-loop formalization is MORE robust than expected. G_c = 8π²/(N_f·Λ²) holds at NLO. The disproved boundedness is a genuine UV sensitivity, not a perturbative artifact.

---

## Track C: MC Data Analysis Pipeline

**Why:** L=8 RHMC is running. When it completes, verified statistics are ready but need to be applied.

### Wave 5 — L=8 Data Analysis
**Prerequisite:** L=8 RHMC completion.
**Status:** Session 3 production running (April 7, 2026). Previous sessions identified and fixed acceptance issues.

- [x] Preliminary 4-panel diagnostic: `fig_rhmc_l8_preliminary` (acceptance, m², h², |ΔH|)
- [ ] Full analysis with verified_analysis.py after 500 traj complete
- [ ] Binder cumulant U₄ vs coupling
- [ ] Autocorrelation analysis → effective sample sizes
- [ ] Phase transition identification (if present)
- [ ] Comparison to mean-field G_c prediction

**Production history:**
- Session 1 (April 5): n_md_steps=30 → |ΔH|>1, acceptance <40%. Data unreliable.
- Session 2 (April 6): n_md_steps=80, g=0.5-8.0, 4 workers. Acceptance at low g still poor (0-20% for g<2), marginal 30-60% for critical region g=3-5, good 60-100% for g>6. Data: 22-305 traj per coupling. |ΔH| averaging 2-4 at low g.
- **Session 3 (April 7, running):** n_md_steps=160 (doubled), g-critical-min=2.0, g-critical-max=6.0. This should halve |ΔH| → acceptance >60% across critical region. Resumes from Session 2 checkpoints (no re-thermalization). PID 46164.

**Key finding:** L=8 acceptance requires n_md_steps scaling with coupling — low g has stiffer fermion matrix → needs smaller MD step size. n_md_steps=160 targets >60% acceptance across g=2-6.

See `docs/references/production_rhmc.md` for the complete guide.

### Wave 6 — L=6 Production + Finite-Size Scaling
**Prerequisite:** Free cores after L=8 completes.

- [ ] L=6 production via `run_rhmc_epochs.sh --l 8 --n-md-steps 40`
- [ ] Binder crossing analysis: L=4 vs L=6 vs L=8
- [ ] Finite-size scaling if transition identified
- [ ] Update Papers 5, 6 with MC results

**Deliverables:**
- `docs/references/production_rhmc.md` — [x] COMPLETE (full RHMC production guide)
- `scripts/run_rhmc_epochs.sh` — [x] COMPLETE (epoch wrapper with thermal recovery)
- MC data analysis notebooks (Phase5f_MC_Technical/Stakeholder) — pending data
- Updated Paper 6 (vestigial) with L=4/6/8 results — pending data
- `fig_rhmc_l8_preliminary` — [x] COMPLETE (4-panel diagnostic)

---

## Track D: Braid Group Infrastructure (Optional)

**Why:** Enables full RT invariant for 3+ strand braids. Extends knot program beyond 2-strand torus knots.

### Waves 7-8 — Figure-Eight Knot from Ising — **COMPLETE**
**Goal:** First 3-strand knot invariant from verified MTC data.

- [x] `lean/SKEFTHawking/FigureEightKnot.lean` — 6 theorems, 0 sorry
- [x] Mat2 type over QCyc16 with matrix multiplication and trace
- [x] F² = I (Hadamard self-inverse) PROVED
- [x] σ₁·σ₁⁻¹ = I, σ₂·σ₂⁻¹ = I (inverse checks) PROVED
- [x] **Figure-eight trace = -1: PROVED** (first 3-strand knot invariant from MTC)
- [x] Normalized RT(4₁, σ) = -1/√2: PROVED
- BraidGroup as PresentedGroup deferred (concrete matrix computation suffices)

**Deep research:** `Phase-5f/Braid groups and RT invariants in Lean 4.md` (COMPLETE)

---

## Dependencies

```
Track A (TQFT):        W1 (axioms) → W2 (Ising TQFT)
Track B (Physics):     W3 (deep research) → W4 (two-loop)
Track C (MC):          [L=8 complete] → W5 (analysis) → W6 (L=6 + FSS)
Track D (Braid):       W7 (BraidGroup) → W8 (figure-eight)
```

Tracks A, B, D are independent and unblocked (A/D need deep research, B needs deep research).
Track C blocked on L=8 RHMC completion.

---

## Deep Research Tasks

| # | Topic | Blocking | File |
|---|-------|----------|------|
| 1 | TQFT axioms in Lean 4: Atiyah-Segal, Mathlib cobordism/functor API | W1 | Phase5f_tqft_axioms_lean4.txt |
| 2 | Wen rotor model → effective 4-fermion coupling in lattice units | W3 | Phase5f_wen_effective_coupling.txt |
| 3 | Two-loop NJL effective potential for tetrad condensation | W4 | Phase5f_two_loop_gap_equation.txt |
| 4 | Braid group via PresentedGroup + RT representation in Lean 4 | W7 | Phase5f_braid_group_lean4.txt |
| 5 | Genus-g partition functions from MTC data (Verlinde formula) | W2 | Phase5f_tqft_partition_functions.txt |

---

## Phase-Level Deliverables

### Lean Modules (planned)
| Module | Track | Theorems (est.) |
|--------|-------|-----------------|
| TQFTAxioms.lean | A-W1 | 10-15 |
| IsingTQFT.lean | A-W2 | 8-12 |
| TetradGapEquation2Loop.lean | B-W4 | 10-15 |
| BraidGroup.lean | D-W7 | 8-12 |
| FigureEightKnot.lean | D-W8 | 5-10 |

### Python
- `tqft_partition_function(k, genus)` — genus-g partition function
- `tetrad_gap_two_loop_correction()` — two-loop gap correction
- `figure_eight_jones()` — figure-eight knot invariant
- MC analysis scripts in verified_analysis.py (already exists)

### Papers
- Paper 5 update: two-loop gap equation + MC results
- Paper 6 update: L=4/6/8 MC data + Binder crossing
- Paper 11 update: TQFT axiom connection
- Paper 14 (potential): "From MTC to TQFT: First Verified Topological Quantum Field Theory"

### Notebooks
- Phase5f_TQFT_Technical/Stakeholder
- Phase5f_MC_Technical/Stakeholder
- Phase5f_TwoLoop_Technical/Stakeholder (if W4 completes)

### Stakeholder Docs
- Phase5f_Implications.md
- Phase5f_Strategic_Positioning.md

---

## Priority Assessment

| Track | Impact | Tractability | Priority |
|-------|--------|-------------|----------|
| A (TQFT) | HIGH — completes math chain | MEDIUM — needs categorical plumbing | **1** |
| B (Physics) | HIGHEST — central research question | MEDIUM — needs deep research first | **1** |
| C (MC) | HIGH — testable predictions | BLOCKED — waiting on data | **2** (when unblocked) |
| D (Braid) | MODERATE — extends knot program | MEDIUM — PresentedGroup exists | **3** |

Tracks A and B are co-primary. A advances the formalization; B advances the physics. Both need deep research to start.

---

*Phase 5f roadmap. Created 2026-04-06. Five deep research tasks to be submitted. All tracks follow WAVE_EXECUTION_PIPELINE.md.*
