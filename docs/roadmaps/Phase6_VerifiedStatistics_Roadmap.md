# Phase 6: Verified Statistical Analysis Pipeline for Lattice Monte Carlo

## Scoping Roadmap — April 2026

*Prepared 2026-04-03 as Phase 5a Wave 5B | Scopes Phase 6 infrastructure needs*

---

> **This is a SCOPING document, not an execution plan.** It identifies what would be
> needed to formally verify the statistical analysis pipeline for lattice MC results.
> Execution depends on Mathlib probability infrastructure maturation and is at least
> 1-2 years out for Phase 1.

---

## 0. Motivation

Our RHMC production (L=4 complete, L=8 in flight) generates raw Monte Carlo data.
The statistical post-processing that turns this data into physics claims — error bars,
autocorrelation corrections, finite-size scaling fits, phase classifications — is
currently unverified. No proof assistant worldwide has formalized:

- Jackknife or bootstrap variance estimators
- Autocorrelation analysis (Γ-method)
- Chi-squared fitting or hypothesis testing
- Bayesian model comparison

This is the **most tractable verification target** for lattice QFT: it avoids
formalizing the lattice action or HMC algorithm while certifying the inference
that produces publishable numbers.

**Research basis:** `Lit-Search/Phase-5a/Formal verification meets lattice Monte Carlo- a feasibility assessment for SMG.md`

---

## 1. Phase 1: Formalized Resampling Statistics (1-2 years)

### 1A. Jackknife Variance Estimator

**Goal:** Formalize the delete-one jackknife variance estimator in Lean 4.

**Formula:**
  σ²_JK = [(N-1)/N] · Σᵢ [f(x̄₍ᵢ₎) - f(x̄)]²

where x̄₍ᵢ₎ is the mean with the i-th observation deleted.

**Mathlib prerequisites:**
- Finite sums over Finset (exists)
- Real-valued variance (partially exists via MeasureTheory)
- Bias correction factor (N-1)/N (elementary)

**Deliverable:** `lean/SKEFTHawking/VerifiedJackknife.lean`

### 1B. Bootstrap Confidence Intervals

**Goal:** Formalize bootstrap percentile and BCa confidence intervals.

**Mathlib prerequisites:**
- Order statistics / quantiles (partially exists)
- Empirical distribution function (missing)
- Normal approximation (CLT exists in Isabelle, partial in Lean)

### 1C. Γ-Method (Wolff 2004)

**Goal:** Formalize the integrated autocorrelation time estimator with automatic windowing.

**Formula:**
  τ_int = 1/2 + Σ_{t=1}^{W} Γ(t)/Γ(0)

where Γ(t) is the normalized autocorrelation function and W is the automatic
window determined by the condition W ≥ c·τ_int(W).

**Mathlib prerequisites:**
- Autocorrelation function (missing)
- Geometric series bounds (exists)
- Automatic windowing criterion (elementary once τ_int is defined)

**Source:** Wolff, Comput. Phys. Commun. 156, 143 (2004)

### 1D. Chi-Squared Fitting

**Goal:** Formalize χ² goodness-of-fit and p-value computation.

**Mathlib prerequisites:**
- Chi-squared distribution (missing — needs gamma distribution)
- CDF / survival function (partially exists)
- Matrix inversion for covariance (exists in principle via LinearAlgebra)

---

## 2. Phase 2: Verified Krylov Solvers (2-4 years)

### 2A. Conjugate Gradient with Error Bounds

**Goal:** Formally verify a CG solver with floating-point error bounds.

**State of the art:** VeriNum (Princeton/Cornell) has verified Störmer-Verlet
leapfrog and Jacobi iteration. CG has never been formally verified.

**Approach:** Certificate-checking paradigm (Flyspeck). Run unverified CG,
then verify the residual ‖Ax - b‖ < ε formally.

### 2B. Multi-shift CG (for RHMC rational approximation)

**Goal:** Verify the multi-shift CG algorithm used in our RHMC production.
We already have the Lean theorem `multishift_cg_shared_krylov` (HubbardStratonovichRHMC.lean)
proving the shared Krylov space property.

### 2C. Sparse Matrix-Vector Multiplication

**Goal:** Extend LAProof's verified SpMV to lattice Dirac operator structure.

---

## 3. Phase 3: Verified Lattice QFT (4-7 years)

### 3A. Staggered Fermion Dirac Operator

**Goal:** Formalize the staggered fermion Dirac operator in Lean 4.

This requires: lattice as discrete structure, SU(N) link variables, staggered
phases η_μ(x) = (-1)^{x_1+...+x_{μ-1}}, the Dirac matrix D[U], and
anti-Hermiticity γ₅ D γ₅ = -D†.

### 3B. Wilson Gauge Action

**Goal:** Formalize S = β Σ_□ (1 - Re Tr U_□) and its gauge invariance.

Our existing `QuaternionGauge.lean` (10 theorems) and `SO4Weingarten.lean`
(14 theorems) provide building blocks.

### 3C. HMC Trajectory Integration

**Goal:** Verify leapfrog integration for gauge field molecular dynamics.

Extends VeriNum's verified leapfrog to gauge field configuration space.

---

## 4. Infrastructure Dependencies

| Component | Mathlib Status | Needed For |
|-----------|---------------|------------|
| Measure theory | Mature | All phases |
| Probability distributions | Partial (Gaussian, Poisson) | Phase 1 |
| CLT | Missing (exists in Isabelle) | Phase 1B |
| Chi-squared distribution | Missing | Phase 1D |
| Floating-point arithmetic | Missing (Flocq is Coq) | Phase 2 |
| Sparse linear algebra | Partial | Phase 2 |
| SU(N) matrix groups | Missing | Phase 3 |
| Haar measure (compact groups) | Incomplete | Phase 3 |

---

## 5. Effort Estimates

Based on Flyspeck precedent (20 person-years, 3000× verification slowdown):

| Phase | Scope | Estimated LOE | Dependencies |
|-------|-------|--------------|-------------|
| Phase 1 | Formalized statistics | 5-10 person-years | Mathlib probability maturation |
| Phase 2 | Verified Krylov solvers | 5-10 person-years | VeriNum methodology port to Lean |
| Phase 3 | Verified lattice QFT | 10-20 person-years | Phases 1-2 + SU(N) in Mathlib |

**Total:** 20-40 person-years for end-to-end. Phase 1 alone is the high-value target.

---

## 6. Near-Term Actions (from Phase 5a)

1. **Deep research task:** Survey Mathlib probability infrastructure gaps for Phase 1
2. **Deep research task:** Assess VeriNum methodology portability from Coq to Lean 4
3. **Prototype:** Jackknife estimator in Lean 4 (test Mathlib readiness)
4. **Connection:** Our existing `HubbardStratonovichRHMC.lean` (22 theorems) provides
   the RHMC algorithmic skeleton; Phase 2B would verify the numerical implementation.

---

*Phase 6 scoping roadmap. Created 2026-04-03 as Phase 5a Wave 5B.
This is infrastructure planning — execution timeline depends on Mathlib
probability infrastructure maturation (estimated 1-2 years minimum).*
