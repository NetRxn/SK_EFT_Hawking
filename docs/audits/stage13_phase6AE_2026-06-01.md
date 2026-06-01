# Stage-13 Adversarial Review — Phase 6AE (General mixed-state / channel layer)

**Date:** 2026-06-01
**Reviewer:** fresh-context adversarial agent (read-only; independently re-ran builds, axiom checks, the bridge math, Mathlib-absence greps, leak greps, LaTeX convergence).
**Scope:** `QuantumNetwork/{MixedState, DiamondNorm}.lean`; D6 §6 "Phase 6AE" paragraph; preprint §3d; `Phase6AE_Roadmap.md`.

## Verdict: GREEN — PASS (DONE via the documented-deferred-frontier clause)

| Check | Result |
|---|---|
| 1. Builds + kernel-pure + no sorry/axiom (16 theorems' axioms ⊆ `{propext, Classical.choice, Quot.sound}`; `sorry`/`native_decide`/`maxHeartbeats`/`axiom` appear only as docstring prose, never code) | PASS |
| 2. **Bridge genuinely proven** (`traceNorm A := ∑√eig(AᴴA)` real Schatten-1; `traceNorm_posSemidef : PosSemidef A → ‖A‖₁ = A.trace.re` via `trace_cfc` + `isHermitian_mul_self_eq_cfc_sq` + `map_eigenvalues_conjTranspose_mul_self` (charpoly/root-multiset) + `Real.sqrt_sq`, no sorry in the chain; `traceNorm_density_eq_one` follows; `partialTrace`/`trace_partialTrace`/`choiMatrix` correct) | PASS |
| 3. **Deferred frontier honest / no overclaim** (Mathlib grep at pin: 0 hits for Schatten / Ky Fan / polar decomposition / von-Neumann-trace-inequality — blocker accurate; triangle, traceDist≤1, fidelity/FvdG, contractivity, diamond-norm sup+axioms all clearly marked DEFERRED; `diamondNorm` NOT falsely claimed defined-with-properties) | PASS |
| 4. Stage-9 + counts (both modules root-imported; **770 mod / 10076 thm / 0 axiom / 0 sorry**) | PASS |
| 5. Leak discipline (no private-repo identifier; no product-framing terms) | PASS |
| 6. Packaging compiles + consistent (D6 latexmk converges, zero undefined refs/citations; D6 §6 + preprint §3d accurately split proven-vs-deferred, no overclaim) | PASS |

## What is PROVEN (kernel-pure)
- 6AE-A: `traceNorm`/`traceDist` + structural properties (nonneg, negation-invariance, symmetry, vanishing); `trace_cfc`; `isHermitian_mul_self_eq_cfc_sq`; `map_eigenvalues_conjTranspose_mul_self`; **`traceNorm_posSemidef`** (the PSD→trace bridge — the linchpin); `traceNorm_density_eq_one`.
- 6AE-B: `partialTrace` + `partialTrace_add` + `trace_partialTrace` + `partialTrace_zero`; `choiMatrix` + `choiMatrix_zero`.

## Deferred research frontier (documented, NOT sorried/axiomatized; precise blocker)
Trace-norm triangle inequality (step 3), `traceDist ∈ [0,1]` upper bound (step 2 remainder), Uhlmann fidelity + Fuchs–van de Graaf (step 4), CPTP trace-distance contractivity (step 5), and the diamond-norm sup definition + norm axioms / submultiplicativity / Choi characterization (step 6). **Blocker:** Mathlib at pin v4.29.1/`5e932f97` provides no von Neumann trace inequality, Ky Fan inequality, matrix polar decomposition, or Schatten norm (grep-verified absent) — building these from scratch is a multi-week formalization beyond this phase's budget. Documented in `DiamondNorm.lean` + `Phase6AE_Roadmap.md`.

Phase 6AE is complete per its DONE criterion: the linchpin trace-norm→trace bridge proven kernel-pure, the channel-state-duality substrate (partial trace + Choi) built, and the analytic core left as an honestly-documented research frontier with a precise, grep-verified blocker.
