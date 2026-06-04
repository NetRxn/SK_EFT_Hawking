import SKEFTHawking.QuantumNetwork.SpectralMajorization
import SKEFTHawking.QuantumNetwork.MixedState

/-!
# Toward Fannes–Audenaert entropy continuity (Phase 6AL, Wave 4, items F1b/F2/F3)

This module assembles the Fannes–Audenaert entropy-continuity bound from the Ky Fan / spectral-majorization
layer (`SpectralMajorization.lean`) and the mixed-state trace-norm API (`MixedState.lean`).

Shipped here so far: the **trace-norm ↔ sorted-eigenvalue bridge** `traceNorm_eq_sum_abs_eigenvalues₀`
(`‖A‖₁ = ∑ₖ |λ↓ₖ(A)|`), which is the right-hand side of Mirsky's inequality and the spectral form used by
the entropy assembly. (The Mirsky ℓ¹ majorization step — Lidskii–Wielandt + Karamata/HLP convex-majorization,
both absent from Mathlib — and the classical Fannes–Audenaert inequality remain to be built; see the
Phase 6AL roadmap Wave-4 block for the precise decomposition.)

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Trace norm via the sorted spectrum:** `‖A‖₁ = ∑ₖ |λ↓ₖ(A)|` for Hermitian `A`. This is the
right-hand side of Mirsky's inequality and the spectral form consumed by the entropy continuity assembly. -/
theorem traceNorm_eq_sum_abs_eigenvalues₀ {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    traceNorm A = ∑ k, |hA.eigenvalues₀ k| := by
  rw [traceNorm_hermitian hA]
  exact sum_eigenvalues_eq_sum_eigenvalues₀ hA (fun x => |x|)

end SKEFTHawking.QuantumNetwork
