import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.Basic

/-!
# Entanglement-swapping fidelity composition (Phase 6AA, Wave 3)

The Werner-state entanglement-swap output fidelity in the Bell-diagonal /
fidelity-parameter representation (D3): an explicit real-parameter expression,
closed by `ring`/`nlinarith` — no density matrices.

`F_out(F₁,F₂) = F₁·F₂ + (1−F₁)(1−F₂)/3`
(Briegel–Dür–Cirac–Zoller PRA 59, 169 (1999) §IV; Zang et al. arXiv:2305.14573
Eq. (2); transcribed in the Phase-6AA exact-formulas DR, Thm 1.1.)

Invariants (Phase 6AA): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- Werner entanglement-swap output fidelity for a deterministic Bell-state
measurement followed by Pauli correction. -/
noncomputable def wernerSwapFidelity (F₁ F₂ : ℝ) : ℝ := F₁ * F₂ + (1 - F₁) * (1 - F₂) / 3

/-- Swap fidelity is symmetric in the two input links. -/
theorem wernerSwapFidelity_comm (F₁ F₂ : ℝ) :
    wernerSwapFidelity F₁ F₂ = wernerSwapFidelity F₂ F₁ := by
  unfold wernerSwapFidelity; ring

/-- **Monotone composition (left).** Swap fidelity is non-decreasing in the first
input over the physical Werner range (`F₂ ≥ 1/4`), since
`∂F_out/∂F₁ = (4F₂−1)/3 ≥ 0`. Load-bearing for propagating a per-link fidelity
lower bound through a swap. -/
theorem wernerSwapFidelity_mono_left {F₁ F₁' F₂ : ℝ} (h : F₁ ≤ F₁') (h2 : 1 / 4 ≤ F₂) :
    wernerSwapFidelity F₁ F₂ ≤ wernerSwapFidelity F₁' F₂ := by
  unfold wernerSwapFidelity
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (show (0 : ℝ) ≤ 4 * F₂ - 1 by linarith)]

/-- **Monotone composition (right).** Symmetric counterpart via `wernerSwapFidelity_comm`. -/
theorem wernerSwapFidelity_mono_right {F₁ F₂ F₂' : ℝ} (h : F₂ ≤ F₂') (h1 : 1 / 4 ≤ F₁) :
    wernerSwapFidelity F₁ F₂ ≤ wernerSwapFidelity F₁ F₂' := by
  rw [wernerSwapFidelity_comm F₁ F₂, wernerSwapFidelity_comm F₁ F₂']
  exact wernerSwapFidelity_mono_left h h1

end SKEFTHawking.QuantumNetwork
