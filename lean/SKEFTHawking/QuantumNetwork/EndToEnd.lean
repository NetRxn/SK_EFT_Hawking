import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.Swapping

/-!
# End-to-end fidelity of a swap chain (Phase 6AA, Wave 4)

The Werner-iterated end-to-end fidelity over a chain of `k` identical Werner links
of per-link fidelity `F`, in the Werner-parameter representation (exact-formulas
DR S5.5):

`F_e2e^(k) = (1 + 3·wᵏ) / 4`,  with the Werner parameter `w = (4F − 1)/3`.

The key structural fact is that an entanglement swap is **multiplicative in the
Werner parameter** (`wernerParam_swap`), so the chain reduces to `w ↦ wᵏ` and the
fidelity has the closed form above. This is the pure-swap (memoryless,
complete-BSM) reference scenario — purely algebraic, no transcendental bounds and
no density-matrix machinery.

Invariants (Phase 6AA): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- Werner parameter `w = (4F − 1)/3` (`∈ [0,1]` for `F ∈ [1/4,1]`). -/
noncomputable def wernerParam (F : ℝ) : ℝ := (4 * F - 1) / 3

/-- The Werner parameter is injective in the fidelity (affine, nonzero slope). -/
theorem wernerParam_injective : Function.Injective wernerParam := by
  intro a b h
  unfold wernerParam at h
  linarith

/-- **Swap is multiplicative in the Werner parameter:** `w(F₁⋈F₂) = w(F₁)·w(F₂)`.
This is the structural heart of the end-to-end closed form. -/
theorem wernerParam_swap (F₁ F₂ : ℝ) :
    wernerParam (wernerSwapFidelity F₁ F₂) = wernerParam F₁ * wernerParam F₂ := by
  unfold wernerParam wernerSwapFidelity; ring

/-- End-to-end fidelity of a chain of `k` identical Werner links of fidelity `F`. -/
noncomputable def endToEndFidelity (F : ℝ) (k : ℕ) : ℝ :=
  (1 + 3 * (wernerParam F) ^ k) / 4

/-- The closed form has Werner parameter `wᵏ`. -/
theorem endToEndFidelity_param (F : ℝ) (k : ℕ) :
    wernerParam (endToEndFidelity F k) = (wernerParam F) ^ k := by
  unfold endToEndFidelity wernerParam; ring

/-- **The closed form satisfies the one-more-link swap recurrence**, validating it
as the iterated entanglement-swap fidelity. -/
theorem endToEndFidelity_succ (F : ℝ) (k : ℕ) :
    endToEndFidelity F (k + 1) = wernerSwapFidelity (endToEndFidelity F k) F := by
  apply wernerParam_injective
  rw [wernerParam_swap, endToEndFidelity_param, endToEndFidelity_param, pow_succ]

end SKEFTHawking.QuantumNetwork
