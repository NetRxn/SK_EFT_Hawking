import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.Swapping

/-!
# General Bell-diagonal entanglement-swap map (Phase 6AB, Wave 3)

The entanglement-swap output for two *general* Bell-diagonal states (beyond the
Werner special case), in the Pauli-error convention `(a,b,c,d) ↔ (I,Z,X,Y)`. The
four output components are the Klein-4 (`ℤ₂×ℤ₂`) convolution `λ'_k = Σ_{i⊕j=k} λᵢ μⱼ`
(exact-formulas DR S1.2a–d / Davies–Avis–Wehner arXiv:2509.16689 Lemma 3).

Still pure real-parameter algebra (no density matrices). The Werner swap of
Phase 6AA is the special case `b=c=d=(1−a)/3`.

Invariants (Phase 6AB): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- Bell-diagonal swap output, target (`I`-error / `a`) component (S1.2a). -/
def bellDiagSwapA (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) : ℝ := a₁ * a₂ + b₁ * b₂ + c₁ * c₂ + d₁ * d₂
/-- Bell-diagonal swap output, `Z`-error / `b` component (S1.2b). -/
def bellDiagSwapB (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) : ℝ := a₁ * b₂ + b₁ * a₂ + c₁ * d₂ + d₁ * c₂
/-- Bell-diagonal swap output, `X`-error / `c` component (S1.2c). -/
def bellDiagSwapC (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) : ℝ := a₁ * c₂ + c₁ * a₂ + b₁ * d₂ + d₁ * b₂
/-- Bell-diagonal swap output, `Y`-error / `d` component (S1.2d). -/
def bellDiagSwapD (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) : ℝ := a₁ * d₂ + d₁ * a₂ + b₁ * c₂ + c₁ * b₂

/-- **Normalization preserved:** the output components sum to the product of the
input sums (`= 1` for two Bell-diagonal probability vectors) — the map sends states
to states. -/
theorem bellDiagSwap_normalization (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    bellDiagSwapA a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ + bellDiagSwapB a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂
      + bellDiagSwapC a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ + bellDiagSwapD a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂
      = (a₁ + b₁ + c₁ + d₁) * (a₂ + b₂ + c₂ + d₂) := by
  unfold bellDiagSwapA bellDiagSwapB bellDiagSwapC bellDiagSwapD; ring

/-- Each output component is nonnegative for nonnegative inputs (sums of products). -/
theorem bellDiagSwap_nonneg {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ}
    (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ b₁) (h₃ : 0 ≤ c₁) (h₄ : 0 ≤ d₁)
    (h₅ : 0 ≤ a₂) (h₆ : 0 ≤ b₂) (h₇ : 0 ≤ c₂) (h₈ : 0 ≤ d₂) :
    0 ≤ bellDiagSwapA a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ ∧ 0 ≤ bellDiagSwapB a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ ∧
      0 ≤ bellDiagSwapC a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ ∧ 0 ≤ bellDiagSwapD a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ := by
  unfold bellDiagSwapA bellDiagSwapB bellDiagSwapC bellDiagSwapD
  refine ⟨?_, ?_, ?_, ?_⟩ <;> positivity

/-- **General Bell-diagonal swap fidelity envelope.** For two Bell-diagonal input
states (nonneg components summing to 1), the target-fidelity output component lies
in `[0,1]`. -/
theorem bellDiagSwapA_mem {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ}
    (n₁ : a₁ + b₁ + c₁ + d₁ = 1) (n₂ : a₂ + b₂ + c₂ + d₂ = 1)
    (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ b₁) (h₃ : 0 ≤ c₁) (h₄ : 0 ≤ d₁)
    (h₅ : 0 ≤ a₂) (h₆ : 0 ≤ b₂) (h₇ : 0 ≤ c₂) (h₈ : 0 ≤ d₂) :
    0 ≤ bellDiagSwapA a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ ∧ bellDiagSwapA a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ ≤ 1 := by
  obtain ⟨hA, hB, hC, hD⟩ := bellDiagSwap_nonneg h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  have hnorm := bellDiagSwap_normalization a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂
  rw [n₁, n₂, one_mul] at hnorm
  exact ⟨hA, by linarith⟩

/-- The general map specializes to the Werner swap on Werner inputs
(`b=c=d=(1−a)/3`): a structural bridge to Phase 6AA's `wernerSwapFidelity`. -/
theorem bellDiagSwapA_werner (a₁ a₂ : ℝ) :
    bellDiagSwapA a₁ ((1 - a₁) / 3) ((1 - a₁) / 3) ((1 - a₁) / 3)
        a₂ ((1 - a₂) / 3) ((1 - a₂) / 3) ((1 - a₂) / 3)
      = wernerSwapFidelity a₁ a₂ := by
  unfold bellDiagSwapA wernerSwapFidelity; ring

end SKEFTHawking.QuantumNetwork
