import SKEFTHawking.QuantumNetwork.HelstromDiscrimination
import SKEFTHawking.QuantumNetwork.CPTPChannel

/-!
# Binary measurement robustness for a memoryless comparison model

Two post-reset density operators close to a common reference cannot have widely
separated binary outcome probabilities after a common normalized Kraus channel.
Observation errors are added separately. This is a bound on the stated comparison
class, not on arbitrary system-environment evolution. The shared channel and effect
are essential: history-dependent choices are not covered. No quantum-only memory
or computational advantage conclusion follows.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Born probability for the first outcome of a binary effect. -/
noncomputable def binaryOutcomeProb (E ρ : Matrix ι ι ℂ) : ℝ :=
  (E * ρ).trace.re

/-- Positivity and completeness of the effect give a normalized probability. -/
theorem binaryOutcomeProb_mem_Icc {E ρ : Matrix ι ι ℂ}
    (hE : IsBinaryPOVM E) (hρ : IsDensityOperator ρ) :
    binaryOutcomeProb E ρ ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 := (Complex.le_def.mp (trace_mul_nonneg hE.1 hρ.1)).1
  have h1 := (Complex.le_def.mp (trace_mul_nonneg hE.2 hρ.1)).1
  simp only [Complex.zero_re] at h0 h1
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    hρ.2, Complex.one_re] at h1
  exact ⟨h0, by unfold binaryOutcomeProb; linarith⟩

/-- The complementary outcome has probability one minus the first outcome. -/
theorem binaryOutcomeProb_complement {E ρ : Matrix ι ι ℂ}
    (hρ : IsDensityOperator ρ) :
    binaryOutcomeProb (1 - E) ρ = 1 - binaryOutcomeProb E ρ := by
  simp [binaryOutcomeProb, Matrix.sub_mul, hρ.2]

/-- A binary measurement cannot separate states more than their trace distance. -/
theorem abs_binaryOutcomeProb_sub_le_traceDist {E ρ σ : Matrix ι ι ℂ}
    (hE : IsBinaryPOVM E) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    |binaryOutcomeProb E ρ - binaryOutcomeProb E σ| ≤ traceDist ρ σ := by
  have h01 := helstrom_le_povmAvgError hρ hσ hE
  have h10 := helstrom_le_povmAvgError hσ hρ hE
  rw [povmAvgError_eq_half_one_sub hρ.2, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re] at h01
  rw [povmAvgError_eq_half_one_sub hσ.2, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re, traceDist_comm σ ρ] at h10
  unfold binaryOutcomeProb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For binary laws `(p,1-p)` and `(q,1-q)`, total variation is `|p-q|`. -/
theorem binary_totalVariation_eq (p q : ℝ) :
    (|p - q| + |(1 - p) - (1 - q)|) / 2 = |p - q| := by
  rw [show (1 - p) - (1 - q) = -(p - q) by ring, abs_neg]
  ring

/-- The common-reference error budgets bound separation after a shared channel
and shared binary effect. The unit cap is intrinsic to probabilities. -/
theorem binary_memoryless_separation_le {ρ₀ ρ₁ τ E : Matrix ι ι ℂ}
    {K : Fin m → Matrix ι ι ℂ} {ε₀ ε₁ : ℝ}
    (hρ₀ : IsDensityOperator ρ₀) (hρ₁ : IsDensityOperator ρ₁)
    (hτ : IsDensityOperator τ) (hK : IsKrausChannel K) (hE : IsBinaryPOVM E)
    (hε₀ : traceDist ρ₀ τ ≤ ε₀) (hε₁ : traceDist ρ₁ τ ≤ ε₁) :
    |binaryOutcomeProb E (krausMap K ρ₀) - binaryOutcomeProb E (krausMap K ρ₁)|
      ≤ min 1 (ε₀ + ε₁) := by
  have hφ₀ := krausMap_isDensityOperator hK hρ₀
  have hφ₁ := krausMap_isDensityOperator hK hρ₁
  have hm := abs_binaryOutcomeProb_sub_le_traceDist hE hφ₀ hφ₁
  have hc := traceDist_krausMap_le hK hρ₀.1.isHermitian hρ₁.1.isHermitian
  have ht := traceDist_triangle ρ₀ τ ρ₁ hρ₀.1.isHermitian hτ.1.isHermitian
    hρ₁.1.isHermitian
  rw [traceDist_comm τ ρ₁] at ht
  exact le_min (hm.trans (traceDist_mem_Icc hφ₀ hφ₁).2) (by linarith)

/-- Observation error budgets concern reported probabilities, separately from
the reset-state budgets. No sampling or numerical certification is assumed here. -/
theorem binary_memoryless_observed_separation_le {ρ₀ ρ₁ τ E : Matrix ι ι ℂ}
    {K : Fin m → Matrix ι ι ℂ} {ε₀ ε₁ δ₀ δ₁ q₀ q₁ : ℝ}
    (hρ₀ : IsDensityOperator ρ₀) (hρ₁ : IsDensityOperator ρ₁)
    (hτ : IsDensityOperator τ) (hK : IsKrausChannel K) (hE : IsBinaryPOVM E)
    (hε₀ : traceDist ρ₀ τ ≤ ε₀) (hε₁ : traceDist ρ₁ τ ≤ ε₁)
    (hq₀ : q₀ ∈ Set.Icc (0 : ℝ) 1) (hq₁ : q₁ ∈ Set.Icc (0 : ℝ) 1)
    (hδ₀ : |q₀ - binaryOutcomeProb E (krausMap K ρ₀)| ≤ δ₀)
    (hδ₁ : |q₁ - binaryOutcomeProb E (krausMap K ρ₁)| ≤ δ₁) :
    |q₀ - q₁| ≤ min 1 (ε₀ + ε₁ + δ₀ + δ₁) := by
  have hm := (binary_memoryless_separation_le hρ₀ hρ₁ hτ hK hE hε₀ hε₁).trans
    (min_le_right 1 (ε₀ + ε₁))
  have ht₀ := abs_sub_le q₀ (binaryOutcomeProb E (krausMap K ρ₀)) q₁
  have ht₁ := abs_sub_le (binaryOutcomeProb E (krausMap K ρ₀))
    (binaryOutcomeProb E (krausMap K ρ₁)) q₁
  rw [abs_sub_comm (binaryOutcomeProb E (krausMap K ρ₁)) q₁] at ht₁
  refine le_min (abs_le.mpr ⟨by linarith [hq₀.1, hq₁.2],
    by linarith [hq₀.2, hq₁.1]⟩) ?_
  linarith

end SKEFTHawking.QuantumNetwork
