import SKEFTHawking.QuantumNetwork.MixedState
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Von Neumann entropy (Phase 6AK, Wave FU-8)

The **von Neumann entropy** `S(ρ) = −tr(ρ log ρ)` of a finite-dimensional state, built *without* a
matrix logarithm: on the Hermitian eigenvalue spectrum it is the eigenvalue sum
`S(ρ) = ∑ᵢ (−λᵢ log λᵢ) = ∑ᵢ negMulLog(λᵢ)` (`Real.negMulLog x = −x log x`). This is the entropic
companion to the negativity/log-negativity ladder (FU-2..FU-7).

Shipped here: the definition, nonnegativity `S(ρ) ≥ 0` (each eigenvalue lies in `[0,1]` for a density
operator), and the maximum-entropy bound `S(ρ) ≤ log(dim)` (concavity of `negMulLog` + Jensen).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Von Neumann entropy** `S(ρ) = ∑ᵢ negMulLog(λᵢ)`, the sum of `−λ log λ` over the eigenvalues of a
Hermitian operator. For a density operator this is `−tr(ρ log ρ)`. -/
noncomputable def vonNeumannEntropy {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, Real.negMulLog (hρ.eigenvalues i)

/-- The eigenvalues of a density operator sum to `1`. -/
theorem sum_eigenvalues_density {ρ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) :
    ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := by
  have h := hρ.1.isHermitian.trace_eq_sum_eigenvalues
  have hsum : ∑ i, (↑(hρ.1.isHermitian.eigenvalues i) : ℂ) = 1 := h.symm.trans hρ.2
  have h2 : ((∑ i, hρ.1.isHermitian.eigenvalues i : ℝ) : ℂ) = 1 := by
    push_cast
    exact hsum
  exact_mod_cast h2

/-- Each eigenvalue of a density operator lies in `[0, 1]`. -/
theorem eigenvalue_mem_Icc {ρ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) (i : ι) :
    hρ.1.isHermitian.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨hρ.1.eigenvalues_nonneg i, ?_⟩
  rw [← sum_eigenvalues_density hρ]
  exact Finset.single_le_sum (fun j _ => hρ.1.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- **Nonnegativity of the von Neumann entropy:** `S(ρ) ≥ 0` for any density operator. -/
theorem vonNeumannEntropy_nonneg {ρ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) :
    0 ≤ vonNeumannEntropy hρ.1.isHermitian := by
  apply Finset.sum_nonneg
  intro i _
  obtain ⟨h0, h1⟩ := eigenvalue_mem_Icc hρ i
  exact Real.negMulLog_nonneg h0 h1

/-- **Maximum-entropy bound:** `S(ρ) ≤ log(dim)` — the von Neumann entropy is maximized (`= log d`) by
the maximally mixed state. Concavity of `negMulLog` + Jensen with uniform weights `1/d`. -/
theorem vonNeumannEntropy_le_log_card [Nonempty ι] {ρ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) :
    vonNeumannEntropy hρ.1.isHermitian ≤ Real.log (Fintype.card ι) := by
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hw : ∑ _i : ι, (n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
    field_simp
  -- Jensen: ∑ (1/n) • negMulLog(λᵢ) ≤ negMulLog(∑ (1/n) • λᵢ)
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _ => (n : ℝ)⁻¹) (p := hρ.1.isHermitian.eigenvalues)
    (fun i _ => by positivity) hw (fun i _ => hρ.1.eigenvalues_nonneg i)
  -- the argument of negMulLog on the RHS is (1/n)·∑ λᵢ = 1/n
  have harg : ∑ i, (n : ℝ)⁻¹ • hρ.1.isHermitian.eigenvalues i = (n : ℝ)⁻¹ := by
    rw [← Finset.smul_sum, sum_eigenvalues_density hρ, smul_eq_mul, mul_one]
  rw [harg] at hjensen
  -- negMulLog (1/n) = (1/n) log n
  have hval : Real.negMulLog ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ * Real.log n := by
    rw [Real.negMulLog, Real.log_inv]; ring
  rw [hval] at hjensen
  -- LHS = (1/n) · S(ρ)
  have hlhs : ∑ i, (n : ℝ)⁻¹ • Real.negMulLog (hρ.1.isHermitian.eigenvalues i)
      = (n : ℝ)⁻¹ * vonNeumannEntropy hρ.1.isHermitian := by
    rw [vonNeumannEntropy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]
  rw [hlhs] at hjensen
  -- (1/n) S ≤ (1/n) log n  ⟹  S ≤ log n
  exact le_of_mul_le_mul_left (by rwa [mul_comm (n:ℝ)⁻¹, mul_comm (n:ℝ)⁻¹] at hjensen) (by positivity)

end SKEFTHawking.QuantumNetwork
