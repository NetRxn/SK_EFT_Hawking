import Mathlib
import SKEFTHawking.BlochBundle
import SKEFTHawking.TopologicalBand.FiniteTorus
import SKEFTHawking.TopologicalBand.FHSLatticeGauge
import SKEFTHawking.TopologicalBand.FHSExamples
import SKEFTHawking.TopologicalBand.BlochFrame

/-!
# D11-FHS Q4 (Lane B) — genuine `BlochBundle` spectral dependency + flat-band fixture

Connects the `BlochBundle.lean` two-band `blochPauli` substrate (Phase 6CA W1) to the Lane-A frame
adapter, making the FHS lattice-Chern pipeline genuinely depend on the spectral machinery.

* `blochProj` / `blochProj_idem` — the lower-band spectral projector `P₋ = ½(I − H/‖d‖)`, proved
  **idempotent** directly from `BlochBundle`'s Pauli identity `blochPauli_sq` (`H² = ‖d‖²·I`) with
  `d ≠ 0` (gap from `blochPauli_gap_pos`). A genuine spectral law, exposed rather than a global
  eigenvector (audit §3.2).
* `BlochLowerBandFrame` — an admissible band frame carrying the lower-band **eigenvector law**
  `H(d(k))·u(k) = −‖d(k)‖·u(k)`, tying the sampled states to `blochPauli`.
* `flatFrame` / `blochLatticeChern_flat` — the **negative fixture** (portfolio non-vacuity gate): a
  concrete constant two-band model (`d ≡ (0,0,1)`, `u ≡ e₂`) whose admissibility **and** lower-band
  law are discharged, with `blochLatticeChern = 0`.

Finite/data-level. A **nontrivial** frame-derived Chern value (`C = ±1`) requires the QWZ
transcendental evaluation (`Complex.arg` of `sin/cos` at generic momenta) and stays behind the
separately-gated QWZ spike.
-/

open Complex Real Matrix
open SKEFTHawking.Topological

namespace SKEFTHawking.TopologicalBand

/-! ### Lower-band spectral projector (genuine BlochBundle spectral law) -/

/-- The lower-band spectral projector `P₋(d) = ½(I − H(d)/‖d‖)` of the two-band Bloch Hamiltonian. -/
noncomputable def blochProj (d : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2⁻¹ : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) - ((Real.sqrt (dNormSq d) : ℝ) : ℂ)⁻¹ • blochPauli d)

/-- **Projector idempotency** `P₋² = P₋`, proved from `BlochBundle`'s Pauli identity `blochPauli_sq`
(`H² = ‖d‖²·I`). The genuine spectral law depending on `BlochBundle`. -/
theorem blochProj_idem (d : Fin 3 → ℝ) (hd : d ≠ 0) :
    blochProj d * blochProj d = blochProj d := by
  have hpos : 0 < Real.sqrt (dNormSq d) := blochPauli_gap_pos d hd
  have hsq : ((Real.sqrt (dNormSq d) : ℝ) : ℂ) * ((Real.sqrt (dNormSq d) : ℝ) : ℂ)
      = (dNormSq d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (dNormSq_nonneg d)]
  set s : ℂ := ((Real.sqrt (dNormSq d) : ℝ) : ℂ) with hs_def
  have hne : s ≠ 0 := by rw [hs_def]; exact_mod_cast ne_of_gt hpos
  set H := blochPauli d with hH_def
  have hHH : H * H = (dNormSq d : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := blochPauli_sq d
  have hinv : s⁻¹ * s⁻¹ * (dNormSq d : ℂ) = 1 := by rw [← hsq]; field_simp
  have e : (s⁻¹ • H) * (s⁻¹ • H) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hHH, smul_smul, hinv, one_smul]
  have key : (1 - s⁻¹ • H) * (1 - s⁻¹ • H) = (2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) - s⁻¹ • H) := by
    rw [sub_mul, mul_sub, mul_sub, e]
    simp only [Matrix.one_mul, Matrix.mul_one]
    module
  unfold blochProj
  rw [Matrix.smul_mul, Matrix.mul_smul, key, smul_smul, smul_smul,
    show ((2 : ℂ)⁻¹ * 2⁻¹) * 2 = 2⁻¹ by norm_num]

/-! ### Sampled lower-band frame tied to `blochPauli` -/

/-- An admissible band frame that genuinely **samples the lower band** of a `blochPauli` family: each
state `u(k)` is the `−‖d(k)‖` eigenvector of `H(d(k))`, and the family is gapped (`d(k) ≠ 0`). This
is the honest bridge to `BlochBundle` (a carried spectral law, not a global continuous eigenvector). -/
structure BlochLowerBandFrame (N₁ N₂ : ℕ) extends AdmissibleBandFrame N₁ N₂ 2 where
  dField : Torus N₁ N₂ → (Fin 3 → ℝ)
  gapped : ∀ k, dField k ≠ 0
  lowerBand : ∀ k, (blochPauli (dField k)) *ᵥ state k
    = (-(Real.sqrt (dNormSq (dField k))) : ℂ) • state k

/-- The **flat two-band model**: constant `d ≡ (0,0,1)` (gap `‖d‖ = 1`) with the constant lower-band
eigenvector `u ≡ e₂ = (0,1)`. Admissibility, normalization, and the lower-band eigenvector law are all
discharged concretely against `blochPauli`. -/
noncomputable def flatFrame : BlochLowerBandFrame 2 2 where
  state := fun _ => ![0, 1]
  normalized := by
    intro k
    simp [frameOverlap, Fin.sum_univ_two]
  overlap_ne := by
    intro μ k
    simp [frameOverlap, Fin.sum_univ_two]
  dField := fun _ => ![0, 0, 1]
  gapped := fun k h => by
    have h2 := congrFun h 2
    rw [show (![(0 : ℝ), 0, 1] : Fin 3 → ℝ) 2 = 1 from rfl, Pi.zero_apply] at h2
    exact one_ne_zero h2
  lowerBand := by
    intro k
    have hd1 : dNormSq ![(0 : ℝ), 0, 1] = 1 := by simp [dNormSq]
    show (blochPauli ![0, 0, 1]) *ᵥ ![(0 : ℂ), 1]
      = (-(Real.sqrt (dNormSq ![(0 : ℝ), 0, 1])) : ℂ) • ![(0 : ℂ), 1]
    rw [hd1, Real.sqrt_one]
    funext i
    fin_cases i <;>
      simp [blochPauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Negative fixture (C = 0).** The flat lower-band model has vanishing FHS lattice Chern number:
every overlap is `1`, so every induced link is `1` and `latticeChern = 0`. -/
theorem blochLatticeChern_flat :
    blochLatticeChern flatFrame.toAdmissibleBandFrame = 0 := by
  have h : linkOfFrame flatFrame.toAdmissibleBandFrame = (fun _ _ => (1 : Circle)) := by
    funext μ k
    show phase (frameOverlap (flatFrame.state k) (flatFrame.state (shift 2 2 μ k))) = 1
    have hO : frameOverlap (flatFrame.state k) (flatFrame.state (shift 2 2 μ k)) = 1 := by
      simp [flatFrame, frameOverlap, Fin.sum_univ_two]
    rw [hO]
    unfold phase
    rw [Complex.arg_one, Circle.exp_zero]
  unfold blochLatticeChern
  rw [h]
  exact latticeChern_trivial

end SKEFTHawking.TopologicalBand
