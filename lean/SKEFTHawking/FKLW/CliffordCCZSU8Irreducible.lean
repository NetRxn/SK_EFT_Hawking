/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4g — Clifford-adjoint irreducibility on 𝔰𝔲(8)

The capstone of Phase 6z Wave 4: the Clifford-adjoint action on `𝔰𝔲(8)` is **irreducible**. Concretely,
any ℝ-submodule `W` of `8×8` matrices that is closed under conjugation by the nine literal Clifford
generators and contains a *single* nonzero traceless skew-Hermitian element contains **all** of `𝔰𝔲(8)`.

The two-step argument assembles the Wave-4 substrate:

  1. **Extract a line** (`twirl_extract`): a nonzero traceless skew-Hermitian `Y ∈ W` has a nonzero
     tensor-Pauli coordinate `repr Y v₀ ≠ 0` (with `v₀ ≠ 0` by tracelessness). The partial Pauli twirl
     `pauli_twirl` projects `Y` onto the line `ℝ·kronK8 v₀`; the twirl sum lies in `W` because each
     summand `kronK8 w · Y · kronK8 w ∈ W` (`conj_kronK8_closed`) and the `±1` weights are absorbed by
     `W`. The coordinate is purely imaginary (`repr8_re_zero`, `Y` skew-Hermitian), so dividing by the
     real factor yields `i·kronK8 v₀ ∈ W`.

  2. **Spread to all lines** (`all_lines_conj`) + **span** (`suEightTangent_spans`): Clifford transport
     carries the one line to every tensor-Pauli line `i·kronK8 v` (`v ≠ 0`), and the 63 lines span
     `𝔰𝔲(8)`, so every traceless skew-Hermitian matrix lies in `W`.

The payoff `clifford_irreducible_spans` is exactly the `hX_spans` engine for the Phase 6z
`ClosureDenseWitness`: the Clifford orbit of the (non-explicit Bolzano-Weierstrass) seed tangent `X₀`
spans `𝔰𝔲(8)` because its ℝ-span is a nonzero Clifford-invariant submodule.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4g (Clifford-adjoint irreducibility on 𝔰𝔲(8)). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8KronK8Closure
import SKEFTHawking.FKLW.CliffordCCZSU8PauliTwirl
import SKEFTHawking.FKLW.CliffordCCZSU8Transport

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.TrappedIonSU4 SKEFTHawking.FKLW.GenericSU2
  SKEFTHawking.FKLW.CliffordCCZ

/-! ## 1. The conjugation signs are `±1` -/

/-- The single-qubit symplectic sign is `±1`. -/
theorem sigmaSign_pm (a b : Fin 4) : sigmaSign a b = 1 ∨ sigmaSign a b = -1 := by
  unfold sigmaSign; split_ifs <;> simp

/-- The 3-qubit total symplectic sign is `±1`. -/
theorem sigmaSign8_pm (w v : PauliLabel) : sigmaSign8 w v = 1 ∨ sigmaSign8 w v = -1 := by
  unfold sigmaSign8
  rcases sigmaSign_pm w.1 v.1 with h1 | h1 <;> rcases sigmaSign_pm w.2.1 v.2.1 with h2 | h2 <;>
    rcases sigmaSign_pm w.2.2 v.2.2 with h3 | h3 <;> simp [h1, h2, h3]

/-! ## 2. The twirl extraction: a nonzero invariant element yields one tensor-Pauli line -/

/-- **Twirl extraction.** A nonzero traceless skew-Hermitian `Y` in a submodule `W` closed under
conjugation by the six per-qubit `H`/`S` generators yields a nonzero tensor-Pauli line in `W`:
`∃ v₀ ≠ 0, i·kronK8 v₀ ∈ W`. -/
theorem twirl_extract (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH1 : ∀ Y ∈ W, (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH2 : ∀ Y ∈ W, (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH3 : ∀ Y ∈ W, (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS1 : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS2 : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS3 : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (Y : Matrix (Fin 8) (Fin 8) ℂ) (hY : Y ∈ W) (hne : Y ≠ 0)
    (hskew : Y.IsSkewHermitian) (htr : Y.trace = 0) :
    ∃ v0 : PauliLabel, v0 ≠ 0 ∧ Complex.I • kronK8 v0 ∈ W := by
  have hex : ∃ v0, kronK8Basis.repr Y v0 ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hne (by rw [← kronK8Basis_sum_repr Y]; simp only [h, zero_smul, Finset.sum_const_zero])
  obtain ⟨v0, hv0⟩ := hex
  have hv0ne : v0 ≠ 0 := by rintro rfl; exact hv0 (repr8_zero_zero_zero Y htr)
  have hsum_mem : (∑ w : PauliLabel, sigmaSign8 w v0 • (kronK8 w * Y * kronK8 w)) ∈ W := by
    apply Submodule.sum_mem
    intro w _
    have hm := conj_kronK8_closed W hH1 hH2 hH3 hS1 hS2 hS3 w Y hY
    rcases sigmaSign8_pm w v0 with h | h
    · rw [h, one_smul]; exact hm
    · rw [h, neg_one_smul]; exact W.neg_mem hm
  rw [pauli_twirl] at hsum_mem
  set z := kronK8Basis.repr Y v0 with hz
  have hre : z.re = 0 := repr8_re_zero Y hskew v0
  have him : z.im ≠ 0 := by
    intro h0; apply hv0; rw [hz, Complex.ext_iff]; exact ⟨by simpa using hre, by simpa using h0⟩
  have hcz : (64 : ℂ) * z = ((64 * z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [hcz, ← smul_smul, Complex.coe_smul] at hsum_mem
  refine ⟨v0, hv0ne, ?_⟩
  have hmem := W.smul_mem (64 * z.im)⁻¹ hsum_mem
  rwa [inv_smul_smul₀ (mul_ne_zero (by norm_num) him)] at hmem

/-! ## 3. Irreducibility: one nonzero element generates all tensor-Pauli lines, then all of 𝔰𝔲(8) -/

/-- **All tensor-Pauli lines.** A submodule `W` closed under conjugation by the nine Clifford generators
that contains a nonzero traceless skew-Hermitian element contains every tensor-Pauli line
`i·kronK8 v` (`v ≠ 0`). -/
theorem clifford_irreducible (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH1 : ∀ Y ∈ W, (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH2 : ∀ Y ∈ W, (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH3 : ∀ Y ∈ W, (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS1 : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS2 : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS3 : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hC12 : ∀ Y ∈ W, CNOT_12_mat * Y * CNOT_12_mat⁻¹ ∈ W)
    (hC13 : ∀ Y ∈ W, CNOT_13_mat * Y * CNOT_13_mat⁻¹ ∈ W)
    (hC23 : ∀ Y ∈ W, CNOT_23_mat * Y * CNOT_23_mat⁻¹ ∈ W)
    (Y : Matrix (Fin 8) (Fin 8) ℂ) (hY : Y ∈ W) (hne : Y ≠ 0)
    (hskew : Y.IsSkewHermitian) (htr : Y.trace = 0) :
    ∀ v : PauliLabel, v ≠ 0 → Complex.I • kronK8 v ∈ W := by
  obtain ⟨v0, hv0ne, hv0mem⟩ := twirl_extract W hH1 hH2 hH3 hS1 hS2 hS3 Y hY hne hskew htr
  exact all_lines_conj W hH1 hH2 hH3 hS1 hS2 hS3 hC12 hC13 hC23 hv0ne hv0mem

/-- **Clifford-adjoint irreducibility (spanning form, `hX_spans` engine).** A submodule `W` closed under
conjugation by the nine Clifford generators that contains a nonzero traceless skew-Hermitian element
contains **all** of `𝔰𝔲(8)`: every traceless skew-Hermitian matrix lies in `W`. -/
theorem clifford_irreducible_spans (W : Submodule ℝ (Matrix (Fin 8) (Fin 8) ℂ))
    (hH1 : ∀ Y ∈ W, (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH2 : ∀ Y ∈ W, (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hH3 : ∀ Y ∈ W, (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed H_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS1 : ∀ Y ∈ W, (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit1Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS2 : ∀ Y ∈ W, (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit2Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hS3 : ∀ Y ∈ W, (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) * Y *
      ((qubit3Embed S_SU : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈ W)
    (hC12 : ∀ Y ∈ W, CNOT_12_mat * Y * CNOT_12_mat⁻¹ ∈ W)
    (hC13 : ∀ Y ∈ W, CNOT_13_mat * Y * CNOT_13_mat⁻¹ ∈ W)
    (hC23 : ∀ Y ∈ W, CNOT_23_mat * Y * CNOT_23_mat⁻¹ ∈ W)
    (Y : Matrix (Fin 8) (Fin 8) ℂ) (hY : Y ∈ W) (hne : Y ≠ 0)
    (hskew : Y.IsSkewHermitian) (htr : Y.trace = 0) :
    ∀ Y' : Matrix (Fin 8) (Fin 8) ℂ, Y'.IsSkewHermitian → Y'.trace = 0 → Y' ∈ W := by
  have hline := clifford_irreducible W hH1 hH2 hH3 hS1 hS2 hS3 hC12 hC13 hC23 Y hY hne hskew htr
  intro Y' hskew' htr'
  obtain ⟨c, hc⟩ := suEightTangent_spans Y' hskew' htr'
  rw [hc]
  apply Submodule.sum_mem
  intro j _
  have htan : suEightTangent j ∈ W := by
    have hmem := W.smul_mem ((2 : ℝ)⁻¹) (hline (idx63 j) (idx63_ne_zero_triple j))
    rw [← Complex.coe_smul, smul_smul,
      show (((2 : ℝ)⁻¹ : ℝ) : ℂ) * Complex.I = Complex.I / 2 from by push_cast; ring] at hmem
    exact hmem
  exact W.smul_mem _ htan

end SKEFTHawking.FKLW.CliffordCCZSU8
