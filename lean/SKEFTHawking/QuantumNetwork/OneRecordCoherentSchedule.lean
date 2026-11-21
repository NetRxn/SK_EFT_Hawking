import SKEFTHawking.QuantumNetwork.FiniteInstrument

/-!
# One-record coherent timing control

This finite gate sequence compares an offset X rotation placed before or after
one system-to-memory copy. The antisymmetric schedule selection keeps the
amplitude difference. In the dephased control, the same selection mixes the
two branch densities. The exact memory X outcome probabilities are measured
with the finite Kraus instrument.

The timing order and memory observable follow Seidel et al.,
arXiv:2611.26371v1, equations (36)–(41) and Appendix C.
-/

namespace SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule

open scoped BigOperators

abbrev Amplitude := Fin 4 → ℂ

private def xSystem : Fin 4 → Fin 4 := ![2, 3, 0, 1]

private def xMemory : Fin 4 → Fin 4 := ![1, 0, 3, 2]

private def copyIndex : Fin 4 → Fin 4 := ![0, 1, 3, 2]

private def initial : Amplitude := ![1, 0, 0, 0]

/-- Coefficients are the real cosine and sine of the half angle when normalized. -/
private def rotate (a b : ℝ) (ψ : Amplitude) : Amplitude := fun i =>
  (a : ℂ) * ψ i - Complex.I * (b : ℂ) * ψ (xSystem i)

private def early (a b c d : ℝ) : Amplitude := fun i =>
  rotate a b (rotate c d initial) (copyIndex i)

private def late (a b c d : ℝ) : Amplitude :=
  rotate c d (fun i => rotate a b initial (copyIndex i))

private noncomputable def minus (a b c d : ℝ) : Amplitude := fun i =>
  (late a b c d i - early a b c d i) / 2

private def moment (p : Fin 4 → Fin 4) (ψ : Amplitude) : ℝ :=
  ∑ i : Fin 4, (star (ψ i) * ψ (p i)).re

private theorem minus_mass_raw (a b c d : ℝ) :
    moment id (minus a b c d) = d^2 * (a^2 + b^2) / 2 := by
  simp [moment, minus, early, late, rotate, xSystem, copyIndex, initial,
    Fin.sum_univ_succ, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem minus_parity_raw (a b c d : ℝ) :
    moment xMemory (minus a b c d) = -(d^2 * (a^2 + b^2) / 2) := by
  simp [moment, minus, early, late, rotate, xSystem, xMemory, copyIndex, initial,
    Fin.sum_univ_succ, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem early_parity (a b c d : ℝ) :
    moment xMemory (early a b c d) = 0 := by
  simp [moment, early, rotate, xSystem, xMemory, copyIndex, initial,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]

private theorem late_parity (a b c d : ℝ) :
    moment xMemory (late a b c d) = 0 := by
  simp [moment, late, rotate, xSystem, xMemory, copyIndex, initial,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- The coherent minus outcome has positive mass and exact conditional parity. -/
private theorem one_record_parity_contrast (a b c d : ℝ) (h : a^2 + b^2 = 1) (hd : d ≠ 0) :
    0 < moment id (minus a b c d) ∧
    moment id (minus a b c d) = d^2 / 2 ∧
    moment xMemory (minus a b c d) / moment id (minus a b c d) = -1 := by
  rw [minus_mass_raw, minus_parity_raw, h, mul_one]
  have hmass : 0 < d^2 / 2 := div_pos (sq_pos_of_ne_zero hd) (by norm_num)
  refine ⟨hmass, rfl, ?_⟩
  rw [neg_div, div_self hmass.ne']

private theorem early_mass (a b c d : ℝ) :
    moment id (early a b c d) = (a^2 + b^2) * (c^2 + d^2) := by
  simp [moment, early, rotate, xSystem, copyIndex, initial, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

private theorem late_mass (a b c d : ℝ) :
    moment id (late a b c d) = (a^2 + b^2) * (c^2 + d^2) := by
  simp [moment, late, rotate, xSystem, copyIndex, initial, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

open Matrix
open scoped ComplexOrder

private def density (ψ : Amplitude) : Matrix (Fin 4) (Fin 4) ℂ :=
  vecMulVec ψ (star ψ)

private def observable (p : Fin 4 → Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if p i = j then 1 else 0

/-- The memory Pauli X on the system-memory basis. -/
def memoryX : Matrix (Fin 4) (Fin 4) ℂ := observable xMemory

private theorem density_trace (ψ : Amplitude) : (density ψ).trace.re = moment id ψ := by
  simp [density, Matrix.trace, moment, Complex.re_sum, vecMulVec_apply, mul_comm]

private theorem density_moment (p : Fin 4 → Fin 4) (ψ : Amplitude) :
    (observable p * density ψ).trace.re = moment p ψ := by
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [observable, density, vecMulVec_apply, Matrix.mul_apply, ite_mul, mul_comm]

private theorem half_moment (p : Fin 4 → Fin 4) (ψ : Amplitude) :
    moment p (fun i => ψ i / 2) = moment p ψ / 4 := by
  unfold moment
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

/-- The unnormalized branch after the antisymmetric schedule outcome. -/
noncomputable def coherentSelected (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  density (minus a b c d)

/-- The corresponding branch with the early-late coherence removed. -/
noncomputable def dephasedSelected (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  density (fun i => early a b c d i / 2) + density (fun i => late a b c d i / 2)

/-- The two experimentally matched choices yield positive unnormalized
branch states with distinct conditional memory X moments. -/
theorem selected_density_contrast (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0) :
    let C := coherentSelected a b c d
    let D := dephasedSelected a b c d
    let O := memoryX
    C.PosSemidef ∧ D.PosSemidef ∧ 0 < C.trace.re ∧ C.trace.re = d^2 / 2 ∧
      (O * C).trace.re / C.trace.re = -1 ∧ D.trace.re = 1 / 2 ∧
      (O * D).trace.re / D.trace.re = 0 := by
  dsimp only
  have hC : (coherentSelected a b c d).PosSemidef :=
    posSemidef_vecMulVec_self_star _
  have hD : (dephasedSelected a b c d).PosSemidef :=
    (posSemidef_vecMulVec_self_star _).add (posSemidef_vecMulVec_self_star _)
  obtain ⟨hpos, hmass, hparity⟩ := one_record_parity_contrast a b c d train hd
  refine ⟨hC, hD, ?_, ?_, ?_, ?_, ?_⟩
  · rw [coherentSelected, density_trace]; exact hpos
  · rw [coherentSelected, density_trace]; exact hmass
  · rw [coherentSelected, memoryX, density_trace, density_moment]; exact hparity
  · rw [dephasedSelected, Matrix.trace_add, Complex.add_re, density_trace, density_trace,
      half_moment, half_moment, early_mass, late_mass, train, offset]
    norm_num
  · rw [dephasedSelected, memoryX, Matrix.mul_add, Matrix.trace_add, Complex.add_re,
      density_moment, density_moment, half_moment, half_moment, early_parity, late_parity]
    norm_num

open SKEFTHawking.QuantumNetwork

private noncomputable def readPlus : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1/2, 1/2, 0, 0; 1/2, 1/2, 0, 0; 0, 0, 1/2, 1/2; 0, 0, 1/2, 1/2]

private noncomputable def readMinus : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1/2, -(1/2), 0, 0; -(1/2), 1/2, 0, 0; 0, 0, 1/2, -(1/2); 0, 0, -(1/2), 1/2]

private theorem readPlus_gram : readPlusᴴ * readPlus = readPlus := by
  have conjTwo : (starRingEnd ℂ) 2 = 2 := Complex.conj_ofNat 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [readPlus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, conjTwo]

private theorem readMinus_gram : readMinusᴴ * readMinus = readMinus := by
  have conjTwo : (starRingEnd ℂ) 2 = 2 := Complex.conj_ofNat 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [readMinus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, conjTwo]

private theorem read_add : readPlus + readMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [readPlus, readMinus, xMemory, Matrix.one_apply, Fin.ext_iff]

private theorem read_sub : readPlus - readMinus = memoryX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [readPlus, readMinus, memoryX, observable, xMemory, Fin.ext_iff]

/-- The memory X measurement on the retained system and memory. -/
noncomputable def memoryXReadout : FiniteInstrument (Fin 4) 2 where
  count := 1
  operators label _ := if label = 0 then readPlus else readMinus
  normalized := by
    simp [Fin.sum_univ_two, readPlus_gram, readMinus_gram, read_add]

private theorem weight_diff (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryXReadout.weight 0 ρ - memoryXReadout.weight 1 ρ = (memoryX * ρ).trace.re := by
  change (∑ _ : Fin 1, readPlus * ρ * readPlusᴴ).trace.re -
      (∑ _ : Fin 1, readMinus * ρ * readMinusᴴ).trace.re = _
  simp only [Fin.sum_univ_one]
  rw [Matrix.trace_mul_cycle readPlus ρ readPlusᴴ, Matrix.trace_mul_cycle readMinus ρ readMinusᴴ,
    readPlus_gram, readMinus_gram,
    ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul, read_sub]

/-- The plus readout is impossible on the coherent selected branch. The
matched dephased selected branch gives each memory X outcome probability one
quarter before conditioning, with total heralding mass one half. -/
theorem one_record_readout_weights (a b c d : ℝ)
    (train : a^2 + b^2 = 1) (offset : c^2 + d^2 = 1) (hd : d ≠ 0) :
    let C := coherentSelected a b c d
    let D := dephasedSelected a b c d
    memoryXReadout.weight 0 C = 0 ∧ memoryXReadout.weight 1 C = d^2 / 2 ∧
      memoryXReadout.weight 0 D = 1 / 4 ∧ memoryXReadout.weight 1 D = 1 / 4 := by
  dsimp only
  obtain ⟨_, _, hc, hcm, hcp, hdm, hdp⟩ := selected_density_contrast a b c d train offset hd
  let C := coherentSelected a b c d
  let D := dephasedSelected a b c d
  have cs := memoryXReadout.sum_weight C
  have ds := memoryXReadout.sum_weight D
  rw [Fin.sum_univ_two] at cs ds
  have cp := weight_diff C
  have dp := weight_diff D
  have hcMoment := (div_eq_iff hc.ne').mp hcp
  have hdMoment := (div_eq_iff (show D.trace.re ≠ 0 by rw [hdm]; norm_num)).mp hdp
  change C.trace.re = _ at hcm
  change D.trace.re = _ at hdm
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The rational gate fixture has coherent heralding probability `72/169`. -/
theorem rational_coherent_mass :
    (coherentSelected (3/5) (4/5) (5/13) (12/13)).trace.re = 72/169 := by
  rw [coherentSelected, density_trace, minus_mass_raw]
  norm_num

private noncomputable def symmetricAmplitude (a b c d : ℝ) : Amplitude := fun i =>
  (late a b c d i + early a b c d i) / 2

private theorem symmetric_orthogonal (a b c d : ℝ) :
    star (symmetricAmplitude a b c d) ⬝ᵥ minus a b c d = 0 := by
  apply Complex.ext <;>
    simp [dotProduct, symmetricAmplitude, minus, early, late, rotate, xSystem, copyIndex, initial,
      Fin.sum_univ_succ, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  ring

/-- The unnormalized branch after the symmetric schedule outcome. -/
noncomputable def symmetricSelected (a b c d : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  density (symmetricAmplitude a b c d)

private theorem dephased_split (a b c d : ℝ) :
    dephasedSelected a b c d = (1/2 : ℂ) •
      (coherentSelected a b c d + symmetricSelected a b c d) := by
  ext i j
  simp [dephasedSelected, coherentSelected, symmetricSelected, symmetricAmplitude, minus, density,
    Matrix.vecMulVec_apply, Matrix.smul_apply]
  ring

/-- The two timing amplitudes are orthogonal, and the dephased selected
branch is the half-sum of their unnormalized densities. -/
theorem dephasedSelected_split (a b c d : ℝ) :
    let C := coherentSelected a b c d
    let A := symmetricSelected a b c d
    A.PosSemidef ∧ A * C = 0 ∧ dephasedSelected a b c d = (1/2 : ℂ) • (C + A) := by
  refine ⟨posSemidef_vecMulVec_self_star _, ?_, dephased_split a b c d⟩
  dsimp only [symmetricSelected, coherentSelected, density]
  rw [vecMulVec_mul_vecMulVec, symmetric_orthogonal, zero_smul, vecMulVec_zero]

/-- Squaring the selected rank-one density scales it by its selection mass. -/
theorem coherentSelected_sq (a b c d : ℝ) (train : a^2 + b^2 = 1)
    (offset : c^2 + d^2 = 1) (hd : d ≠ 0) :
    let C := coherentSelected a b c d
    C * C = ((d^2 / 2 : ℝ) : ℂ) • C := by
  obtain ⟨hC, _, _, hmass, _, _, _⟩ := selected_density_contrast a b c d train offset hd
  have ht : (coherentSelected a b c d).trace = ((d^2 / 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · exact hmass
    · exact (Complex.le_def.mp hC.trace_nonneg).2.symm
  dsimp only [coherentSelected, density] at ht ⊢
  rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, ← dotProduct_comm (minus a b c d),
    ← Matrix.trace_vecMulVec, ht]

private theorem plus_weight_trace (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryXReadout.weight 0 ρ = (ρ * readPlus).trace.re := by
  change (∑ _ : Fin 1, readPlus * ρ * readPlusᴴ).trace.re = _
  rw [Fin.sum_univ_one, Matrix.trace_mul_cycle, readPlus_gram, Matrix.trace_mul_comm]

private theorem minus_weight_trace (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    memoryXReadout.weight 1 ρ = (ρ * readMinus).trace.re := by
  change (∑ _ : Fin 1, readMinus * ρ * readMinusᴴ).trace.re = _
  rw [Fin.sum_univ_one, Matrix.trace_mul_cycle, readMinus_gram, Matrix.trace_mul_comm]

/-- The memory-X minus projector is a binary effect. Its two trace pairings
are the weights returned by the existing instrument. -/
theorem memoryXReadout_effects (ρ : Matrix (Fin 4) (Fin 4) ℂ) :
    let E := memoryXReadout.operators 1 ⟨0, by decide⟩
    E.PosSemidef ∧ (1 - E).PosSemidef ∧
      memoryXReadout.weight 0 ρ = (ρ * (1 - E)).trace.re ∧
      memoryXReadout.weight 1 ρ = (ρ * E).trace.re := by
  change readMinus.PosSemidef ∧ (1-readMinus).PosSemidef ∧ _
  have hcomp : (1 : Matrix (Fin 4) (Fin 4) ℂ) - readMinus = readPlus := by
    rw [← read_add, add_sub_cancel_right]
  refine ⟨readMinus_gram ▸ posSemidef_conjTranspose_mul_self readMinus,
    hcomp.symm ▸ (readPlus_gram ▸ posSemidef_conjTranspose_mul_self readPlus), ?_,
    minus_weight_trace ρ⟩
  change memoryXReadout.weight 0 ρ = (ρ * (1-readMinus)).trace.re
  rw [hcomp]
  exact plus_weight_trace ρ

end SKEFTHawking.QuantumNetwork.OneRecordCoherentSchedule
