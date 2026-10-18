import SKEFTHawking.FiniteNontracialPauliReflection
import SKEFTHawking.QuantumNetwork.FiniteThreeLevelThermalPhase

/-!
# Fifteen-effect stationary qutrit histories

The reference is the actual three-level thermal equilibrium. The four-event
chronological kernel is derived from normalized replacement Kraus branches.
The reflected Hilbert space describes this fixed finite process only.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelPositiveHistory
open Matrix FiniteInterventionProcess FinitePositiveKernel GibbsObservable
open GibbsMultilevelProcess GibbsMultilevelReflection
open scoped BigOperators ComplexOrder Kronecker

abbrev Q := Fin 3
abbrev MatQ := Matrix Q Q ℂ
abbrev Outcome := Fin 15
abbrev rhoN := FiniteThreeLevelThermalPhase.equilibrium

def weights : Q → ℝ := three.w

theorem weights_pos (i : Q) : 0 < weights i := three.positive i

theorem weights_nonnegative (i : Q) : 0 ≤ weights i := le_of_lt (weights_pos i)

theorem weights_normalized : ∑ i, weights i = 1 := three.normalized

theorem weights_density : DiagonalLindblad.density weights = rhoN := rfl

theorem rhoN_density : IsDensityOperator rhoN :=
  FiniteThreeLevelThermalPhase.equilibrium_density

theorem rhoN_trace : rhoN.trace = 1 := rhoN_density.2

theorem rhoN_posDef : rhoN.PosDef := FiniteThreeLevelThermalPhase.equilibrium_posDef

def rdiag (i : Q) : ℝ := Real.sqrt (weights i)
def R : MatQ := Matrix.diagonal (fun i => (rdiag i : ℂ))
def Gamma (A : MatQ) : MatQ := R * A * R

theorem rdiag_pos (i : Q) : 0 < rdiag i := Real.sqrt_pos.2 (weights_pos i)

theorem rdiag_square (i : Q) : rdiag i * rdiag i = weights i :=
  Real.mul_self_sqrt (weights_nonnegative i)

theorem R_adjoint : Rᴴ = R := by simp [R]

theorem R_square : R * R = rhoN := by
  rw [R, Matrix.diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul, rdiag_square]
  rfl

def E (i j : Q) : MatQ := Matrix.single i j 1
def D (i : Q) : MatQ := E i i
def X (i j : Q) : MatQ := E i j + E j i
def Y (i j : Q) : MatQ := -Complex.I • E i j + Complex.I • E j i

/-- Ordered computational, 01, 02, 12 projectors; each pair is x+,x-,y+,y-. -/
def projector : Outcome → MatQ := ![
  !![1, 0, 0; 0, 0, 0; 0, 0, 0],
  !![0, 0, 0; 0, 1, 0; 0, 0, 0],
  !![0, 0, 0; 0, 0, 0; 0, 0, 1],
  !![1/2, 1/2, 0; 1/2, 1/2, 0; 0, 0, 0],
  !![1/2, -1/2, 0; -1/2, 1/2, 0; 0, 0, 0],
  !![1/2, -Complex.I/2, 0; Complex.I/2, 1/2, 0; 0, 0, 0],
  !![1/2, Complex.I/2, 0; -Complex.I/2, 1/2, 0; 0, 0, 0],
  !![1/2, 0, 1/2; 0, 0, 0; 1/2, 0, 1/2],
  !![1/2, 0, -1/2; 0, 0, 0; -1/2, 0, 1/2],
  !![1/2, 0, -Complex.I/2; 0, 0, 0; Complex.I/2, 0, 1/2],
  !![1/2, 0, Complex.I/2; 0, 0, 0; -Complex.I/2, 0, 1/2],
  !![0, 0, 0; 0, 1/2, 1/2; 0, 1/2, 1/2],
  !![0, 0, 0; 0, 1/2, -1/2; 0, -1/2, 1/2],
  !![0, 0, 0; 0, 1/2, -Complex.I/2; 0, Complex.I/2, 1/2],
  !![0, 0, 0; 0, 1/2, Complex.I/2; 0, -Complex.I/2, 1/2]]

def effect (o : Outcome) : MatQ := (1/5 : ℂ) • projector o

theorem projector_adjoint (o : Outcome) : (projector o)ᴴ = projector o := by
  fin_cases o <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [projector, Matrix.conjTranspose_apply]

theorem projector_trace (o : Outcome) : (projector o).trace = 1 := by
  fin_cases o <;> norm_num [projector, Matrix.trace, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk, Matrix.diagonal_apply]

private theorem projector_compression_0 (A : MatQ) :
    projector 0 * A * projector 0 = (projector 0 * A).trace • projector 0 := by
  change !![1, 0, 0; 0, 0, 0; 0, 0, 0] * A * !![1, 0, 0; 0, 0, 0; 0, 0, 0] = (!![1, 0, 0; 0, 0, 0; 0, 0, 0] * A).trace • !![1, 0, 0; 0, 0, 0; 0, 0, 0]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val]

private theorem projector_compression_1 (A : MatQ) :
    projector 1 * A * projector 1 = (projector 1 * A).trace • projector 1 := by
  change !![0, 0, 0; 0, 1, 0; 0, 0, 0] * A * !![0, 0, 0; 0, 1, 0; 0, 0, 0] = (!![0, 0, 0; 0, 1, 0; 0, 0, 0] * A).trace • !![0, 0, 0; 0, 1, 0; 0, 0, 0]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val]

private theorem projector_compression_2 (A : MatQ) :
    projector 2 * A * projector 2 = (projector 2 * A).trace • projector 2 := by
  change !![0, 0, 0; 0, 0, 0; 0, 0, 1] * A * !![0, 0, 0; 0, 0, 0; 0, 0, 1] = (!![0, 0, 0; 0, 0, 0; 0, 0, 1] * A).trace • !![0, 0, 0; 0, 0, 0; 0, 0, 1]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val]

private theorem projector_compression_3 (A : MatQ) :
    projector 3 * A * projector 3 = (projector 3 * A).trace • projector 3 := by
  change !![1/2, 1/2, 0; 1/2, 1/2, 0; 0, 0, 0] * A * !![1/2, 1/2, 0; 1/2, 1/2, 0; 0, 0, 0] = (!![1/2, 1/2, 0; 1/2, 1/2, 0; 0, 0, 0] * A).trace • !![1/2, 1/2, 0; 1/2, 1/2, 0; 0, 0, 0]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring

private theorem projector_compression_4 (A : MatQ) :
    projector 4 * A * projector 4 = (projector 4 * A).trace • projector 4 := by
  change !![1/2, -1/2, 0; -1/2, 1/2, 0; 0, 0, 0] * A * !![1/2, -1/2, 0; -1/2, 1/2, 0; 0, 0, 0] = (!![1/2, -1/2, 0; -1/2, 1/2, 0; 0, 0, 0] * A).trace • !![1/2, -1/2, 0; -1/2, 1/2, 0; 0, 0, 0]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring

private theorem projector_compression_5 (A : MatQ) :
    projector 5 * A * projector 5 = (projector 5 * A).trace • projector 5 := by
  change !![1/2, -Complex.I/2, 0; Complex.I/2, 1/2, 0; 0, 0, 0] * A * !![1/2, -Complex.I/2, 0; Complex.I/2, 1/2, 0; 0, 0, 0] = (!![1/2, -Complex.I/2, 0; Complex.I/2, 1/2, 0; 0, 0, 0] * A).trace • !![1/2, -Complex.I/2, 0; Complex.I/2, 1/2, 0; 0, 0, 0]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring_nf <;> norm_num [Complex.I_sq]
  all_goals ring

private theorem projector_compression_6 (A : MatQ) :
    projector 6 * A * projector 6 = (projector 6 * A).trace • projector 6 := by
  change !![1/2, Complex.I/2, 0; -Complex.I/2, 1/2, 0; 0, 0, 0] * A * !![1/2, Complex.I/2, 0; -Complex.I/2, 1/2, 0; 0, 0, 0] = (!![1/2, Complex.I/2, 0; -Complex.I/2, 1/2, 0; 0, 0, 0] * A).trace • !![1/2, Complex.I/2, 0; -Complex.I/2, 1/2, 0; 0, 0, 0]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring_nf <;> norm_num [Complex.I_sq]
  all_goals ring

private theorem projector_compression_7 (A : MatQ) :
    projector 7 * A * projector 7 = (projector 7 * A).trace • projector 7 := by
  change !![1/2, 0, 1/2; 0, 0, 0; 1/2, 0, 1/2] * A * !![1/2, 0, 1/2; 0, 0, 0; 1/2, 0, 1/2] = (!![1/2, 0, 1/2; 0, 0, 0; 1/2, 0, 1/2] * A).trace • !![1/2, 0, 1/2; 0, 0, 0; 1/2, 0, 1/2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring

private theorem projector_compression_8 (A : MatQ) :
    projector 8 * A * projector 8 = (projector 8 * A).trace • projector 8 := by
  change !![1/2, 0, -1/2; 0, 0, 0; -1/2, 0, 1/2] * A * !![1/2, 0, -1/2; 0, 0, 0; -1/2, 0, 1/2] = (!![1/2, 0, -1/2; 0, 0, 0; -1/2, 0, 1/2] * A).trace • !![1/2, 0, -1/2; 0, 0, 0; -1/2, 0, 1/2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring

private theorem projector_compression_9 (A : MatQ) :
    projector 9 * A * projector 9 = (projector 9 * A).trace • projector 9 := by
  change !![1/2, 0, -Complex.I/2; 0, 0, 0; Complex.I/2, 0, 1/2] * A * !![1/2, 0, -Complex.I/2; 0, 0, 0; Complex.I/2, 0, 1/2] = (!![1/2, 0, -Complex.I/2; 0, 0, 0; Complex.I/2, 0, 1/2] * A).trace • !![1/2, 0, -Complex.I/2; 0, 0, 0; Complex.I/2, 0, 1/2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring_nf <;> norm_num [Complex.I_sq]
  all_goals ring

private theorem projector_compression_10 (A : MatQ) :
    projector 10 * A * projector 10 = (projector 10 * A).trace • projector 10 := by
  change !![1/2, 0, Complex.I/2; 0, 0, 0; -Complex.I/2, 0, 1/2] * A * !![1/2, 0, Complex.I/2; 0, 0, 0; -Complex.I/2, 0, 1/2] = (!![1/2, 0, Complex.I/2; 0, 0, 0; -Complex.I/2, 0, 1/2] * A).trace • !![1/2, 0, Complex.I/2; 0, 0, 0; -Complex.I/2, 0, 1/2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring_nf <;> norm_num [Complex.I_sq]
  all_goals ring

private theorem projector_compression_11 (A : MatQ) :
    projector 11 * A * projector 11 = (projector 11 * A).trace • projector 11 := by
  change !![0, 0, 0; 0, 1/2, 1/2; 0, 1/2, 1/2] * A * !![0, 0, 0; 0, 1/2, 1/2; 0, 1/2, 1/2] = (!![0, 0, 0; 0, 1/2, 1/2; 0, 1/2, 1/2] * A).trace • !![0, 0, 0; 0, 1/2, 1/2; 0, 1/2, 1/2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring

private theorem projector_compression_12 (A : MatQ) :
    projector 12 * A * projector 12 = (projector 12 * A).trace • projector 12 := by
  change !![0, 0, 0; 0, 1/2, -1/2; 0, -1/2, 1/2] * A * !![0, 0, 0; 0, 1/2, -1/2; 0, -1/2, 1/2] = (!![0, 0, 0; 0, 1/2, -1/2; 0, -1/2, 1/2] * A).trace • !![0, 0, 0; 0, 1/2, -1/2; 0, -1/2, 1/2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring

private theorem projector_compression_13 (A : MatQ) :
    projector 13 * A * projector 13 = (projector 13 * A).trace • projector 13 := by
  change !![0, 0, 0; 0, 1/2, -Complex.I/2; 0, Complex.I/2, 1/2] * A * !![0, 0, 0; 0, 1/2, -Complex.I/2; 0, Complex.I/2, 1/2] = (!![0, 0, 0; 0, 1/2, -Complex.I/2; 0, Complex.I/2, 1/2] * A).trace • !![0, 0, 0; 0, 1/2, -Complex.I/2; 0, Complex.I/2, 1/2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring_nf <;> norm_num [Complex.I_sq]
  all_goals ring

private theorem projector_compression_14 (A : MatQ) :
    projector 14 * A * projector 14 = (projector 14 * A).trace • projector 14 := by
  change !![0, 0, 0; 0, 1/2, Complex.I/2; 0, -Complex.I/2, 1/2] * A * !![0, 0, 0; 0, 1/2, Complex.I/2; 0, -Complex.I/2, 1/2] = (!![0, 0, 0; 0, 1/2, Complex.I/2; 0, -Complex.I/2, 1/2] * A).trace • !![0, 0, 0; 0, 1/2, Complex.I/2; 0, -Complex.I/2, 1/2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;>
    ring_nf <;> norm_num [Complex.I_sq]
  all_goals ring

theorem projector_compression (o : Outcome) (A : MatQ) :
    projector o * A * projector o = (projector o * A).trace • projector o := by
  fin_cases o
  · exact projector_compression_0 A
  · exact projector_compression_1 A
  · exact projector_compression_2 A
  · exact projector_compression_3 A
  · exact projector_compression_4 A
  · exact projector_compression_5 A
  · exact projector_compression_6 A
  · exact projector_compression_7 A
  · exact projector_compression_8 A
  · exact projector_compression_9 A
  · exact projector_compression_10 A
  · exact projector_compression_11 A
  · exact projector_compression_12 A
  · exact projector_compression_13 A
  · exact projector_compression_14 A

theorem projector_idempotent (o : Outcome) : projector o * projector o = projector o := by
  simpa [projector_trace] using projector_compression o 1

theorem projector_posSemidef (o : Outcome) : (projector o).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (projector o)
  rwa [projector_adjoint, projector_idempotent] at h

theorem projector_sum : ∑ o, projector o = (5 : ℂ) • (1 : MatQ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [projector, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk, Matrix.diagonal_apply] <;> ring

theorem effect_sum : ∑ o, effect o = 1 := by
  simp only [effect, ← Finset.smul_sum, projector_sum, smul_smul]
  norm_num

def frameCoeff (A : MatQ) : Outcome → ℂ := ![
  5*A 0 0, 5*A 1 1, 5*A 2 2,
  (5/2)*(A 0 1+A 1 0), -(5/2)*(A 0 1+A 1 0),
  (5*Complex.I/2)*(A 0 1-A 1 0), -(5*Complex.I/2)*(A 0 1-A 1 0),
  (5/2)*(A 0 2+A 2 0), -(5/2)*(A 0 2+A 2 0),
  (5*Complex.I/2)*(A 0 2-A 2 0), -(5*Complex.I/2)*(A 0 2-A 2 0),
  (5/2)*(A 1 2+A 2 1), -(5/2)*(A 1 2+A 2 1),
  (5*Complex.I/2)*(A 1 2-A 2 1), -(5*Complex.I/2)*(A 1 2-A 2 1)]

def frameSynthesis (f : Outcome → ℂ) : MatQ := ∑ o, f o • effect o

theorem frame_right_inverse (A : MatQ) : frameSynthesis (frameCoeff A) = A := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [frameSynthesis, frameCoeff, effect, projector, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk] <;>
    ring_nf <;> norm_num [Complex.I_sq, map_ofNat, map_inv₀] <;> ring

theorem frame_constant : frameSynthesis (fun _ => 1) = 1 := by
  simpa [frameSynthesis] using effect_sum

def d (o : Outcome) : ℝ := (projector o * rhoN).trace.re

theorem d_values (o : Outcome) : d o =
    ![1/2,1/3,1/6,5/12,5/12,5/12,5/12,1/3,1/3,1/3,1/3,1/4,1/4,1/4,1/4] o := by
  fin_cases o <;>
    norm_num [d, projector, FiniteThreeLevelThermalPhase.equilibrium,
      DiagonalLindblad.density, three, GibbsReset.threeWeights,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk, Matrix.diagonal_apply]

theorem d_pos (o : Outcome) : 0 < d o := by
  rw [d_values]; fin_cases o <;> norm_num

theorem d_trace (o : Outcome) : (d o : ℂ) = (projector o * rhoN).trace := by
  rw [d_values]
  fin_cases o <;>
    norm_num [projector, FiniteThreeLevelThermalPhase.equilibrium,
      DiagonalLindblad.density, three, GibbsReset.threeWeights,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk, Matrix.diagonal_apply]

theorem projector_rho_projector (o : Outcome) :
    projector o * rhoN * projector o = (d o : ℂ) • projector o := by
  rw [projector_compression, d_trace]

def c (o : Outcome) : ℂ := (Real.sqrt (5 * d o) : ℂ)⁻¹
def L (o : Outcome) : MatQ := c o • (R * projector o)

theorem c_real (o : Outcome) : star (c o) = c o := by simp [c]

theorem c_square_d (o : Outcome) : c o * c o * (d o : ℂ) = 1/5 := by
  have hd : d o ≠ 0 := ne_of_gt (d_pos o)
  have hc : (d o : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [c, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (mul_pos (by norm_num) (d_pos o)))]
  push_cast
  field_simp

theorem L_effect (o : Outcome) : (L o)ᴴ * L o = effect o := by
  simp only [L, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    projector_adjoint, R_adjoint, c_real, smul_mul_smul]
  have h : projector o * R * (R * projector o) =
      projector o * rhoN * projector o := by rw [← R_square]; noncomm_ring
  rw [h, projector_rho_projector, smul_smul, c_square_d]
  rfl

def instrument : FiniteInstrument Q 15 where
  count := 1
  operators o _ := L o
  normalized := by
    simp only [Fin.sum_univ_one, L_effect, effect]
    rw [← Finset.smul_sum, projector_sum, smul_smul]
    norm_num

def J (o : Outcome) (A : MatQ) : MatQ := (L o)ᴴ * A * L o

theorem instrument_branch (o : Outcome) (X : MatQ) :
    instrument.branch o X = L o * X * (L o)ᴴ := by
  simp [FiniteInstrument.branch, instrument, krausMap]

theorem branch_Gamma (o : Outcome) (A : MatQ) :
    instrument.branch o (Gamma A) = Gamma (J o A) := by
  rw [instrument_branch]
  simp only [Gamma, J, L, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    projector_adjoint, R_adjoint, c_real, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  noncomm_ring

theorem J_one (o : Outcome) : J o 1 = effect o := by
  simpa [J] using L_effect o

theorem branch_rhoN (o : Outcome) : instrument.branch o rhoN = Gamma (effect o) := by
  have h : rhoN = Gamma 1 := by simpa [Gamma] using R_square.symm
  rw [h, branch_Gamma, J_one]

theorem instrument_stationary : ∑ o, instrument.branch o rhoN = rhoN := by
  simp_rw [branch_rhoN, Gamma]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  simp only [effect]
  rw [← Finset.smul_sum, projector_sum, smul_smul]
  norm_num [R_square]

theorem trace_duality (o : Outcome) (A X : MatQ) :
    (A * instrument.branch o X).trace = (J o A * X).trace := by
  rw [instrument_branch, J]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

def channel (q : ℝ) := GibbsReset.timeKraus weights q

def Phi (q : ℝ) (X : MatQ) : MatQ :=
  (q : ℂ) • X + (1-(q : ℂ)) • (X.trace • rhoN)

def Psi (q : ℝ) (A : MatQ) : MatQ :=
  (q : ℂ) • A + (1-(q : ℂ)) • ((rhoN * A).trace • 1)

theorem channel_normalized {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    IsKrausChannel (channel q) :=
  GibbsReset.time_normalized weights weights_nonnegative weights_normalized q hq hq1

theorem channel_state {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (X : MatQ) :
    krausMap (channel q) X = Phi q X := by
  rw [channel, GibbsReset.time_state weights weights_nonnegative q hq hq1, weights_density]
  rfl

theorem channel_observable {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (A : MatQ) :
    Channel.heisenberg (channel q) A = Psi q A := by
  rw [channel, GibbsReset.time_observable weights weights_nonnegative q hq hq1, weights_density]
  rfl

theorem channel_stationary {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    krausMap (channel q) rhoN = rhoN := by
  rw [← weights_density]
  exact GibbsReset.time_stationary weights weights_nonnegative weights_normalized q hq hq1

theorem Gamma_trace (A : MatQ) : (Gamma A).trace = (rhoN * A).trace := by
  rw [Gamma, Matrix.trace_mul_cycle, R_square]

theorem Gamma_one : Gamma 1 = rhoN := by simpa [Gamma] using R_square

theorem Gamma_smul (z : ℂ) (A : MatQ) : Gamma (z • A) = z • Gamma A := by
  simp [Gamma]

theorem Gamma_add (A B : MatQ) : Gamma (A+B) = Gamma A + Gamma B := by
  simp [Gamma, mul_add, add_mul]

theorem Phi_Gamma (q : ℝ) (A : MatQ) : Phi q (Gamma A) = Gamma (Psi q A) := by
  simp only [Phi, Psi, Gamma_trace, Gamma_add, Gamma_smul, Gamma_one]

theorem Phi_Psi_duality (q : ℝ) (A X : MatQ) :
    (A * Phi q X).trace = (Psi q A * X).trace := by
  simp only [Phi, Psi, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    Matrix.trace_add, Matrix.trace_smul, one_mul, smul_eq_mul]
  rw [Matrix.trace_mul_comm A rhoN]
  ring

theorem Psi_mean (q : ℝ) (A : MatQ) : (rhoN * Psi q A).trace = (rhoN*A).trace := by
  simp only [Psi, mul_add, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul,
    mul_one, rhoN_trace, smul_eq_mul, mul_one]
  ring

theorem Psi_comp (p q : ℝ) (A : MatQ) : Psi p (Psi q A) = Psi (p*q) A := by
  rw [Psi, Psi_mean]
  simp only [Psi, smul_add, smul_smul, Complex.ofReal_mul]
  module

theorem Phi_one (X : MatQ) : Phi 1 X = X := by simp [Phi]
theorem Phi_zero (X : MatQ) : Phi 0 X = X.trace • rhoN := by simp [Phi]
theorem Psi_one (A : MatQ) : Psi 1 A = A := by simp [Psi]
theorem Psi_zero (A : MatQ) : Psi 0 A = (rhoN*A).trace • 1 := by simp [Psi]

theorem Psi_unital (q : ℝ) : Psi q 1 = 1 := by
  simp only [Psi, mul_one, rhoN_trace, one_smul]
  module

theorem Psi_smul (q : ℝ) (z : ℂ) (A : MatQ) : Psi q (z • A) = z • Psi q A := by
  simp only [Psi, mul_smul_comm, Matrix.trace_smul, smul_add, smul_smul, smul_eq_mul]
  module

theorem Psi_add (q : ℝ) (A B : MatQ) : Psi q (A+B) = Psi q A + Psi q B := by
  simp only [Psi, mul_add, Matrix.trace_add, smul_add, add_smul]
  module

theorem rhoN_adjoint : rhoNᴴ = rhoN := rhoN_density.1.isHermitian.eq

theorem Psi_adjoint (q : ℝ) (A : MatQ) : (Psi q A)ᴴ = Psi q Aᴴ := by
  simp only [Psi, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_sub, star_one, Complex.star_def, Complex.conj_ofReal,
    ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, rhoN_adjoint]
  rw [Matrix.trace_mul_comm Aᴴ rhoN]

theorem Gamma_adjoint (A : MatQ) : (Gamma A)ᴴ = Gamma Aᴴ := by
  simp [Gamma, Matrix.conjTranspose_mul, R_adjoint, Matrix.mul_assoc]

/-- Symmetric square-root-weighted form, with conjugation in its first argument. -/
def form (A B : MatQ) : ℂ := (B * R * Aᴴ * R).trace

theorem form_Psi_symmetric (q : ℝ) (A B : MatQ) :
    form A (Psi q B) = form (Psi q A) B := by
  simp only [form, Psi_adjoint]
  change (Psi q B * R * Aᴴ * R).trace = (B * R * Psi q Aᴴ * R).trace
  have hg (X Y : MatQ) : (X*R*Y*R).trace = (X*Gamma Y).trace := by
    simp only [Gamma, Matrix.mul_assoc]
  rw [hg, hg]
  rw [← Phi_Gamma, Phi_Psi_duality]

def qdiag (i : Q) : ℝ := Real.sqrt (rdiag i)
def Q4 : MatQ := Matrix.diagonal (fun i => (qdiag i : ℂ))
def feature (A : MatQ) : MatQ := Q4 * A * Q4

theorem qdiag_pos (i : Q) : 0 < qdiag i := Real.sqrt_pos.2 (rdiag_pos i)

theorem Q4_adjoint : Q4ᴴ = Q4 := by simp [Q4]

theorem qdiag_square (i : Q) : qdiag i * qdiag i = rdiag i :=
  Real.mul_self_sqrt (le_of_lt (rdiag_pos i))

theorem Q4_square : Q4 * Q4 = R := by
  rw [Q4, Matrix.diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul, qdiag_square]
  rfl

theorem feature_injective : Function.Injective feature := by
  intro A B h
  ext i j
  have he := congrArg (fun M : MatQ => M i j) h
  simp only [feature, Q4, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  have hi : (qdiag i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (qdiag_pos i)
  have hj : (qdiag j : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (qdiag_pos j)
  exact mul_left_cancel₀ hi (mul_right_cancel₀ hj he)

theorem feature_gram (A B : MatQ) : (feature B * (feature A)ᴴ).trace = form A B := by
  simp only [feature, Matrix.conjTranspose_mul, Q4_adjoint, form]
  rw [← Matrix.mul_assoc Q4 Aᴴ Q4]
  calc
    (Q4*B*Q4*(Q4*Aᴴ*Q4)).trace = (Q4*(B*(Q4*Q4)*Aᴴ)*Q4).trace := by congr 1; noncomm_ring
    _ = (Q4*Q4*(B*(Q4*Q4)*Aᴴ)).trace := Matrix.trace_mul_cycle _ _ _
    _ = (R*(B*R*Aᴴ)).trace := by rw [Q4_square]
    _ = (B*R*Aᴴ*R).trace := Matrix.trace_mul_comm _ _

abbrev HalfHistory := Outcome × Outcome

/-- The actual reset Kraus evolution precedes the actual replacement instrument. -/
def step (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) : Step Q Unit 15 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (channel q k)
  normalized := GibbsMultilevelReflection.joint_normalized _ (channel_normalized hq hq1)
  instrument := instrument

theorem step_branch (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (o : Outcome) (X : MatQ) :
    (step q hq hq1).branch Q Unit 15 o (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint (instrument.branch o (Phi q X)) := by
  change (instrument.lift Unit).branch o
    (krausMap (fun k => GibbsMultilevelReflection.joint (channel q k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus, channel_state hq hq1]
  exact GibbsMultilevelReflection.joint_kraus _ _

def negativeTree (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : Tree Q Unit 15 2 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step r hr hr1) (fun _ => .done))

/-- Half labels are (inner,outer); chronology is outer,inner,inner,outer. -/
def fourTree (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Tree Q Unit 15 4 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step r hr hr1) (fun _ =>
      .node (step (p*p) (mul_nonneg hp hp) (by nlinarith)) (fun _ =>
        .node (step r hr hr1) (fun _ => .done))))

/-- Defined from the actual four-node process weight before the Gram theorem. -/
def kernel (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) : ℂ :=
  (weight Q Unit 15 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

def halfEffect (r : ℝ) (u : HalfHistory) : MatQ :=
  J u.1 (Psi r (effect u.2))

def midpoint (p r : ℝ) (u : HalfHistory) : MatQ := Psi p (halfEffect r u)

theorem J_adjoint (o : Outcome) (A : MatQ) : (J o A)ᴴ = J o Aᴴ := by
  simp [J, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem effect_adjoint (o : Outcome) :
    (effect o)ᴴ = effect o := by
  simp [effect, Matrix.conjTranspose_smul,
    projector_adjoint]

theorem halfEffect_adjoint (r : ℝ) (u : HalfHistory) : (halfEffect r u)ᴴ = halfEffect r u := by
  rw [halfEffect, J_adjoint, Psi_adjoint, effect_adjoint]

theorem midpoint_adjoint (p r : ℝ) (u : HalfHistory) :
    (midpoint p r u)ᴴ = midpoint p r u := by
  rw [midpoint, Psi_adjoint, halfEffect_adjoint]

theorem branch_trace (o : Outcome) (X : MatQ) :
    (instrument.branch o X).trace = (effect o * X).trace := by
  simpa only [one_mul, J_one] using trace_duality o 1 X

/-- Actual negative-half state, retaining the nontracial square-root sandwich. -/
theorem negative_run (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : HalfHistory) :
    run Q Unit 15 (negativeTree r hr hr1) (u.2,u.1,())
      (GibbsMultilevelReflection.joint rhoN) =
    GibbsMultilevelReflection.joint (Gamma (halfEffect r u)) := by
  change (step r hr hr1).branch Q Unit 15 u.1
    ((step 1 (by norm_num) le_rfl).branch Q Unit 15 u.2
      (GibbsMultilevelReflection.joint rhoN)) = _
  rw [step_branch, step_branch, Phi_one, branch_rhoN, Phi_Gamma, branch_Gamma]
  rfl

theorem actual_run (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) :
    run Q Unit 15 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rhoN) =
    GibbsMultilevelReflection.joint (instrument.branch v.2
      (Phi r (instrument.branch v.1 (Phi (p*p) (Gamma (halfEffect r u)))))) := by
  change (step r hr hr1).branch Q Unit 15 v.2
    ((step (p*p) (mul_nonneg hp hp) (by nlinarith)).branch Q Unit 15 v.1
      (run Q Unit 15 (negativeTree r hr hr1) (u.2,u.1,())
        (GibbsMultilevelReflection.joint rhoN))) = _
  rw [negative_run, step_branch, step_branch]

theorem actual_trace (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) :
    (run Q Unit 15 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rhoN)).trace =
      (halfEffect r v * Phi (p*p) (Gamma (halfEffect r u))).trace := by
  rw [actual_run, GibbsMultilevelReflection.joint_trace, branch_trace,
    Phi_Psi_duality, trace_duality]
  rfl

theorem hermitian_product_real (A B : MatQ) (hA : Aᴴ=A) (hB : Bᴴ=B) :
    (((A*B).trace.re : ℝ) : ℂ) = (A*B).trace := by
  have hc : star (A*B).trace = (A*B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hB,
      Matrix.trace_mul_comm]
  have hi := Complex.conj_eq_iff_im.mp hc
  apply Complex.ext
  · rfl
  · simpa using hi.symm

/-- The actual real process weight is the full complex trace, also for imaginary projector labels. -/
theorem kernel_trace (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) :
    kernel p r hp hp1 hr hr1 u v =
      (halfEffect r v * Phi (p*p) (Gamma (halfEffect r u))).trace := by
  unfold kernel weight
  rw [actual_trace]
  apply hermitian_product_real _ _ (halfEffect_adjoint r v)
  rw [Phi_Gamma, Gamma_adjoint, Psi_adjoint, halfEffect_adjoint]

theorem central_split (p : ℝ) (A B : MatQ) :
    (B * Phi (p*p) (Gamma A)).trace = (Psi p B * Gamma (Psi p A)).trace := by
  rw [Phi_Gamma, ← Psi_comp, ← Phi_Gamma, Phi_Psi_duality]

/-- Derived from actual chronology, both dual maps, and branchwise reversal. -/
theorem kernel_form (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) :
    kernel p r hp hp1 hr hr1 u v = form (midpoint p r u) (midpoint p r v) := by
  rw [kernel_trace, central_split]
  rw [form, midpoint_adjoint]
  simp only [midpoint, Gamma, Matrix.mul_assoc]

def synthesis (p r : ℝ) (F : HalfHistory → ℂ) : MatQ := ∑ u, F u • midpoint p r u

theorem feature_synthesis (p r : ℝ) (F : HalfHistory → ℂ) :
    feature (synthesis p r F) = ∑ u, F u • feature (midpoint p r u) := by
  simp only [feature, synthesis, Matrix.mul_sum, Matrix.sum_mul, mul_smul_comm, smul_mul_assoc]

theorem kernel_posSemidef (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Matrix.PosSemidef (kernel p r hp hp1 hr hr1) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup (1 : MatQ) Matrix.PosSemidef.one
  letI := Matrix.toMatrixInnerProductSpace (1 : MatQ) Matrix.PosSemidef.one
  have hk : kernel p r hp hp1 hr hr1 = Matrix.gram ℂ (fun u => feature (midpoint p r u)) := by
    ext u v
    rw [kernel_form, ← feature_gram]
    change (feature (midpoint p r v) * (feature (midpoint p r u))ᴴ).trace =
      (feature (midpoint p r v) * 1 * (feature (midpoint p r u))ᴴ).trace
    simp
  rw [hk]
  exact Matrix.posSemidef_gram ℂ _

/-- Arbitrary complex coefficients use the square-root-weighted form. -/
theorem pairing_synthesis (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (F G : HalfHistory → ℂ) :
    pairing (kernel p r hp hp1 hr hr1) F G = form (synthesis p r F) (synthesis p r G) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup (1 : MatQ) Matrix.PosSemidef.one
  letI := Matrix.toMatrixInnerProductSpace (1 : MatQ) Matrix.PosSemidef.one
  have hk : kernel p r hp hp1 hr hr1 = Matrix.gram ℂ (fun u => feature (midpoint p r u)) := by
    ext u v
    rw [kernel_form, ← feature_gram]
    change (feature (midpoint p r v) * (feature (midpoint p r u))ᴴ).trace =
      (feature (midpoint p r v) * 1 * (feature (midpoint p r u))ᴴ).trace
    simp
  rw [hk]
  unfold pairing
  rw [Matrix.star_dotProduct_gram_mulVec, ← feature_synthesis, ← feature_synthesis]
  change (feature (synthesis p r G) * 1 * (feature (synthesis p r F))ᴴ).trace = _
  simpa using feature_gram (synthesis p r F) (synthesis p r G)

def PsiLinear (q : ℝ) : MatQ →ₗ[ℂ] MatQ where
  toFun := Psi q
  map_add' := Psi_add q
  map_smul' := Psi_smul q

def JLinear (o : Outcome) : MatQ →ₗ[ℂ] MatQ where
  toFun := J o
  map_add' A B := by simp [J, mul_add, add_mul]
  map_smul' z A := by simp [J]

theorem Psi_sum {ι : Type*} [Fintype ι] (q : ℝ) (A : ι → MatQ) :
    Psi q (∑ i, A i) = ∑ i, Psi q (A i) :=
  map_sum (PsiLinear q) A Finset.univ

/-- The actual observable dual is unital, including complete side reset. -/
theorem halfEffect_outer (r : ℝ) (i : Outcome) :
    ∑ o, halfEffect r (i,o) = effect i := by
  change (∑ o, JLinear i (PsiLinear r (effect o))) = _
  rw [← map_sum, ← map_sum, effect_sum]
  change J i (Psi r 1) = _
  rw [Psi_unital, J_one]

theorem midpoint_outer (p r : ℝ) (i : Outcome) :
    ∑ o, midpoint p r (i,o) = Psi p (effect i) := by
  simp only [midpoint, ← Psi_sum, halfEffect_outer]

/-- The explicit complex frame coefficients are used on the inner outcome. -/
theorem synthesis_inner (p r : ℝ) (F : Outcome → ℂ) :
    synthesis p r (fun u => F u.1) = Psi p (frameSynthesis F) := by
  unfold synthesis
  rw [Fintype.sum_prod_type]
  simp only [← Finset.smul_sum, midpoint_outer, ← Psi_smul, ← Psi_sum]
  rfl

def synthesisLinear (p r : ℝ) : (HalfHistory → ℂ) →ₗ[ℂ] MatQ where
  toFun := synthesis p r
  map_add' F G := by simp [synthesis, add_smul, Finset.sum_add_distrib]
  map_smul' z F := by simp [synthesis, Finset.smul_sum, smul_smul]

def featureLinear : MatQ →ₗ[ℂ] MatQ where
  toFun := feature
  map_add' A B := by simp [feature, mul_add, add_mul]
  map_smul' z A := by simp [feature]

theorem feature_surjective : Function.Surjective feature :=
  LinearMap.surjective_of_injective (f := featureLinear) feature_injective

theorem synthesis_constant (p r : ℝ) : synthesis p r (fun _ => 1) = 1 := by
  rw [synthesis_inner p r (fun _ => 1), frame_constant, Psi_unital]

def inversePsi (p : ℝ) (A : MatQ) : MatQ :=
  (rhoN*A).trace • 1 + (p : ℂ)⁻¹ • (A - (rhoN*A).trace • 1)

theorem mean_centered (A : MatQ) : (rhoN * (A - (rhoN*A).trace • 1)).trace = 0 := by
  simp [mul_sub, Matrix.trace_sub, Matrix.trace_smul, rhoN_trace]

theorem Psi_centered (p : ℝ) (A : MatQ) :
    Psi p (A - (rhoN*A).trace • 1) = (p : ℂ) • (A - (rhoN*A).trace • 1) := by
  rw [Psi, mean_centered]
  simp

theorem Psi_inverse {p : ℝ} (hp : 0 < p) (A : MatQ) : Psi p (inversePsi p A) = A := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  rw [inversePsi, Psi_add, Psi_smul, Psi_unital, Psi_smul, Psi_centered,
    smul_smul, inv_mul_cancel₀ hpC, one_smul]
  module

def coefficients (p : ℝ) (A : MatQ) (u : HalfHistory) : ℂ :=
  frameCoeff (inversePsi p A) u.1

theorem synthesis_coefficients {p : ℝ} (hp : 0 < p) (r : ℝ) (A : MatQ) :
    synthesis p r (coefficients p A) = A := by
  change synthesis p r (fun u => frameCoeff (inversePsi p A) u.1) = _
  rw [synthesis_inner, frame_right_inverse, Psi_inverse hp]

def resetMean (r : ℝ) (F : HalfHistory → ℂ) : ℂ :=
  (rhoN * ∑ u, F u • halfEffect r u).trace

theorem synthesis_full_reset (r : ℝ) (F : HalfHistory → ℂ) :
    synthesis 0 r F = resetMean r F • 1 := by
  simp only [synthesis, midpoint, Psi_zero, resetMean, Matrix.mul_sum,
    mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    Finset.sum_smul, smul_smul]

theorem resetMean_constant (r : ℝ) : resetMean r (fun _ => 1) = 1 := by
  have h := congrArg (fun A : MatQ => A 0 0) (synthesis_constant 0 r)
  rw [synthesis_full_reset] at h
  simpa using h

/-- New-instrument two-event process at central retention p². -/
def twoTree (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : Tree Q Unit 15 2 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step (p*p) (mul_nonneg hp hp) (by nlinarith)) (fun _ => .done))

def twoKernel (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i j : Outcome) : ℂ :=
  (weight Q Unit 15 (twoTree p hp hp1) (i,j,())
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem twoKernel_trace (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i j : Outcome) :
    twoKernel p hp hp1 i j = (effect j *
      Phi (p*p) (Gamma (effect i))).trace := by
  unfold twoKernel weight
  change (((step (p*p) (mul_nonneg hp hp) (by nlinarith)).branch Q Unit 15 j
    ((step 1 (by norm_num) le_rfl).branch Q Unit 15 i
      (GibbsMultilevelReflection.joint rhoN))).trace.re : ℂ) = _
  rw [step_branch, step_branch, Phi_one, branch_rhoN,
    GibbsMultilevelReflection.joint_trace, branch_trace]
  apply hermitian_product_real _ _ (effect_adjoint j)
  rw [Phi_Gamma, Gamma_adjoint, Psi_adjoint, effect_adjoint]

theorem Phi_sum {ι : Type*} [Fintype ι] (q : ℝ) (A : ι → MatQ) :
    Phi q (∑ i, A i) = ∑ i, Phi q (A i) := by
  simp [Phi, Matrix.trace_sum, Finset.smul_sum, Finset.sum_smul, Finset.sum_add_distrib]

theorem Gamma_sum {ι : Type*} [Fintype ι] (A : ι → MatQ) :
    Gamma (∑ i, A i) = ∑ i, Gamma (A i) := by
  simp [Gamma, Matrix.mul_sum, Matrix.sum_mul]

/-- Literal summation of both outer labels of the actual four-event weights. -/
theorem outer_marginal (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (i j : Outcome) :
    ∑ o, ∑ o', kernel p r hp hp1 hr hr1 (i,o) (j,o') = twoKernel p hp hp1 i j := by
  simp_rw [kernel_trace]
  simp only [← Matrix.trace_sum, ← Matrix.sum_mul, halfEffect_outer,
    ← Matrix.mul_sum, ← Phi_sum, ← Gamma_sum]
  rw [twoKernel_trace]


theorem form_one : form 1 1 = 1 := by
  simpa [form, R_square] using rhoN_trace

theorem form_self_zero_iff (A : MatQ) : form A A = 0 ↔ A = 0 := by
  constructor
  · intro h
    rw [← feature_gram] at h
    have hz : feature A = 0 := GibbsObservable.trace_weighted_eq_zero
      (show (1 : MatQ).PosDef from Matrix.PosDef.one) _ (by simpa using h)
    apply feature_injective
    simpa [feature] using hz
  · rintro rfl
    simp [form]

section Reconstruction
open scoped InnerProductSpace
/-- Identity weight installs the Hilbert-Schmidt structure, not the entry sup norm. -/
local instance : NormedAddCommGroup MatQ := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance : InnerProductSpace ℂ MatQ := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)

abbrev Reconstructed := Space (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)

theorem null_iff (F : HalfHistory → ℂ) :
    mk (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) F = 0 ↔
      synthesis p r F = 0 := by
  rw [mk_eq_zero_iff, pairing_synthesis, form_self_zero_iff]

def coefficientSynthesis : Coefficients (kernel_posSemidef p r hp hp1 hr hr1) →ₗ[ℂ] MatQ :=
  synthesisLinear p r

theorem synthesis_null : nullSpace (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) ≤
    (coefficientSynthesis p r hp hp1 hr hr1).ker := by
  intro F hF
  change synthesis p r F = 0
  apply (null_iff p r hp hp1 hr hr1 F).mp
  rw [mk_eq_zero_iff]
  exact (mem_nullSpace_iff _ _ F).mp hF

/-- Algebraic coordinates descend through exactly the actual kernel null space. -/
def coordinates : Reconstructed p r hp hp1 hr hr1 →ₗ[ℂ] MatQ :=
  ((nullSpace (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)).liftQ
    (coefficientSynthesis p r hp hp1 hr hr1) (synthesis_null p r hp hp1 hr hr1)).comp
      (quotientEquiv (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)).symm.toLinearMap

theorem coordinates_mk (F : HalfHistory → ℂ) :
    coordinates p r hp hp1 hr hr1 (mk _ _ F) = synthesis p r F := by
  rw [← quotientEquiv_mk (kernel_posSemidef p r hp hp1 hr hr1) F]
  simp only [coordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  rfl

theorem coordinates_injective : Function.Injective (coordinates p r hp hp1 hr hr1) := by
  intro z w h
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  obtain ⟨G,rfl⟩ := mk_surjective _ _ w
  rw [coordinates_mk, coordinates_mk] at h
  apply (mk_eq_mk_iff _ _ F G).mpr
  rw [pairing_synthesis]
  have hz : synthesis p r (F-G) = 0 :=
    (synthesisLinear p r).map_sub F G |>.trans (sub_eq_zero.mpr h)
  simp [hz, form]

theorem coordinates_surjective (hpos : 0 < p) : Function.Surjective (coordinates p r hp hp1 hr hr1) := by
  intro A
  exact ⟨mk _ _ (coefficients p A), by rw [coordinates_mk, synthesis_coefficients hpos]⟩

def coordinateEquiv (hpos : 0 < p) : Reconstructed p r hp hp1 hr hr1 ≃ₗ[ℂ] MatQ :=
  LinearEquiv.ofBijective (coordinates p r hp hp1 hr hr1)
    ⟨coordinates_injective p r hp hp1 hr hr1, coordinates_surjective p r hp hp1 hr hr1 hpos⟩

theorem reconstructed_finrank (hpos : 0 < p) :
    Module.finrank ℂ (Reconstructed p r hp hp1 hr hr1) = 9 := by
  rw [(coordinateEquiv p r hp hp1 hr hr1 hpos).finrank_eq]
  simpa using Module.finrank_matrix ℂ ℂ Q Q

def embeddingLinear : Reconstructed p r hp hp1 hr hr1 →ₗ[ℂ] MatQ :=
  featureLinear.comp (coordinates p r hp hp1 hr hr1)

theorem embeddingLinear_mk (F : HalfHistory → ℂ) :
    embeddingLinear p r hp hp1 hr hr1 (mk _ _ F) = feature (synthesis p r F) := by
  change feature (coordinates p r hp hp1 hr hr1 (mk _ _ F)) = _
  rw [coordinates_mk]

/-- The actual Q4-sandwich is isometric for the Hilbert-Schmidt target. -/
def embedding : Reconstructed p r hp hp1 hr hr1 →ₗᵢ[ℂ] MatQ :=
  (embeddingLinear p r hp hp1 hr hr1).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [embeddingLinear_mk, embeddingLinear_mk, inner_mk, pairing_synthesis]
    change (feature (synthesis p r G) * 1 * (feature (synthesis p r F))ᴴ).trace = _
    simpa using feature_gram (synthesis p r F) (synthesis p r G))

theorem embedding_mk (F : HalfHistory → ℂ) :
    embedding p r hp hp1 hr hr1 (mk _ _ F) = feature (synthesis p r F) :=
  embeddingLinear_mk p r hp hp1 hr hr1 F

/-- The range consists exactly of Q4*S(F)*Q4 for actual history coefficients. -/
theorem embedding_range : (embedding p r hp hp1 hr hr1).range =
    (featureLinear.comp (synthesisLinear p r)).range := by
  ext A
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    exact ⟨F, (embedding_mk p r hp hp1 hr hr1 F).symm⟩
  · rintro ⟨F,rfl⟩
    exact ⟨mk _ _ F, embedding_mk p r hp hp1 hr hr1 F⟩

/-- An isometric equivalence with the actual matrix range, for all p including zero. -/
def rangeEquiv : Reconstructed p r hp hp1 hr hr1 ≃ₗᵢ[ℂ]
    (embedding p r hp hp1 hr hr1).range := (embedding p r hp hp1 hr hr1).equivRange

theorem embedding_surjective (hpos : 0 < p) : Function.Surjective (embedding p r hp hp1 hr hr1) := by
  intro A
  obtain ⟨B,rfl⟩ := feature_surjective A
  refine ⟨mk _ _ (coefficients p B), ?_⟩
  rw [embedding_mk, synthesis_coefficients hpos]

theorem full_matrix_range (hpos : 0 < p) : (embedding p r hp hp1 hr hr1).range = ⊤ :=
  LinearMap.range_eq_top.mpr (embedding_surjective p r hp hp1 hr hr1 hpos)

theorem reset_null_iff (F : HalfHistory → ℂ) :
    mk (kernel 0 r (by norm_num) (by norm_num) hr hr1)
      (kernel_posSemidef 0 r (by norm_num) (by norm_num) hr hr1) F = 0 ↔ resetMean r F = 0 := by
  rw [null_iff, synthesis_full_reset]
  constructor
  · intro h
    have he := congrArg (fun A : MatQ => A 0 0) h
    simpa using he
  · intro h
    simp [h]

def resetCoordinates : Reconstructed 0 r (by norm_num) (by norm_num) hr hr1 →ₗ[ℂ] ℂ where
  toFun z := coordinates 0 r (by norm_num) (by norm_num) hr hr1 z 0 0
  map_add' z w := by simp
  map_smul' c z := by simp

theorem resetCoordinates_mk (F : HalfHistory → ℂ) :
    resetCoordinates r hr hr1 (mk _ _ F) = resetMean r F := by
  change coordinates 0 r (by norm_num) (by norm_num) hr hr1 (mk _ _ F) 0 0 = _
  rw [coordinates_mk, synthesis_full_reset]
  simp

theorem resetCoordinates_bijective : Function.Bijective (resetCoordinates r hr hr1) := by
  constructor
  · intro z w h
    apply coordinates_injective 0 r (by norm_num) (by norm_num) hr hr1
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [resetCoordinates_mk, resetCoordinates_mk] at h
    rw [coordinates_mk, coordinates_mk, synthesis_full_reset, synthesis_full_reset, h]
  · intro c
    refine ⟨c • mk _ _ (fun _ => 1), ?_⟩
    rw [map_smul, resetCoordinates_mk, resetMean_constant]
    simp

def resetCoordinateEquiv : Reconstructed 0 r (by norm_num) (by norm_num) hr hr1 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (resetCoordinates r hr hr1) (resetCoordinates_bijective r hr hr1)

theorem reset_finrank : Module.finrank ℂ (Reconstructed 0 r (by norm_num) (by norm_num) hr hr1) = 1 := by
  rw [(resetCoordinateEquiv r hr hr1).finrank_eq]
  exact Module.finrank_self ℂ

theorem reset_embedding (F : HalfHistory → ℂ) :
    embedding 0 r (by norm_num) (by norm_num) hr hr1 (mk _ _ F) = resetMean r F • R := by
  rw [embedding_mk, synthesis_full_reset]
  simp [feature, Q4_square]

theorem reset_matrix_range : (embedding 0 r (by norm_num) (by norm_num) hr hr1).range =
    Submodule.span ℂ {R} := by
  ext A
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    exact ⟨resetMean r F, (reset_embedding r hr hr1 F).symm⟩
  · rintro ⟨c,rfl⟩
    refine ⟨c • mk _ _ (fun _ => 1), ?_⟩
    rw [map_smul]
    change c • embedding 0 r (by norm_num) (by norm_num) hr hr1 (mk _ _ (fun _ => 1)) = _
    rw [reset_embedding, resetMean_constant, one_smul]

theorem constant_pairing : pairing (kernel p r hp hp1 hr hr1) (fun _ => 1) (fun _ => 1) = 1 := by
  rw [pairing_synthesis, synthesis_constant, form_one]

theorem constant_norm_sq :
    ‖mk (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) (fun _ => 1)‖^2 = 1 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_mk, constant_pairing]
  rfl

/-- Sum of the actual chronological weights, including impossible outcomes. -/
theorem kernel_total : ∑ u, ∑ v, kernel p r hp hp1 hr hr1 u v = 1 := by
  have h := constant_pairing p r hp hp1 hr hr1
  simpa [pairing, dotProduct, Matrix.mulVec] using h

theorem joint_density : IsDensityOperator (GibbsMultilevelReflection.joint rhoN) := by
  refine ⟨rhoN_density.1.kronecker Matrix.PosSemidef.one, ?_⟩
  rw [GibbsMultilevelReflection.joint_trace, rhoN_trace]

theorem actual_probabilities :
    (∀ h, 0 ≤ weight Q Unit 15 (fourTree p r hp hp1 hr hr1) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h, weight Q Unit 15 (fourTree p r hp hp1 hr hr1) h
      (GibbsMultilevelReflection.joint rhoN)) = 1 :=
  normalized_weights Q Unit 15 _ joint_density

theorem kernel_entry_nonnegative (u v : HalfHistory) : 0 ≤ (kernel p r hp hp1 hr hr1 u v).re :=
  (actual_probabilities p r hp hp1 hr hr1).1 _

end Reconstruction

/-- Endpoint channel actions are actual Kraus evaluations and require no inverses. -/
theorem channel_endpoints (A : MatQ) :
    krausMap (channel 0) A = A.trace • rhoN ∧
    krausMap (channel 1) A = A ∧
    Channel.heisenberg (channel 0) A = (rhoN*A).trace • 1 ∧
    Channel.heisenberg (channel 1) A = A := by
  rw [channel_state (by norm_num) (by norm_num),
    channel_state (by norm_num) (by norm_num),
    channel_observable (by norm_num) (by norm_num),
    channel_observable (by norm_num) (by norm_num), Phi_zero, Phi_one, Psi_zero, Psi_one]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem side_reset_halfEffect (u : HalfHistory) :
    halfEffect 0 u = (rhoN * effect u.2).trace •
      effect u.1 := by
  rw [halfEffect, Psi_zero]
  change JLinear u.1 (_ • 1) = _
  rw [map_smul]
  change _ • J u.1 1 = _
  rw [J_one]

theorem side_identity_halfEffect (u : HalfHistory) :
    halfEffect 1 u = J u.1 (effect u.2) := by
  rw [halfEffect, Psi_one]


/-- Real nonnegative overlap of two explicit rank-one outcomes. -/
def overlap (i j : Outcome) : ℝ := (projector j * Gamma (projector i)).trace.re

theorem overlap_cast (i j : Outcome) :
    (overlap i j : ℂ) = (projector j * Gamma (projector i)).trace := by
  apply hermitian_product_real _ _ (projector_adjoint j)
  rw [Gamma_adjoint, projector_adjoint]

theorem overlap_symmetric (i j : Outcome) : overlap i j = overlap j i := by
  apply Complex.ofReal_injective
  rw [overlap_cast, overlap_cast]
  simp only [Gamma, ← Matrix.mul_assoc]
  calc
    (projector j * R * projector i * R).trace =
        ((projector j * R) * (projector i * R)).trace := by rw [Matrix.mul_assoc]
    _ = ((projector i * R) * (projector j * R)).trace := Matrix.trace_mul_comm _ _
    _ = (projector i * R * projector j * R).trace := by simp only [Matrix.mul_assoc]

theorem overlap_nonnegative (i j : Outcome) : 0 ≤ overlap i j := by
  have hG : (Gamma (projector i)).PosSemidef := by
    simpa [Gamma, R_adjoint] using (projector_posSemidef i).conjTranspose_mul_mul_same R
  have h := trace_mul_nonneg (projector_posSemidef j) hG
  exact h.1

theorem c_square (i : Outcome) : c i * c i = 1 / (5 * (d i : ℂ)) := by
  have hd : (d i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (d_pos i)
  have h := c_square_d i
  apply (mul_right_cancel₀ hd)
  rw [h]
  field_simp

theorem J_compressed (i : Outcome) (A : MatQ) :
    J i A = (c i * c i * (projector i * Gamma A).trace) • projector i := by
  simp only [J, L, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    projector_adjoint, R_adjoint, c_real, smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : projector i * R * A * (R * projector i) =
      projector i * Gamma A * projector i := by unfold Gamma; noncomm_ring
  rw [h, projector_compression, smul_smul]

theorem mean_effect (o : Outcome) : (rhoN * effect o).trace = (d o : ℂ)/5 := by
  rw [effect, mul_smul_comm, Matrix.trace_smul, Matrix.trace_mul_comm, ← d_trace]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem J_effect (i o : Outcome) :
    J i (effect o) = ((overlap i o : ℂ)/(25*(d i : ℂ))) • projector i := by
  rw [J_compressed, effect, Gamma_smul, mul_smul_comm, Matrix.trace_smul,
    ← overlap_cast, overlap_symmetric o i, c_square]
  congr 1
  simp only [smul_eq_mul]
  ring

/-- The universal half-history coefficient, for all 225 pairs. -/
def halfCoefficient (r : ℝ) (i o : Outcome) : ℝ :=
  (r * overlap i o / d i + (1-r)*d o)/25

theorem halfEffect_factored (r : ℝ) (i o : Outcome) :
    halfEffect r (i,o) = (halfCoefficient r i o : ℂ) • projector i := by
  unfold halfEffect Psi
  change JLinear i ((r:ℂ) • effect o + (1-(r:ℂ)) • ((rhoN*effect o).trace • 1)) = _
  rw [map_add, map_smul, map_smul, map_smul]
  change (r:ℂ) • J i (effect o) + (1-(r:ℂ)) • ((rhoN*effect o).trace • J i 1) = _
  rw [J_effect, mean_effect, J_one, effect]
  simp only [smul_smul, ← add_smul]
  congr 1
  simp only [halfCoefficient, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem halfCoefficient_nonnegative {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (i o : Outcome) :
    0 ≤ halfCoefficient r i o := by
  exact div_nonneg (add_nonneg (div_nonneg (mul_nonneg hr (overlap_nonnegative i o))
    (le_of_lt (d_pos i))) (mul_nonneg (sub_nonneg.mpr hr1) (le_of_lt (d_pos o)))) (by norm_num)

theorem halfCoefficient_outer (r : ℝ) (i : Outcome) : ∑ o, halfCoefficient r i o = 1/5 := by
  have h := congrArg Matrix.trace (halfEffect_outer r i)
  simp only [halfEffect_factored, Matrix.trace_sum, Matrix.trace_smul,
    projector_trace, smul_eq_mul, mul_one, effect] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-- All 50,625 chronological weights follow from this single factored identity. -/
theorem kernel_factored (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (i o j k : Outcome) :
    kernel p r hp hp1 hr hr1 (i,o) (j,k) =
      ((halfCoefficient r i o * halfCoefficient r j k *
        (p^2*overlap i j + (1-p^2)*d i*d j) : ℝ) : ℂ) := by
  rw [kernel_trace, halfEffect_factored, halfEffect_factored, Gamma_smul]
  simp only [Phi, Matrix.trace_smul, Gamma_trace, Matrix.trace_mul_comm rhoN (projector i),
    ← d_trace, mul_add, mul_smul_comm, smul_mul_assoc, smul_smul,
    Matrix.trace_add, Matrix.trace_smul, ← overlap_cast]
  push_cast
  simp only [smul_eq_mul]
  ring

theorem rdiag_01 : rdiag 0 * rdiag 1 = Real.sqrt 6 / 6 := by
  change Real.sqrt (1/2) * Real.sqrt (1/3) = _
  calc
    Real.sqrt (1/2) * Real.sqrt (1/3) = Real.sqrt (6/36) := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    _ = Real.sqrt 6 / 6 := by rw [Real.sqrt_div (by norm_num)]; norm_num

theorem rdiag_02 : rdiag 0 * rdiag 2 = Real.sqrt 3 / 6 := by
  change Real.sqrt (1/2) * Real.sqrt (1/6) = _
  calc
    Real.sqrt (1/2) * Real.sqrt (1/6) = Real.sqrt (3/36) := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    _ = Real.sqrt 3 / 6 := by rw [Real.sqrt_div (by norm_num)]; norm_num

theorem rdiag_12 : rdiag 1 * rdiag 2 = Real.sqrt 2 / 6 := by
  change Real.sqrt (1/3) * Real.sqrt (1/6) = _
  calc
    Real.sqrt (1/3) * Real.sqrt (1/6) = Real.sqrt (2/36) := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    _ = Real.sqrt 2 / 6 := by rw [Real.sqrt_div (by norm_num)]; norm_num

def metricWeight : Q → Q → ℝ :=
  !![1/2,Real.sqrt 6/6,Real.sqrt 3/6;
     Real.sqrt 6/6,1/3,Real.sqrt 2/6;
     Real.sqrt 3/6,Real.sqrt 2/6,1/6]

theorem rdiag_product (i j : Q) : rdiag i * rdiag j = metricWeight i j := by
  fin_cases i <;> fin_cases j
  · exact rdiag_square 0
  · exact rdiag_01
  · exact rdiag_02
  · exact (mul_comm (rdiag 1) (rdiag 0)).trans rdiag_01
  · exact rdiag_square 1
  · exact rdiag_12
  · exact (mul_comm (rdiag 2) (rdiag 0)).trans rdiag_02
  · exact (mul_comm (rdiag 2) (rdiag 1)).trans rdiag_12
  · exact rdiag_square 2

theorem form_entries (A B : MatQ) :
    form A B = ∑ i, ∑ j, (metricWeight i j : ℂ) * B i j * star (A i j) := by
  unfold form Matrix.trace
  change (∑ i, (B * R * Aᴴ * R) i i) = _
  simp [R, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← rdiag_product]
  push_cast
  ring

def Z1 : MatQ := !![1,0,0;0,-3/2,0;0,0,0]
def Z2 : MatQ := !![1,0,0;0,1,0;0,0,-5]

/-- Eight centered modes; the identity is the ninth mode. -/
def modeMatrix : Fin 8 → MatQ := ![Z1,Z2,X 0 1,Y 0 1,X 0 2,Y 0 2,X 1 2,Y 1 2]
def modeNorm : Fin 8 → ℝ :=
  ![5/4,5,Real.sqrt 6/3,Real.sqrt 6/3,Real.sqrt 3/3,Real.sqrt 3/3,Real.sqrt 2/3,Real.sqrt 2/3]
def innerMode (a : Fin 8) (u : HalfHistory) : ℂ := frameCoeff (modeMatrix a) u.1

theorem mode_mean_zero (a : Fin 8) : (rhoN * modeMatrix a).trace = 0 := by
  fin_cases a <;>
    simp [modeMatrix, Z1, Z2, X, Y, E, Matrix.single, FiniteThreeLevelThermalPhase.equilibrium,
      DiagonalLindblad.density, three, GibbsReset.threeWeights, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_three, Matrix.cons_val] <;> norm_num

theorem synthesis_innerMode (p r : ℝ) (a : Fin 8) :
    synthesis p r (innerMode a) = (p : ℂ) • modeMatrix a := by
  change synthesis p r (fun u => frameCoeff (modeMatrix a) u.1) = _
  rw [synthesis_inner, frame_right_inverse, Psi, mode_mean_zero]
  simp

theorem form_smul (z w : ℂ) (A B : MatQ) :
    form (z • A) (w • B) = star z * w * form A B := by
  simp [form, Matrix.conjTranspose_smul, Matrix.trace_smul, smul_smul, smul_eq_mul]

private theorem modeMatrix_form_0 (b : Fin 8) :
    form (modeMatrix 0) (modeMatrix b) = if 0=b then (modeNorm 0 : ℂ) else 0 := by
  rw [form_entries]
  fin_cases b <;>
    simp [modeMatrix, modeNorm, metricWeight, Z1, Z2, X, Y, E, Matrix.single,
      Fin.sum_univ_three, Matrix.cons_val]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, map_ofNat, map_inv₀]

private theorem modeMatrix_form_1 (b : Fin 8) :
    form (modeMatrix 1) (modeMatrix b) = if 1=b then (modeNorm 1 : ℂ) else 0 := by
  rw [form_entries]
  fin_cases b <;>
    simp [modeMatrix, modeNorm, metricWeight, Z1, Z2, X, Y, E, Matrix.single,
      Fin.sum_univ_three, Matrix.cons_val]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, map_ofNat, map_inv₀]

private theorem modeMatrix_form_2 (b : Fin 8) :
    form (modeMatrix 2) (modeMatrix b) = if 2=b then (modeNorm 2 : ℂ) else 0 := by
  rw [form_entries]
  fin_cases b <;>
    simp [modeMatrix, modeNorm, metricWeight, Z1, Z2, X, Y, E, Matrix.single,
      Fin.sum_univ_three, Matrix.cons_val]
  all_goals ring

private theorem modeMatrix_form_3 (b : Fin 8) :
    form (modeMatrix 3) (modeMatrix b) = if 3=b then (modeNorm 3 : ℂ) else 0 := by
  rw [form_entries]
  fin_cases b <;>
    simp [modeMatrix, modeNorm, metricWeight, Z1, Z2, X, Y, E, Matrix.single,
      Fin.sum_univ_three, Matrix.cons_val]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, map_ofNat, map_inv₀]

private theorem modeMatrix_form_4 (b : Fin 8) :
    form (modeMatrix 4) (modeMatrix b) = if 4=b then (modeNorm 4 : ℂ) else 0 := by
  rw [form_entries]
  fin_cases b <;>
    simp [modeMatrix, modeNorm, metricWeight, Z1, Z2, X, Y, E, Matrix.single,
      Fin.sum_univ_three, Matrix.cons_val]
  all_goals ring

private theorem modeMatrix_form_5 (b : Fin 8) :
    form (modeMatrix 5) (modeMatrix b) = if 5=b then (modeNorm 5 : ℂ) else 0 := by
  rw [form_entries]
  fin_cases b <;>
    simp [modeMatrix, modeNorm, metricWeight, Z1, Z2, X, Y, E, Matrix.single,
      Fin.sum_univ_three, Matrix.cons_val]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, map_ofNat, map_inv₀]

private theorem modeMatrix_form_6 (b : Fin 8) :
    form (modeMatrix 6) (modeMatrix b) = if 6=b then (modeNorm 6 : ℂ) else 0 := by
  rw [form_entries]
  fin_cases b <;>
    simp [modeMatrix, modeNorm, metricWeight, Z1, Z2, X, Y, E, Matrix.single,
      Fin.sum_univ_three, Matrix.cons_val]
  all_goals ring

private theorem modeMatrix_form_7 (b : Fin 8) :
    form (modeMatrix 7) (modeMatrix b) = if 7=b then (modeNorm 7 : ℂ) else 0 := by
  rw [form_entries]
  fin_cases b <;>
    simp [modeMatrix, modeNorm, metricWeight, Z1, Z2, X, Y, E, Matrix.single,
      Fin.sum_univ_three, Matrix.cons_val]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq, map_ofNat, map_inv₀]

theorem modeMatrix_form (a b : Fin 8) :
    form (modeMatrix a) (modeMatrix b) = if a=b then (modeNorm a : ℂ) else 0 := by
  fin_cases a
  · exact modeMatrix_form_0 b
  · exact modeMatrix_form_1 b
  · exact modeMatrix_form_2 b
  · exact modeMatrix_form_3 b
  · exact modeMatrix_form_4 b
  · exact modeMatrix_form_5 b
  · exact modeMatrix_form_6 b
  · exact modeMatrix_form_7 b

theorem modeNorm_pos (a : Fin 8) : 0 < modeNorm a := by
  fin_cases a <;> simp [modeNorm, Matrix.cons_val]

theorem constant_mode_form (a : Fin 8) : form 1 (modeMatrix a) = 0 := by
  rw [form, Matrix.conjTranspose_one, mul_one, Matrix.mul_assoc, R_square, Matrix.trace_mul_comm]
  exact mode_mean_zero a

theorem modeMatrix_nonzero (a : Fin 8) : modeMatrix a ≠ 0 := by
  intro h
  have he := modeMatrix_form a a
  simp [h, form] at he
  exact (ne_of_gt (modeNorm_pos a)) (by exact_mod_cast he.symm)

section ModeConsumers
open scoped InnerProductSpace
local instance : NormedAddCommGroup MatQ := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance : InnerProductSpace ℂ MatQ := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)

def matrixIsometry (hpos : 0 < p) : Reconstructed p r hp hp1 hr hr1 ≃ₗᵢ[ℂ] MatQ :=
  LinearIsometryEquiv.ofSurjective (embedding p r hp hp1 hr hr1)
    (embedding_surjective p r hp hp1 hr hr1 hpos)

theorem innerMode_pairing (a b : Fin 8) :
    pairing (kernel p r hp hp1 hr hr1) (innerMode a) (innerMode b) =
      if a=b then (modeNorm a : ℂ)*(p : ℂ)^2 else 0 := by
  rw [pairing_synthesis, synthesis_innerMode, synthesis_innerMode, form_smul, modeMatrix_form]
  simp only [Complex.star_def, Complex.conj_ofReal]
  split_ifs <;> ring

theorem innerMode_norm_sq (a : Fin 8) :
    ‖mk (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) (innerMode a)‖^2 =
      modeNorm a * p^2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_mk, innerMode_pairing, if_pos rfl]
  simp [← Complex.ofReal_pow]

theorem constant_innerMode_pairing (a : Fin 8) :
    pairing (kernel p r hp hp1 hr hr1) (fun _ => 1) (innerMode a) = 0 := by
  rw [pairing_synthesis, synthesis_constant, synthesis_innerMode]
  have h := form_smul 1 (p : ℂ) 1 (modeMatrix a)
  simpa [constant_mode_form] using h

theorem reset_modes_null (a : Fin 8) :
    mk (kernel 0 r (by norm_num) (by norm_num) hr hr1)
      (kernel_posSemidef 0 r (by norm_num) (by norm_num) hr hr1) (innerMode a) = 0 := by
  rw [null_iff, synthesis_innerMode]
  simp

theorem centered_mode_survives (hpos : 0 < p) (a : Fin 8) :
    0 < ‖mk (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) (innerMode a)‖^2 := by
  rw [innerMode_norm_sq]
  exact mul_pos (modeNorm_pos a) (sq_pos_of_pos hpos)

end ModeConsumers

/-- All complex matrix entries, including all three imaginary coherences, are retained. -/
theorem matrix_mode_decomposition (A : MatQ) :
    A = (A 0 0/2+A 1 1/3+A 2 2/6) • (1 : MatQ) +
      ((2/5)*(A 0 0-A 1 1)) • Z1 + (A 0 0/10+A 1 1/15-A 2 2/6) • Z2 +
      ((A 0 1+A 1 0)/2) • X 0 1 + (Complex.I*(A 0 1-A 1 0)/2) • Y 0 1 +
      ((A 0 2+A 2 0)/2) • X 0 2 + (Complex.I*(A 0 2-A 2 0)/2) • Y 0 2 +
      ((A 1 2+A 2 1)/2) • X 1 2 + (Complex.I*(A 1 2-A 2 1)/2) • Y 1 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Z1,Z2,X,Y,E,Matrix.single,Matrix.cons_val] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

def nineMode : Fin 9 → HalfHistory → ℂ :=
  ![fun _ => 1,innerMode 0,innerMode 1,innerMode 2,innerMode 3,
    innerMode 4,innerMode 5,innerMode 6,innerMode 7]

theorem nineMode_spans {p : ℝ} (hp : 0 < p) (r : ℝ) (A : MatQ) :
    ∃ c : Fin 9 → ℂ, ∑ i, c i • synthesis p r (nineMode i) = A := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  refine ⟨![A 0 0/2+A 1 1/3+A 2 2/6,
    ((2/5)*(A 0 0-A 1 1))/(p:ℂ), (A 0 0/10+A 1 1/15-A 2 2/6)/(p:ℂ),
    ((A 0 1+A 1 0)/2)/(p:ℂ), (Complex.I*(A 0 1-A 1 0)/2)/(p:ℂ),
    ((A 0 2+A 2 0)/2)/(p:ℂ), (Complex.I*(A 0 2-A 2 0)/2)/(p:ℂ),
    ((A 1 2+A 2 1)/2)/(p:ℂ), (Complex.I*(A 1 2-A 2 1)/2)/(p:ℂ)], ?_⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, nineMode, Matrix.cons_val, Matrix.cons_val_succ, synthesis_constant,
    synthesis_innerMode, smul_smul, div_mul_cancel₀ _ hpC, modeMatrix]
  simpa only [add_assoc] using (matrix_mode_decomposition A).symm

theorem nineMode_span {p : ℝ} (hp : 0 < p) (r : ℝ) :
    Submodule.span ℂ (Set.range (fun i => synthesis p r (nineMode i))) = ⊤ := by
  apply top_unique
  intro A hA
  obtain ⟨c,hc⟩ := nineMode_spans hp r A
  rw [← hc]
  exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))

theorem matrixUnit_from_modes (i j : Q) : (1/2 : ℂ) • (X i j + Complex.I • Y i j) = E i j := by
  ext a b
  simp [X,Y,E,Matrix.single]
  split_ifs <;> ring

theorem matrixUnit_mean {i j : Q} (hij : i ≠ j) : (rhoN * E i j).trace = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [FiniteThreeLevelThermalPhase.equilibrium, DiagonalLindblad.density,
      E, Matrix.single, Matrix.mul_apply, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Matrix.diagonal_apply]

theorem matrixUnit_form (i j : Q) : form (E i j) (E i j) = (metricWeight i j : ℂ) := by
  rw [form_entries]
  fin_cases i <;> fin_cases j <;>
    simp [E,Matrix.single,Fin.sum_univ_three]

theorem metricWeight_sqrt (i j : Q) : metricWeight i j = Real.sqrt (weights i * weights j) := by
  rw [← rdiag_product, rdiag, rdiag, Real.sqrt_mul (weights_nonnegative i)]

def complexProbe (z : ℂ) (i j : Q) (u : HalfHistory) : ℂ := frameCoeff (z • E i j) u.1

theorem synthesis_complexProbe (p r : ℝ) (z : ℂ) {i j : Q} (hij : i ≠ j) :
    synthesis p r (complexProbe z i j) = ((p:ℂ)*z) • E i j := by
  change synthesis p r (fun u => frameCoeff (z • E i j) u.1) = _
  rw [synthesis_inner, frame_right_inverse, Psi_smul, Psi, matrixUnit_mean hij]
  simp only [zero_smul, smul_zero, add_zero, smul_smul]
  congr 1
  ring

theorem complexProbe_pairing (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (z w : ℂ) {i j : Q} (hij : i ≠ j) :
    pairing (kernel p r hp hp1 hr hr1) (complexProbe z i j) (complexProbe w i j) =
      star z * w * (p:ℂ)^2 * (Real.sqrt (weights i * weights j) : ℂ) := by
  rw [pairing_synthesis, synthesis_complexProbe p r z hij,
    synthesis_complexProbe p r w hij, form_smul, matrixUnit_form, metricWeight_sqrt]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem synthesized_commutator (p r : ℝ) :
    synthesis p r (innerMode 2) * synthesis p r (innerMode 3) -
      synthesis p r (innerMode 3) * synthesis p r (innerMode 2) =
      (2*Complex.I*(p:ℂ)^2) • (D 0-D 1) := by
  rw [synthesis_innerMode,synthesis_innerMode]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [modeMatrix,X,Y,D,E,Matrix.single,Matrix.mul_apply,Matrix.cons_val] <;> ring

theorem image_commutator_nonzero {p : ℝ} (hp : 0 < p) (r : ℝ) :
    synthesis p r (innerMode 2) * synthesis p r (innerMode 3) -
      synthesis p r (innerMode 3) * synthesis p r (innerMode 2) ≠ 0 := by
  rw [synthesized_commutator]
  intro h
  have he := congrArg (fun A : MatQ => (A 0 0).im) h
  norm_num [D,E,Matrix.single,Complex.mul_im,Complex.mul_re,pow_two] at he
  nlinarith

theorem old_metric_x : (X 0 1 * rhoN * (X 0 1)ᴴ).trace = 5/6 := by
  simp [X,E,Matrix.single,FiniteThreeLevelThermalPhase.equilibrium,
    DiagonalLindblad.density,three,GibbsReset.threeWeights,Matrix.mul_apply,
    Matrix.trace,Matrix.diag,Fin.sum_univ_three,Matrix.conjTranspose_apply]
  norm_num

theorem actual_metric_mismatch (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (pairing (kernel 1 r (by norm_num) le_rfl hr hr1) (innerMode 2) (innerMode 2)).re <
      (X 0 1 * rhoN * (X 0 1)ᴴ).trace.re := by
  rw [innerMode_pairing, old_metric_x]
  simp [modeNorm,Matrix.cons_val]
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  nlinarith [Real.sqrt_nonneg 6]

/-- The same fifteen effects also admit the distinct Lüders instrument. -/
def ludersScale : ℂ := (Real.sqrt 5 : ℂ)⁻¹
def ludersL (o : Outcome) : MatQ := ludersScale • projector o

theorem ludersScale_real : star ludersScale = ludersScale := by simp [ludersScale]

theorem ludersScale_square : ludersScale * ludersScale = 1/5 := by
  rw [ludersScale, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem ludersL_effect (o : Outcome) : (ludersL o)ᴴ * ludersL o = effect o := by
  simp only [ludersL, Matrix.conjTranspose_smul, projector_adjoint,
    ludersScale_real, smul_mul_smul, ludersScale_square, projector_idempotent]
  rfl

def luders : FiniteInstrument Q 15 where
  count := 1
  operators o _ := ludersL o
  normalized := by simpa only [Fin.sum_univ_one,ludersL_effect] using effect_sum

theorem luders_branch (o : Outcome) (A : MatQ) :
    luders.branch o A = (1/5 : ℂ) • (projector o * A * projector o) := by
  simp only [FiniteInstrument.branch, luders, krausMap,
    ludersL, Matrix.conjTranspose_smul, projector_adjoint, ludersScale_real,
    smul_mul_assoc, mul_smul_comm, smul_smul, ludersScale_square]
  simp

theorem replacement_selected_output : instrument.branch 3 rhoN 0 0 = 1/20 := by
  rw [branch_rhoN]
  simp [Gamma,R,effect,projector,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.cons_val]
  have h := rdiag_square 0
  change rdiag 0 * rdiag 0 = (1/2:ℝ) at h
  have hc := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at hc
  linear_combination (1/10:ℂ)*hc

theorem luders_selected_output : luders.branch 3 rhoN 0 0 = 1/24 := by
  rw [luders_branch,projector_rho_projector,d_values]
  simp [projector,Matrix.cons_val]
  norm_num

theorem selected_output_differs : instrument.branch 3 rhoN ≠ luders.branch 3 rhoN := by
  intro h
  have he := congrArg (fun A : MatQ => A 0 0) h
  rw [replacement_selected_output,luders_selected_output] at he
  norm_num at he

def ludersStep : Step Q Unit 15 := { step 1 (by norm_num) le_rfl with instrument := luders }

theorem ludersStep_branch (o : Outcome) (A : MatQ) :
    ludersStep.branch Q Unit 15 o (GibbsMultilevelReflection.joint A) =
      GibbsMultilevelReflection.joint (luders.branch o A) := by
  change (luders.lift Unit).branch o
    (krausMap (fun k => GibbsMultilevelReflection.joint (channel 1 k))
      (GibbsMultilevelReflection.joint A)) = _
  rw [GibbsMultilevelReflection.joint_kraus,channel_state (by norm_num) le_rfl,Phi_one]
  exact GibbsMultilevelReflection.joint_kraus _ _

def ludersTree : Tree Q Unit 15 2 :=
  .node ludersStep (fun _ => .node ludersStep (fun _ => .done))

def ludersKernel (i j : Outcome) : ℂ :=
  (weight Q Unit 15 ludersTree (i,j,()) (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem luders_run (i j : Outcome) :
    run Q Unit 15 ludersTree (i,j,()) (GibbsMultilevelReflection.joint rhoN) =
      GibbsMultilevelReflection.joint (luders.branch j (luders.branch i rhoN)) := by
  change ludersStep.branch Q Unit 15 j
    (ludersStep.branch Q Unit 15 i (GibbsMultilevelReflection.joint rhoN)) = _
  rw [ludersStep_branch,ludersStep_branch]

theorem luders_forward : ludersKernel 0 3 = 1/100 := by
  unfold ludersKernel weight
  rw [luders_run,GibbsMultilevelReflection.joint_trace,luders_branch,luders_branch,
    projector_rho_projector,d_values]
  simp [projector,Matrix.trace,Matrix.diag,Fin.sum_univ_three,Matrix.cons_val]
  norm_num

theorem luders_reverse : ludersKernel 3 0 = 1/120 := by
  unfold ludersKernel weight
  rw [luders_run,GibbsMultilevelReflection.joint_trace,luders_branch,luders_branch,
    projector_rho_projector,d_values]
  simp [projector,Matrix.trace,Matrix.diag,Fin.sum_univ_three,Matrix.cons_val]
  norm_num

theorem luders_asymmetry : ludersKernel 0 3 - ludersKernel 3 0 = 1/600 := by
  rw [luders_forward,luders_reverse]
  norm_num

theorem luders_not_hermitian : ¬ Matrix.IsHermitian ludersKernel := by
  intro h
  have he := congrArg (fun A : Matrix Outcome Outcome ℂ => A 0 3) h.eq
  simp only [Matrix.conjTranspose_apply,luders_forward,luders_reverse] at he
  norm_num at he

theorem luders_not_posSemidef : ¬ Matrix.PosSemidef ludersKernel :=
  fun h => luders_not_hermitian h.isHermitian

theorem luders_actual_probabilities :
    (∀ h, 0 ≤ weight Q Unit 15 ludersTree h (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h, weight Q Unit 15 ludersTree h (GibbsMultilevelReflection.joint rhoN)) = 1 :=
  normalized_weights Q Unit 15 _ joint_density

theorem rhoN_not_scalar (z : ℂ) : rhoN ≠ z • (1 : MatQ) := by
  intro h
  have h0 := congrArg (fun A : MatQ => A 0 0) h
  have h1 := congrArg (fun A : MatQ => A 1 1) h
  norm_num [FiniteThreeLevelThermalPhase.equilibrium,DiagonalLindblad.density,
    three,GibbsReset.threeWeights] at h0 h1
  have he : (1/2:ℂ) = 1/3 := h0.trans h1.symm
  norm_num at he

def Rinv : MatQ := Matrix.diagonal (fun i => (rdiag i : ℂ)⁻¹)
def Q4inv : MatQ := Matrix.diagonal (fun i => (qdiag i : ℂ)⁻¹)

theorem Rinv_mul : Rinv * R = 1 := by
  rw [Rinv,R,Matrix.diagonal_mul_diagonal]
  have h (i : Q) : (rdiag i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (rdiag_pos i)
  simp [h]

theorem R_mul_inv : R * Rinv = 1 := by
  rw [Rinv,R,Matrix.diagonal_mul_diagonal]
  have h (i : Q) : (rdiag i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (rdiag_pos i)
  simp [h]

theorem Q4inv_mul : Q4inv * Q4 = 1 := by
  rw [Q4inv,Q4,Matrix.diagonal_mul_diagonal]
  have h (i : Q) : (qdiag i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (qdiag_pos i)
  simp [h]

theorem Q4_mul_inv : Q4 * Q4inv = 1 := by
  rw [Q4inv,Q4,Matrix.diagonal_mul_diagonal]
  have h (i : Q) : (qdiag i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (qdiag_pos i)
  simp [h]

/-!
This construction uses the reflection carrier `Fin 3 × Unit` and fifteen outcomes.
Its nine-dimensional complex observable quotient is distinct from a retained
physical `Fin 3 × Fin 3` carrier. The image commutator supplies no coefficientwise
quotient product. Central reset and side reset have the separate ranks proved
above. No arbitrary-depth reflection positivity, continuum reconstruction,
physical clock calibration, or operational trace-norm identification is asserted.
-/
end SKEFTHawking.QuantumNetwork.FiniteThreeLevelPositiveHistory
