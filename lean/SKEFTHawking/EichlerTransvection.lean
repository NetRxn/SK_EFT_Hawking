/-
# Eichler transvections — integral isometries attached to an isotropic vector

For a symmetric integer form `M`, an `M`-isotropic vector `u` and a vector `x ⟂ u` whose
self-product is EVEN (`x ⬝ᵥ M *ᵥ x = 2 * h`), the **Eichler transvection**

  `E(z) = z + (x·z) u − (u·z) x − h (u·z) u`

is an integral isometry of `M` fixing `u`. It is the standard elementary move of unimodular-lattice
theory (Eichler, Kneser, Wall) and the only non-reflection generator the `StableNegRank16` route
needs: unlike a reflection it never divides, so integrality costs only the parity condition on
`x ⬝ᵥ M *ᵥ x`, which is automatic on an EVEN sublattice.

Encoded as an explicit matrix `eichler M u x h = 1 + u(Mx)ᵀ − x(Mu)ᵀ − h·u(Mu)ᵀ` so that it plugs
straight into `IntCongr` (`∃ P, IsUnit P.det ∧ Pᵀ M P = N`). The isometry identity is pure
outer-product algebra: with `p = M *ᵥ u`, `r = M *ᵥ x` and the three scalar side conditions
`u ⬝ᵥ p = 0`, `u ⬝ᵥ r = 0`, `x ⬝ᵥ r = 2h`, every mixed term collapses.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.HyperbolicNormalForm

namespace SKEFTHawking

open Matrix

/-! ### Outer-product toolkit -/

/-- The transpose of an outer product swaps the factors. -/
theorem transpose_vecMulVec {n : ℕ} (a b : Fin n → ℤ) :
    (Matrix.vecMulVec a b)ᵀ = Matrix.vecMulVec b a := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- The product of two outer products contracts through the inner dot product. -/
theorem vecMulVec_mul_vecMulVec {n : ℕ} (a b c d : Fin n → ℤ) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d = (b ⬝ᵥ c) • Matrix.vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dotProduct,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- Right multiplication of an outer product by a SYMMETRIC matrix. -/
theorem vecMulVec_mul_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (hsymm : Mᵀ = M)
    (a b : Fin n → ℤ) : Matrix.vecMulVec a b * M = Matrix.vecMulVec a (M *ᵥ b) := by
  rw [Matrix.vecMulVec_mul, ← Matrix.vecMul_transpose, hsymm]

/-- An outer product applied to a vector is a rescaling. -/
theorem vecMulVec_mulVec {n : ℕ} (a b z : Fin n → ℤ) :
    Matrix.vecMulVec a b *ᵥ z = (b ⬝ᵥ z) • a := by
  ext i
  simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_comm,
    mul_left_comm]

/-! ### The transvection -/

/-- **The Eichler transvection matrix.** `eichler M u x h = 1 + u(Mx)ᵀ − x(Mu)ᵀ − h·u(Mu)ᵀ`, i.e.
`z ↦ z + (x·z)u − (u·z)x − h(u·z)u`. The parameter `h` is *half* the self-product of `x`; passing it
explicitly (rather than dividing) is what keeps the matrix integral. -/
def eichler {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (u x : Fin n → ℤ) (h : ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  1 + Matrix.vecMulVec u (M *ᵥ x) - Matrix.vecMulVec x (M *ᵥ u) - h • Matrix.vecMulVec u (M *ᵥ u)

/-- The action of `eichler` on a vector. -/
theorem eichler_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (u x : Fin n → ℤ) (h : ℤ)
    (z : Fin n → ℤ) :
    eichler M u x h *ᵥ z
      = z + ((M *ᵥ x) ⬝ᵥ z) • u - ((M *ᵥ u) ⬝ᵥ z) • x - (h * ((M *ᵥ u) ⬝ᵥ z)) • u := by
  simp only [eichler, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, vecMulVec_mulVec, smul_smul]

/-- **The Eichler transvection is an isometry.** Requires `M` symmetric, `u` isotropic, `x ⟂ u`,
and `x ⬝ᵥ M *ᵥ x = 2h`. -/
theorem eichler_isometry {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (u x : Fin n → ℤ) (h : ℤ) (huu : u ⬝ᵥ M *ᵥ u = 0) (hux : u ⬝ᵥ M *ᵥ x = 0)
    (hxx : x ⬝ᵥ M *ᵥ x = 2 * h) :
    (eichler M u x h)ᵀ * M * (eichler M u x h) = M := by
  set p := M *ᵥ u with hp
  set r := M *ᵥ x with hr
  have hMsymm : ∀ y : Fin n → ℤ, y ᵥ* M = M *ᵥ y := fun y => by
    rw [← Matrix.vecMul_transpose, hsymm]
  have hup : u ⬝ᵥ p = 0 := huu
  have hur : u ⬝ᵥ r = 0 := hux
  have hxr : x ⬝ᵥ r = 2 * h := hxx
  have hxp : x ⬝ᵥ p = 0 := by
    have hcomm : x ⬝ᵥ M *ᵥ u = u ⬝ᵥ M *ᵥ x := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hsymm, dotProduct_comm]
    rw [hp, hcomm]; exact hux
  have hEt : (eichler M u x h)ᵀ
      = 1 + Matrix.vecMulVec r u - Matrix.vecMulVec p x - h • Matrix.vecMulVec p u := by
    simp only [eichler, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_smul, transpose_vecMulVec, ← hp, ← hr]
  have hME : M * eichler M u x h
      = M + Matrix.vecMulVec p r - Matrix.vecMulVec r p - h • Matrix.vecMulVec p p := by
    simp only [eichler, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_vecMulVec, ← hp, ← hr]
  rw [hEt, Matrix.mul_assoc, hME]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, one_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_smul, vecMulVec_mul_symm hsymm, vecMulVec_mul_vecMulVec,
    ← hp, ← hr, hup, hur, hxr, hxp]
  simp only [zero_smul, smul_zero, sub_zero, add_zero]
  module

/-- **The Eichler transvection is unimodular.** Its determinant is `±1` because it preserves a
nondegenerate form; concretely `(det E)² · det M = det M` and `det M = ±1`. -/
theorem eichler_isUnit_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (u x : Fin n → ℤ) (h : ℤ) (huu : u ⬝ᵥ M *ᵥ u = 0)
    (hux : u ⬝ᵥ M *ᵥ x = 0) (hxx : x ⬝ᵥ M *ᵥ x = 2 * h) :
    IsUnit (eichler M u x h).det := by
  have hiso := eichler_isometry M hsymm u x h huu hux hxx
  have hdet := congrArg Matrix.det hiso
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hMne : M.det ≠ 0 := by rcases hunim with h1 | h1 <;> rw [h1] <;> norm_num
  have hsq : (eichler M u x h).det * (eichler M u x h).det = 1 := by
    have hz : M.det * ((eichler M u x h).det * (eichler M u x h).det - 1) = 0 := by
      linear_combination hdet
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact absurd h1 hMne
    · linarith [h1]
  exact ⟨Units.mkOfMulEqOne _ _ hsq, rfl⟩

/-- **`IntCongr` witness form**: an Eichler transvection exhibits `M ≅ M` by a change of basis that
moves vectors. Packaged for the descent, which needs both the isometry and the unimodularity. -/
theorem eichler_intCongr_self {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hsymm : Mᵀ = M)
    (hunim : IsUnimodular M) (u x : Fin n → ℤ) (h : ℤ) (huu : u ⬝ᵥ M *ᵥ u = 0)
    (hux : u ⬝ᵥ M *ᵥ x = 0) (hxx : x ⬝ᵥ M *ᵥ x = 2 * h) :
    IsUnit (eichler M u x h).det ∧ (eichler M u x h)ᵀ * M * (eichler M u x h) = M :=
  ⟨eichler_isUnit_det M hsymm hunim u x h huu hux hxx,
    eichler_isometry M hsymm u x h huu hux hxx⟩

end SKEFTHawking
