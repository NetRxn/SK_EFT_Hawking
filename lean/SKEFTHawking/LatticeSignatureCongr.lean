/-
Phase 5q.B: congruence-invariance of `latticeSig`, and the signature of the hyperbolic plane `σ(H) = 0`.

This module supplies the *Sylvester invariance* that the classification route to van der Blij needs: the
signature of an integer symmetric form is unchanged under integer congruence `M ↦ Pᵀ · M · P` with
`P ∈ GL(ℤ)` (i.e. `IsUnit P.det`). This is exactly what lets us read the signature off a normal form: once
the classification gives `M ≅ E₈^a ⊕ (−E₈)^b ⊕ H^c`, congruence-invariance + additivity
(`SignatureAdditivity.lean`) + the generator signatures (`E8Signature.lean`, and `σ(H) = 0` here) compute
`σ(M) = 8(a − b)`, manifestly divisible by 8.

The proof chain, all kernel-pure:
* `toQuadraticMap'_congr` — `(Bᵀ · A · B).toQuadraticMap' = A.toQuadraticMap'.comp (mulVecLin B)`, the
  matrix-level statement that congruence is precomposition by `B`. Evaluating: `xᵀ (Bᵀ A B) x = (Bx)ᵀ A (Bx)`.
* `latticeSig_congr` — for `P` invertible, the cast of `B = P` gives a linear equivalence, so the two real
  forms are `QuadraticMap.Equivalent`; Mathlib's `Equivalent.sigPos_eq`/`sigNeg_eq` (Sylvester's law of
  inertia) then give `latticeSig (PᵀMP) = latticeSig M`.
* `hyp_latticeSig` — `σ(H) = 0` for the hyperbolic plane `H = [[0,1],[1,0]]`, because `H` is congruent to
  `−H` (via `P = diag(1,−1)`), forcing `σ(H) = −σ(H) = 0`.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.LatticeSignature

namespace SKEFTHawking

open Matrix QuadraticForm QuadraticMap

/-! ## Matrix congruence as precomposition, and `latticeSig` congruence-invariance -/

/-- **Congruence at the form level:** `(Bᵀ · A · B).toQuadraticMap' = A.toQuadraticMap'.comp (mulVecLin B)`.
Evaluating, `xᵀ (Bᵀ A B) x = (Bx)ᵀ A (Bx)`. -/
theorem toQuadraticMap'_congr {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (Bᵀ * A * B).toQuadraticMap' = A.toQuadraticMap'.comp (Matrix.mulVecLin B) := by
  ext x
  simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', QuadraticMap.comp_apply, Matrix.mulVecLin_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- **Congruence-invariance of `latticeSig`** (Sylvester's law of inertia): for `P ∈ GL(ℤ)`
(`IsUnit P.det`), `latticeSig (Pᵀ · M · P) = latticeSig M`. The cast of `P` is invertible over ℝ, so its
`mulVecLin` is a linear equivalence and `(Pᵀ M P)`'s real form is `QuadraticMap.Equivalent` to `M`'s. -/
theorem latticeSig_congr {n : ℕ} (M P : Matrix (Fin n) (Fin n) ℤ) (hP : IsUnit P.det) :
    latticeSig (Pᵀ * M * P) = latticeSig M := by
  set Mr := M.map (Int.cast : ℤ → ℝ) with hMr
  set Pr := P.map (Int.cast : ℤ → ℝ) with hPr
  have hmap : ((Pᵀ * M * P).map (Int.cast : ℤ → ℝ)) = Prᵀ * Mr * Pr := by
    rw [hMr, hPr, show (Int.cast : ℤ → ℝ) = ⇑(Int.castRingHom ℝ) from rfl,
      Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hPrdet : IsUnit Pr.det := by
    rw [hPr, ← Int.cast_det]; exact (Int.castRingHom ℝ).isUnit_map hP
  letI : Invertible Pr := Matrix.invertibleOfIsUnitDet Pr hPrdet
  have hcoe : (↑(Pr.toLinearEquiv' inferInstance) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      = Matrix.mulVecLin Pr := by rw [Matrix.toLinearEquiv'_apply]; rfl
  have hequiv : QuadraticMap.Equivalent Mr.toQuadraticMap' (Prᵀ * Mr * Pr).toQuadraticMap' := by
    refine ⟨?_⟩
    have h := QuadraticMap.isometryEquivOfCompLinearEquiv Mr.toQuadraticMap'
      (Pr.toLinearEquiv' inferInstance)
    rwa [hcoe, ← toQuadraticMap'_congr] at h
  unfold latticeSig
  rw [hmap, ← hequiv.sigPos_eq, ← hequiv.sigNeg_eq]

/-! ## The hyperbolic plane `H` and `σ(H) = 0` -/

/-- The **hyperbolic plane** `H = [[0,1],[1,0]]` — the rank-2 even unimodular indefinite form, the third
generator (with `E₈`, `−E₈`) of the classification of even unimodular lattices. -/
def Hyp : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- `Hyp` is symmetric. -/
theorem hyp_symm : Hypᵀ = Hyp := by decide

/-- `Hyp` is even (zero diagonal). -/
theorem hyp_even : ∀ i, 2 ∣ Hyp i i := by decide

/-- `Hyp` is unimodular (`det = −1`). -/
theorem hyp_unimodular : IsUnimodular Hyp := Or.inr (by decide)

/-- The flip `P = diag(1,−1)` realizing the congruence `H ≅ −H`. -/
private def Pflip : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- **`σ(H) = 0`.** The hyperbolic plane is congruent to its own negative (`Pflipᵀ · H · Pflip = −H` with
`Pflip = diag(1,−1)` invertible), so `σ(H) = σ(−H) = −σ(H)`, forcing `σ(H) = 0`. -/
theorem hyp_latticeSig : latticeSig Hyp = 0 := by
  have hcong : latticeSig (Pflipᵀ * Hyp * Pflip) = latticeSig Hyp :=
    latticeSig_congr Hyp Pflip (by rw [show Pflip.det = -1 from by decide]; exact isUnit_one.neg)
  rw [show Pflipᵀ * Hyp * Pflip = -Hyp from by decide, latticeSig_neg] at hcong
  omega

end SKEFTHawking
