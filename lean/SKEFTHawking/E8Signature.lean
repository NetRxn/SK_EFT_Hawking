/-
Phase 5q.B: the signature of E₈ is `+8` (and of `−E₈` is `−8`), kernel-pure.

This is sub-step [A1] of the FULL (zero-axiom, zero-citation) discharge of van der Blij's
`IsEvenUnimodular M → 8 ∣ latticeSig M` via the classification of even unimodular lattices
(`E₈^a ⊕ (−E₈)^b ⊕ H^c`). The generators' signatures are the numerical anchors of that classification:
`σ(E₈) = 8`, `σ(−E₈) = −8`, `σ(H) = 0`. This module nails the first two.

THE OBSTRUCTION AND HOW WE ROUTE AROUND IT. The signature is *analytic* (a count of eigenvalue signs),
so proving `σ(E₈) = 8` means proving `E₈` is positive definite over ℝ. The textbook certificate is an
LDLᵀ decomposition with positive pivots, but its pivots are rational (`D = diag(2,2,3/2,5/6,4/5,3/4,
2/3,1/2)`), and kernel `decide` does **not** reduce ℚ matrix identities (Rat normalisation gets stuck),
while an entrywise `norm_num` over the 64 entries blows the heartbeat budget.

The trick: `2·E₈` embeds in `ℤ⁸` (the E₈ root lattice has a half-integer basis, so twice the basis is
integral). Concretely there is an **integer** matrix `C8` — its columns are `2 ×` the E₈ simple roots,
ordered to match `E8lit` — with `C8ᵀ · C8 = 4 · E8lit`. That identity is a product of small integers, so
`decide` reduces it cleanly over ℤ. Casting to ℝ, `C8rᴴ · C8r = 4 · E8r`, and since `C8` is invertible
(`det(C8)² = det(C8ᵀ·C8) = det(4·E8lit) = 4⁸ · (±1) ≠ 0`, dodging the infeasible 8×8 determinant),
`Matrix.PosDef.conjTranspose_mul_self` gives `(4·E8r).PosDef`; stripping the positive scalar `4` gives
`E8r.PosDef`. Then `latticeSig_of_posDef` reads off `σ(E₈) = 8`.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom. Builds on `E8Literal.lean` (kernel-pure even-unimodular E₈) and
`LatticeSignature.lean` (`latticeSig`, `latticeSig_of_posDef`).
-/

import Mathlib
import SKEFTHawking.E8Literal
import SKEFTHawking.LatticeSignature

namespace SKEFTHawking

open Matrix

/-- The integer matrix whose columns are `2 ×` the E₈ simple roots (Bourbaki even-coordinate model,
ordered to match `E8lit`). Its defining property is `C8ᵀ · C8 = 4 · E8lit` (`c8_eq`). -/
def C8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 2, -2, 0, 0, 0, 0, 0;
     -1, 2, 2, -2, 0, 0, 0, 0;
     -1, 0, 0, 2, -2, 0, 0, 0;
     -1, 0, 0, 0, 2, -2, 0, 0;
     -1, 0, 0, 0, 0, 2, -2, 0;
     -1, 0, 0, 0, 0, 0, 2, -2;
     -1, 0, 0, 0, 0, 0, 0, 2;
     1, 0, 0, 0, 0, 0, 0, 0]

/-- **The integral Gram identity** `C8ᵀ · C8 = 4 · E8lit`, proven by `decide` (small integer
multiplications — kernel-pure, native_decide-free). This is the certificate that `4 · E8lit` is the Gram
matrix of the integer vectors `2 × (E₈ roots)`, hence positive (semi)definite. -/
theorem c8_eq : C8ᵀ * C8 = (4 : ℤ) • E8lit := by decide

/-- `E8lit` cast to a real matrix. -/
noncomputable def E8r : Matrix (Fin 8) (Fin 8) ℝ := E8lit.map (Int.cast : ℤ → ℝ)

/-- `C8` cast to a real matrix. -/
noncomputable def C8r : Matrix (Fin 8) (Fin 8) ℝ := C8.map (Int.cast : ℤ → ℝ)

/-- The real Gram identity `C8rᴴ · C8r = 4 · E8r`, transported from the integral `c8_eq` along the
cast ring homomorphism `ℤ → ℝ` (over ℝ the conjugate transpose is the transpose). -/
theorem c8r_eq : C8rᴴ * C8r = (4 : ℝ) • E8r := by
  have key := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℤ => M.map (Int.castRingHom ℝ)) c8_eq
  dsimp only at key
  rw [Matrix.map_mul, Matrix.transpose_map] at key
  simp only [Int.coe_castRingHom] at key
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  unfold C8r E8r
  rw [key]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **E₈ is positive definite over ℝ.** From `C8rᴴ · C8r = 4 · E8r` with `C8r` invertible
(`det(C8r)² = det(4·E8r) = 4⁸ · det(E8r)`, and `det(E8r) = ±1 ≠ 0` by unimodularity — no 8×8 determinant
is ever evaluated), `Matrix.PosDef.conjTranspose_mul_self` gives `(4·E8r).PosDef`, and dividing by the
positive scalar `4` gives `E8r.PosDef`. -/
theorem e8r_posDef : E8r.PosDef := by
  have hE8det : E8r.det ≠ 0 := by
    have hd : E8r.det = ((E8lit.det : ℤ) : ℝ) := by rw [E8r, ← Int.cast_det]
    rcases e8lit_unimodular with h | h <;> rw [hd, h] <;> norm_num
  have hdet : IsUnit C8r.det := by
    rw [isUnit_iff_ne_zero]
    intro hzero
    have h2 : (C8rᴴ * C8r).det = 0 := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose, hzero]; ring
    rw [c8r_eq, Matrix.det_smul] at h2
    simp only [Fintype.card_fin] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact hE8det h
  have hUnit : IsUnit C8r := (Matrix.isUnit_iff_isUnit_det C8r).mpr hdet
  have hpd : ((4 : ℝ) • E8r).PosDef := by
    rw [← c8r_eq]
    exact Matrix.PosDef.conjTranspose_mul_self C8r (Matrix.mulVec_injective_of_isUnit hUnit)
  have hfin := hpd.smul (a := (1 / 4 : ℝ)) (by norm_num)
  rwa [smul_smul, (by norm_num : (1 / 4 : ℝ) * 4 = 1), one_smul] at hfin

/-- **`σ(E₈) = 8`** — the positive inertia index of E₈ is its full rank, since E₈ is positive definite. -/
theorem e8lit_latticeSig : latticeSig E8lit = 8 := by
  have h := latticeSig_of_posDef E8lit e8r_posDef
  simpa using h

/-- **`σ(−E₈) = −8`** — orientation reversal of `σ(E₈) = 8`. -/
theorem neg_e8lit_latticeSig : latticeSig (-E8lit) = -8 := by
  rw [latticeSig_neg, e8lit_latticeSig]

end SKEFTHawking
