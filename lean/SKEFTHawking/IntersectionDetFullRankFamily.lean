/-
# The DETERMINANT of the intersection form from a full-rank family and its index

`IntersectionSigFullRankFamily` transports the **signature** from an arbitrary full-rank family `v`
to the basis Gram, and gets away with saying nothing about the index of `span v` — because a
signature is a real invariant and cannot see a finite index. The **determinant** can, and does:

    Gram(v) = Pᵀ · Gram(B) · P      (`gram_family_congr`, already in tree)
      ⟹  det Gram(v) = (det P)² · det Gram(B)

with `P` the coordinate matrix of `v` in the basis `B`. That identity is *present* in the signature
proof — it is how `det P ≠ 0` is extracted — but was never exposed. Exposing it is the point of this
module, because it converts an otherwise very hard obligation into an arithmetic one:

> **`det Gram(B) = ±1` (i.e. the lattice is unimodular, i.e. Poincaré duality) as soon as the family's
> own Gram determinant is `± (det P)²`.**

`|det P|` is exactly the index `[Gram(B)-lattice : span v]`. So a family whose Gram determinant is
`±(index)²` certifies unimodularity of the ambient form — with no Poincaré-duality input anywhere,
which is what makes this route legal under the circularity fence
`k3-gram-must-not-use-pdInput-of-gram`.

## Why this is not a weakening

`isUnimodular_of_family_index` is sharp in both directions: §3's converse shows that if the ambient
form *is* unimodular then `(det P)² = ± det Gram(v)` necessarily. So the index hypothesis is not an
over-ask bolted on to make the argument go through — it is forced, and supplying it is exactly the
missing geometric content. Concretely for the welded Kummer `K3`: the 16 exceptional `(−2)`-classes
plus the 6 descended `T⁴` classes have `det = ±2¹⁶` and span an index-`2⁸` sublattice
(`SETTLED_FORKS: kummer-16-plus-6-geometric-block-is-not-a-basis`), and `2¹⁶ = (2⁸)²` — so those two
facts *together* give unimodularity, while either alone gives nothing.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntersectionSigFullRankFamily

namespace SKEFTHawking.IntersectionDetFullRankFamily

open Matrix
open SKEFTHawking SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.IntersectionSigFullRankFamily (gram_family_congr)
open SKEFTHawking.IntersectionMatrixBasisChange (reindex_interMatrix)

variable {X : TopCat}

noncomputable section

/-- **The coordinate matrix of a family in a rank-`n` `IntH2Basis`.** Its determinant is (up to sign)
the index of `span v` in the lattice `B` spans. -/
def coordMatrix (B : IntH2Basis X) {n : ℕ} (h : B.rank = n) (v : Fin n → Cohomology X 2) :
    Matrix (Fin n) (Fin n) ℤ :=
  (B.basis.reindex (finCongr h)).toMatrix v

/-! ## §1. The determinant identity -/

/-- **`(det P)² · det (interMatrix) = det G`.** The determinant half of `gram_family_congr`, stated
for an arbitrary family with an arbitrary (possibly enormous) index. -/
theorem det_coordMatrix_sq_mul (fc : IntFundamentalClass X) (B : IntH2Basis X) {n : ℕ}
    (h : B.rank = n) (v : Fin n → Cohomology X 2) (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : ∀ i j, interFormInt fc (v i) (v j) = G i j) :
    (coordMatrix B h v).det ^ 2
      * (Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B)).det = G.det := by
  set Br := B.basis.reindex (finCongr h) with hBr
  set P := Br.toMatrix v with hPdef
  set Gb : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => interFormInt fc (Br i) (Br j) with hGb
  have hGram : Pᵀ * Gb * P = G := by
    rw [hGb, hPdef, gram_family_congr fc Br v]
    ext i j
    exact hG i j
  show P.det ^ 2 * (Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B)).det = G.det
  rw [reindex_interMatrix fc B h, ← hGb, ← hGram, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  ring

/-! ## §2. Unimodularity from the family's determinant and its index -/

/-- **THE CRITERION.** If the family's Gram determinant is `± (det P)²` — i.e. `± (index)²` — then the
ambient intersection matrix is **unimodular**.

Nothing about Poincaré duality is used: the whole content is the change-of-basis identity §1 plus
cancellation of the nonzero factor `(det P)²`. This is what makes the route usable to *produce* PD
rather than consume it. -/
theorem isUnimodular_of_family_index (fc : IntFundamentalClass X) (B : IntH2Basis X) {n : ℕ}
    (h : B.rank = n) (v : Fin n → Cohomology X 2) (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : ∀ i j, interFormInt fc (v i) (v j) = G i j)
    (hne : (coordMatrix B h v).det ≠ 0)
    (hsq : G.det = (coordMatrix B h v).det ^ 2 ∨ G.det = - (coordMatrix B h v).det ^ 2) :
    IsUnimodular (Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B)) := by
  have key := det_coordMatrix_sq_mul fc B h v G hG
  have hp2 : (coordMatrix B h v).det ^ 2 ≠ 0 := pow_ne_zero 2 hne
  rcases hsq with hs | hs
  · refine Or.inl (mul_left_cancel₀ hp2 ?_)
    rw [mul_one, key, hs]
  · refine Or.inr (mul_left_cancel₀ hp2 ?_)
    rw [mul_neg_one, key, hs]

/-! ## §3. The criterion is SHARP — a unimodular ambient form FORCES the index relation -/

/-- **The converse.** If the ambient intersection matrix is unimodular then the family's Gram
determinant is `± (det P)²` on the nose. So §2's index hypothesis is not an over-ask invented to make
the proof close; it is exactly equivalent (given nondegeneracy) to what it is used to conclude, and
supplying it is supplying the geometry. -/
theorem det_family_eq_sq_of_isUnimodular (fc : IntFundamentalClass X) (B : IntH2Basis X) {n : ℕ}
    (h : B.rank = n) (v : Fin n → Cohomology X 2) (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : ∀ i j, interFormInt fc (v i) (v j) = G i j)
    (huni : IsUnimodular (Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B))) :
    G.det = (coordMatrix B h v).det ^ 2 ∨ G.det = - (coordMatrix B h v).det ^ 2 := by
  have key := det_coordMatrix_sq_mul fc B h v G hG
  rcases huni with hu | hu
  · exact Or.inl (by rw [← key, hu, mul_one])
  · exact Or.inr (by rw [← key, hu, mul_neg_one])

end

end SKEFTHawking.IntersectionDetFullRankFamily
