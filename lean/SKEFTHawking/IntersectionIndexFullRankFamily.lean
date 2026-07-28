/-
# The coordinate determinant IS the index — the basis-free form of the unimodularity criterion

`IntersectionDetFullRankFamily.isUnimodular_of_family_index` asks for `det (coordMatrix B h v) = ±p`.
That is correct but nearly unusable as a *geometric* obligation, because `coordMatrix` is taken
against `B.basis` — for the welded `K3` a `Classical.choice` extraction that names no geometry. No
one can hand you the coordinates of the 16 exceptional classes in an anonymous basis.

They can hand you the **index**. Mathlib's `Submodule.natAbs_det_basis_change` says exactly that the
coordinate determinant's absolute value is the order of the quotient, so

    |det (coordMatrix B h v)|  =  Nat.card (H²(X;ℤ) ⧸ span ℤ (range v))

and the criterion becomes: *the family's Gram determinant is `± (index)²`* — a statement about
subgroups and cup products only, with no chosen basis anywhere. For the welded Kummer `K3` this is
the literal classical fact: the 16 exceptional `(−2)`-classes plus the 6 descended `T⁴` classes
generate a subgroup of **index `2⁸`** (the Kummer half-sums are the missing `2⁸`), and
`det (⟨−2⟩¹⁶ ⊕ 3H) = ±2¹⁶ = ±(2⁸)²`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntersectionDetFullRankFamily

namespace SKEFTHawking.IntersectionIndexFullRankFamily

open Matrix
open SKEFTHawking SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.IntersectionDetFullRankFamily (coordMatrix isUnimodular_of_family_index)

variable {X : TopCat}

noncomputable section

/-- **`|det P|` is the index of the subgroup the family generates.** `Module.Basis.span hli` is the
induced basis of `span ℤ (range v)`, and `Submodule.natAbs_det_basis_change` identifies the
change-of-basis determinant with `Nat.card` of the quotient. -/
theorem natAbs_det_coordMatrix_eq_index (B : IntH2Basis X) {n : ℕ} (h : B.rank = n)
    (v : Fin n → Cohomology X 2) (hli : LinearIndependent ℤ v) :
    (coordMatrix B h v).det.natAbs
      = Nat.card (Cohomology X 2 ⧸ Submodule.span ℤ (Set.range v)) := by
  classical
  haveI : Module.Free ℤ (Cohomology X 2) := Module.Free.of_basis B.basis
  haveI : Module.Finite ℤ (Cohomology X 2) := Module.Finite.of_basis B.basis
  have hmain := Submodule.natAbs_det_basis_change (B.basis.reindex (finCongr h))
    (Submodule.span ℤ (Set.range v)) (Module.Basis.span hli)
  have hcomp : (Subtype.val ∘ ⇑(Module.Basis.span hli)) = v := by
    funext i; simp [Module.Basis.span_apply]
  rw [hcomp] at hmain
  rw [← hmain, coordMatrix, Module.Basis.det_apply]

/-- **The index, read back as the two possible determinant values.** The bridge that lets a
basis-free geometric input feed `IntersectionDetFullRankFamily`. -/
theorem det_coordMatrix_eq_of_index (B : IntH2Basis X) {n : ℕ} (h : B.rank = n)
    (v : Fin n → Cohomology X 2) (hli : LinearIndependent ℤ v) {k : ℕ}
    (hcard : Nat.card (Cohomology X 2 ⧸ Submodule.span ℤ (Set.range v)) = k) :
    (coordMatrix B h v).det = (k : ℤ) ∨ (coordMatrix B h v).det = -(k : ℤ) := by
  have hnat := natAbs_det_coordMatrix_eq_index B h v hli
  rw [hcard] at hnat
  exact Int.natAbs_eq_iff.mp hnat

/-- **THE BASIS-FREE UNIMODULARITY CRITERION.** The ambient intersection form is unimodular as soon
as the family's Gram determinant is `±` the square of the index of the subgroup it generates. Every
hypothesis is now a statement about cup products and subgroups — no chosen basis, and no Poincaré
duality on the way in. -/
theorem isUnimodular_of_index_sq (fc : IntFundamentalClass X) (B : IntH2Basis X) {n : ℕ}
    (h : B.rank = n) (v : Fin n → Cohomology X 2) (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : ∀ i j, interFormInt fc (v i) (v j) = G i j) (hli : LinearIndependent ℤ v) {k : ℕ}
    (hk : k ≠ 0) (hcard : Nat.card (Cohomology X 2 ⧸ Submodule.span ℤ (Set.range v)) = k)
    (hGdet : G.det = ((k : ℤ)) ^ 2 ∨ G.det = - ((k : ℤ)) ^ 2) :
    IsUnimodular (Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B)) := by
  have hdet := det_coordMatrix_eq_of_index B h v hli hcard
  have hne : (coordMatrix B h v).det ≠ 0 := by
    have hk' : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk
    rcases hdet with hd | hd <;> rw [hd] <;> simpa using hk'
  have hsq : (coordMatrix B h v).det ^ 2 = ((k : ℤ)) ^ 2 := by
    rcases hdet with hd | hd <;> rw [hd] <;> ring
  refine isUnimodular_of_family_index fc B h v G hG hne ?_
  rcases hGdet with hg | hg
  · exact Or.inl (by rw [hg, hsq])
  · exact Or.inr (by rw [hg, hsq])

end

end SKEFTHawking.IntersectionIndexFullRankFamily
