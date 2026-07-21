/-
# Phase 5q.H — K10 span 3: the intersection matrix is **basis-independent up to `IntCongr`**

The `hk3` field of `PinPlusKTSpinSigmaStock.K3RealizingElement` asks for
`IntCongr (reindex (interMatrix (a.fc g) (a.B g))) k3Form` — a **congruence**, deliberately not a
literal Gram equality (`SETTLED_FORKS`: "Gram atoms: a literal matrix EQUALITY is the wrong target";
`SphereProdGramPinRetire.sphereProdGramPin_iff` is the cautionary computation).

This module proves the structural fact that makes that choice pay off:

> for a FIXED fundamental class, the Gram matrices of **any two** bases of `H²(X;ℤ)` of the same
> rank are integrally congruent (`interMatrix_intCongr_of_rank_eq`).

Consequences that unblock the Kummer-K3 → row bridge:

* **The arbitrary basis is harmless.** `KummerK3E1Package.kummerK3IntH2Basis` is extracted from the
  `Nonempty` of `kummerK3_b2_target_unconditional` by `Classical.choice`, so it is *a* rank-22 basis
  and emphatically not the geometric 3H ⊕ 2(−E₈) system. `hk3_of_other_basis` shows this costs
  nothing: the K3-lattice congruence proved on ANY rank-22 basis transfers to it verbatim.
* **The Gram span may pick its own coordinates.** The remaining geometric work (the 16 exceptional
  `(−2)`-spheres' Gram block, the Q-side `3H` block descended from
  `KummerT4GramCross.interMatrix_t4_intCongr_torusFourForm`, and the cross terms) can be executed on
  whatever basis makes the cup products computable, then transferred.

The bilinear-algebra core is the already-banked `SphereProdBasisIdInt.gram_congr_of_basis_change`
(`Gram C = Pᵀ (Gram B) P` for `Cⱼ = Σᵢ Pᵢⱼ Bᵢ`); what is new here is the unimodularity of the
change-of-basis matrix between two genuine bases, and the `IntH2Basis`/`reindex` packaging that the
`hk3` field's exact shape demands.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdBasisIdInt
import SKEFTHawking.SpinSigmaGenerator

namespace SKEFTHawking.IntersectionMatrixBasisChange

open SKEFTHawking SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SphereProdBasisIdInt (gram_congr_of_basis_change)

variable {X : TopCat}

/-! ## §1. The change-of-basis matrix between two bases is unimodular -/

/-- **`B.toMatrix C` is unimodular** when both `B` and `C` are bases: its inverse is `C.toMatrix B`
(`Basis.toMatrix_mul_toMatrix_flip`), so the determinants multiply to `1`. The integrality input the
`IntCongr` witness needs. -/
theorem isUnit_det_toMatrix {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [AddCommGroup M] [Module R M] (B C : Module.Basis ι R M) :
    IsUnit (B.toMatrix C).det :=
  Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip B C)

/-! ## §2. The Gram matrices of two bases are integrally congruent -/

/-- **Two bases of `H²(X;ℤ)` give integrally congruent Gram matrices** (fixed fundamental class).
The congruence matrix is the change of basis `B.toMatrix C`, unimodular by §1; the conjugation
identity is the banked bilinear-algebra core. This is the precise sense in which "the intersection
form" is a well-defined lattice: only its `IntCongr` class is, never its matrix. -/
theorem gram_intCongr_of_bases (fc : IntFundamentalClass X) {n : ℕ}
    (B C : Module.Basis (Fin n) ℤ (Cohomology X 2)) :
    IntCongr (Matrix.of fun i j => interFormInt fc (B i) (B j))
      (Matrix.of fun i j => interFormInt fc (C i) (C j)) :=
  ⟨B.toMatrix C, isUnit_det_toMatrix B C,
    gram_congr_of_basis_change (interFormInt fc) B C (B.toMatrix C)
      (fun j => (B.sum_repr (C j)).symm)⟩

/-- **The reindexed `interMatrix` is the Gram matrix of the reindexed basis** — the bookkeeping that
lets §2 be applied at the `hk3` field's exact spelling (`Matrix.reindex (finCongr h) (finCongr h)`).
-/
theorem reindex_interMatrix (fc : IntFundamentalClass X) (B : IntH2Basis X) {n : ℕ}
    (h : B.rank = n) :
    Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B)
      = Matrix.of fun i j => interFormInt fc (B.basis.reindex (finCongr h) i)
          (B.basis.reindex (finCongr h) j) := by
  ext i j
  simp [Matrix.reindex_apply, interMatrix, Module.Basis.reindex_apply]

/-- **THE BASIS-INDEPENDENCE THEOREM.** For a fixed fundamental class, any two `IntH2Basis` data of
the same rank `n` have integrally congruent intersection matrices, at the `reindex`-normalised
spelling the row's `hk3` field uses. So `hk3` is a property of the *manifold plus orientation*, not
of the chosen basis — which is exactly why the row asks for `IntCongr` and not a Gram equality. -/
theorem interMatrix_intCongr_of_rank_eq (fc : IntFundamentalClass X) (B C : IntH2Basis X) {n : ℕ}
    (hB : B.rank = n) (hC : C.rank = n) :
    IntCongr (Matrix.reindex (finCongr hB) (finCongr hB) (interMatrix fc B))
      (Matrix.reindex (finCongr hC) (finCongr hC) (interMatrix fc C)) := by
  rw [reindex_interMatrix fc B hB, reindex_interMatrix fc C hC]
  exact gram_intCongr_of_bases fc _ _

/-! ## §3. The consumer form: transferring the K3-lattice congruence between bases -/

/-- **The `hk3` obligation transfers between rank-22 bases.** If the K3 lattice congruence
`IntCongr (…) k3Form` is proved on SOME rank-22 basis `C` of `H²(X;ℤ)`, it holds on EVERY rank-22
basis `B` — in particular on the `Classical.choice`-extracted
`KummerK3E1Package.kummerK3IntH2Basis`, which is otherwise geometrically anonymous.

This is the bridge that lets the Gram span be executed in geometric coordinates (the 16 exceptional
`(−2)`-sphere classes and the six descended `T⁴` classes) and then be consumed by the packaged
element without any basis-normalisation obligation. -/
theorem hk3_of_other_basis (fc : IntFundamentalClass X) (B C : IntH2Basis X)
    (hB : B.rank = 22) (hC : C.rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hC) (finCongr hC) (interMatrix fc C))
      SKEFTHawking.SpinSigmaRoute.k3Form) :
    IntCongr (Matrix.reindex (finCongr hB) (finCongr hB) (interMatrix fc B))
      SKEFTHawking.SpinSigmaRoute.k3Form :=
  (interMatrix_intCongr_of_rank_eq fc B C hB hC).trans hk3

end SKEFTHawking.IntersectionMatrixBasisChange
