/-
# Phase 5q.H · E1 — the DETERMINANT CRITERION for integral Poincaré duality

`IntersectionFormUnimodularInt.interMatrix_isUnit_det_of_intPD` runs one way: integral PD makes the
integer Gram matrix `interMatrix fc B` unimodular. This module proves the **converse**, and therefore
that on any carrier already carrying the `IntH2Basis` datum the two are the SAME statement:

> `Nonempty (IntPoincareDuality fc) ↔ IsUnit (interMatrix fc B).det`   (`nonempty_intPoincareDuality_iff_isUnit_det`)

The mechanism is that `IntPoincareDuality fc` is, by its own two fields, *exactly* the assertion that
the curried intersection form `interFormInt fc : H²(M;ℤ) →ₗ[ℤ] Dual ℤ (H²(M;ℤ))` is an isomorphism —
and `interMatrix fc B` **is** the matrix of that very map in the pair `(B.basis, B.basis.dualBasis)`
(§1, the PD-free half of `interMatrix_eq_toMatrix_intPD`). Mathlib's `LinearEquiv.ofIsUnitDet` then
converts a unit determinant into the equivalence, with `LinearEquiv.ofIsUnitDet_apply` supplying the
`toDualEquiv_apply` field on the nose.

## Why this matters for the ledger (the structural payoff)

A carrier's Gram span has to prove a congruence `IntCongr (reindex (interMatrix fc B)) N` against a
concrete unimodular target `N` (for K3, `SpinSigmaRoute.k3Form`). Congruence preserves the
determinant (`IntCongr.det_eq`, §3), so **that congruence already carries the unimodularity**, hence
already carries integral Poincaré duality. So on any carrier holding an `IntH2Basis`, `pdInput` is
**not an independent residual**: it is implied by the Gram target the same span must establish anyway.

## Headlines (all kernel-pure; no `sorry`/`native_decide`/`maxHeartbeats`/axiom)

* `interMatrix_eq_toMatrix_interFormInt` — the Gram matrix is the matrix of the curried form (no PD input);
* `intPoincareDualityOfIsUnitDet` / `intPoincareDualityOfUnimodular` — PD from one integer determinant;
* `nonempty_intPoincareDuality_iff_isUnit_det` — the biconditional (with the banked forward direction);
* `IntCongr.det_eq`, `IntCongr.isUnimodular_source` — determinant/unimodularity transport along congruence;
* `intPoincareDualityOfIntCongr` — **PD from the Gram span's own `IntCongr … N` target**, `N` unimodular;
* `capBijective_of_capSurjective` — the cap-route input weakens from *bijective* to **surjective**
  (Orzech/Vasconcelos on `H²`, given `H₂ ≃ₗ H²`), so a cap-*spanning* family suffices where
  `IntPDCapOnly.capBijective_of_capDualBasis` demanded a cap-dual *basis*;
* `capSurjective_of_span` — that surjectivity from a family of geometric classes spanning `H₂(M;ℤ)`.
-/
import Mathlib
import SKEFTHawking.IntersectionFormUnimodularInt
import SKEFTHawking.IntersectionMatrixBasisChange
import SKEFTHawking.IntPoincareDualityCapOnly

namespace SKEFTHawking

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt

/-! ## §0. Determinant transport along integer congruence

Stated in the `SKEFTHawking` namespace next to `IntCongr` itself (so `h.det_eq` dot-notation works),
alongside the banked `IntCongr.latticeSig` / `IntCongr.isEvenUnimodular`. -/

/-- **Integer congruence preserves the determinant.** `Pᵀ M P = N` with `det P = ±1` gives
`det N = (det P)² · det M = det M`. The step that lets a *congruence* target (which is what the `hk3`
field of the row asks for, deliberately not a Gram equality) carry unimodularity. -/
theorem IntCongr.det_eq {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ} (h : IntCongr M N) :
    N.det = M.det := by
  obtain ⟨P, hP, hPMP⟩ := h
  have hsq : P.det * P.det = 1 := by
    rcases Int.isUnit_iff.mp hP with hp | hp <;> rw [hp] <;> norm_num
  calc N.det = (P.transpose * M * P).det := by rw [hPMP]
    _ = P.det * M.det * P.det := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    _ = M.det * (P.det * P.det) := by ring
    _ = M.det := by rw [hsq, mul_one]

/-- **Unimodularity transports backwards along a congruence**: if `M` is congruent to an unimodular
`N`, then `M` itself is unimodular. (`IntCongr.isEvenUnimodular` transports forwards; this is the
determinant-only direction, which is the one a Gram *target* delivers.) -/
theorem IntCongr.isUnimodular_source {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ} (h : IntCongr M N)
    (hN : IsUnimodular N) : IsUnimodular M := by
  unfold IsUnimodular at hN ⊢
  rwa [h.det_eq] at hN

namespace IntPDDetCriterion

variable {X : TopCat}

/-! ## §1. The Gram matrix is the matrix of the curried intersection form — with NO PD input -/

/-- **`interMatrix fc B` is the matrix of `interFormInt fc` in the basis/dual-basis pair.** The
PD-free half of `interMatrix_eq_toMatrix_intPD`: that theorem computes the matrix of the *PD
equivalence*, using `toDualEquiv_apply` to replace it by the form; here the map IS the curried form
`interFormInt fc : H²(M;ℤ) →ₗ[ℤ] Dual ℤ (H²(M;ℤ))` (note `Module.Dual ℤ V = V →ₗ[ℤ] ℤ`, so no
repackaging is needed), so no duality datum is consumed. The transpose that `toMatrix` introduces is
absorbed by symmetry of the form (`interFormInt_symm`). -/
theorem interMatrix_eq_toMatrix_interFormInt (fc : IntFundamentalClass X) (B : IntH2Basis X) :
    interMatrix fc B = (LinearMap.toMatrix B.basis B.basis.dualBasis) (interFormInt fc) := by
  ext i j
  rw [LinearMap.toMatrix_apply, interMatrix_apply, Module.Basis.dualBasis_repr, interFormInt_symm]

/-! ## §2. Integral Poincaré duality from ONE integer determinant -/

/-- **INTEGRAL POINCARÉ DUALITY FROM A UNIT GRAM DETERMINANT.** Given the `IntH2Basis` datum (a finite
free ℤ-basis of `H²(M;ℤ)`, which every carrier in this arc already holds) and the single integer fact
`IsUnit (interMatrix fc B).det`, the disclosed `IntPoincareDuality fc` datum is INHABITED.

`toDualEquiv` is `LinearEquiv.ofIsUnitDet` applied to the curried intersection form through §1, so its
underlying map is `interFormInt fc` definitionally-after-`ofIsUnitDet_apply` — which is exactly what
the `toDualEquiv_apply` field demands. This is the converse of
`interMatrix_isUnit_det_of_intPD`, and it is what makes `pdInput` derivable from a Gram computation. -/
noncomputable def intPoincareDualityOfIsUnitDet (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (h : IsUnit (interMatrix fc B).det) : IntPoincareDuality fc where
  toDualEquiv :=
    LinearEquiv.ofIsUnitDet (f := interFormInt fc) (v := B.basis) (v' := B.basis.dualBasis)
      (by rwa [← interMatrix_eq_toMatrix_interFormInt])
  toDualEquiv_apply _ _ := by rw [LinearEquiv.ofIsUnitDet_apply]

/-- **PD from an UNIMODULAR Gram matrix** (`AlgebraicRokhlin.IsUnimodular`, `det = ±1`) — the shape the
lattice leg speaks. Same content as `intPoincareDualityOfIsUnitDet` with `Int.isUnit_iff` applied. -/
noncomputable def intPoincareDualityOfUnimodular (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (h : IsUnimodular (interMatrix fc B)) : IntPoincareDuality fc :=
  intPoincareDualityOfIsUnitDet fc B (Int.isUnit_iff.mpr h)

/-- **THE BICONDITIONAL: integral PD ⟺ the integer Gram determinant is a unit.** Forward is the banked
`interMatrix_isUnit_det_of_intPD`; backward is §2. So — for any carrier already carrying an
`IntH2Basis` — the disclosed `IntPoincareDuality` datum contains **exactly** the information "the
intersection matrix is unimodular", no more and no less. In particular the statement is independent of
*which* basis `B` is used (both sides are, the left visibly and the right by
`IntersectionMatrixBasisChange.interMatrix_intCongr_of_rank_eq` + `IntCongr.det_eq`). -/
theorem nonempty_intPoincareDuality_iff_isUnit_det (fc : IntFundamentalClass X) (B : IntH2Basis X) :
    Nonempty (IntPoincareDuality fc) ↔ IsUnit (interMatrix fc B).det :=
  ⟨fun ⟨PD⟩ => interMatrix_isUnit_det_of_intPD fc B PD,
    fun h => ⟨intPoincareDualityOfIsUnitDet fc B h⟩⟩

/-! ## §3. Transport along `IntCongr` — PD from the Gram span's own congruence target -/

/-- **INTEGRAL POINCARÉ DUALITY FROM THE GRAM SPAN'S OWN TARGET.** The `hk3`-shaped hypothesis — the
reindexed Gram matrix of `B` is `IntCongr` to a *concrete unimodular* form `N` — already implies the
`IntPoincareDuality` datum for the same fundamental class.

Reindexing along a bijection of index types does not change the determinant
(`Matrix.det_reindex_self`), and congruence does not change it either (§3), so `N` unimodular forces
`interMatrix fc B` unimodular, and §2 converts that into PD. **Consequence for every carrier in this
arc: `pdInput` is not an independent residual — it is a corollary of the Gram congruence.** -/
noncomputable def intPoincareDualityOfIntCongr (fc : IntFundamentalClass X) (B : IntH2Basis X)
    {n : ℕ} (hrank : B.rank = n) {N : Matrix (Fin n) (Fin n) ℤ} (hN : IsUnimodular N)
    (hcong : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank) (interMatrix fc B)) N) :
    IntPoincareDuality fc := by
  refine intPoincareDualityOfUnimodular fc B ?_
  have h1 : IsUnimodular (Matrix.reindex (finCongr hrank) (finCongr hrank) (interMatrix fc B)) :=
    hcong.isUnimodular_source hN
  unfold IsUnimodular at h1 ⊢
  rwa [Matrix.det_reindex_self] at h1

/-! ## §4. The cap route's input weakens from BIJECTIVE to SURJECTIVE

`IntPDCapOnly.capBijective_of_capDualBasis` asks the geometric classes `c i = B i ⌢ [M]` to form a
BASIS of `H₂(M;ℤ)`. On a carrier where `H₂(M;ℤ)` and `H²(M;ℤ)` are abstractly isomorphic — which the
UCT already delivers wherever `H₁(M;ℤ)` is free and `H₂(M;ℤ)` is finite free — mere **spanning**
suffices: a surjective endomorphism of a Noetherian module is injective (Orzech/Vasconcelos), the same
mechanism `IntPDCapOnly.kroneckerHInt2_injective_of_capBijective` uses on the Kronecker map. -/

/-- **A surjective cap map is bijective**, given an abstract isomorphism `H₂(M;ℤ) ≃ₗ H²(M;ℤ)` and
`H²(M;ℤ)` finite (hence Noetherian over ℤ). Conjugating `capMapLin zM : H² → H₂` by `e` gives a
surjective ENDOmorphism of `H²`, which `IsNoetherian.injective_of_surjective_endomorphism` makes
injective; injectivity of the cap follows since `e` is injective. -/
theorem capBijective_of_capSurjective {zM : Homology X 4} [Module.Finite ℤ (Cohomology X 2)]
    (e : Homology X 2 ≃ₗ[ℤ] Cohomology X 2) (hsurj : Function.Surjective (capMapLin zM)) :
    Function.Bijective (capMapLin zM) := by
  classical
  haveI : IsNoetherian ℤ (Cohomology X 2) := inferInstance
  set f : Cohomology X 2 →ₗ[ℤ] Cohomology X 2 := e.toLinearMap.comp (capMapLin zM) with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := hsurj (e.symm y)
    exact ⟨w, by simp [hf, hw]⟩
  have hfi : Function.Injective f := IsNoetherian.injective_of_surjective_endomorphism f hfs
  refine ⟨fun a b hab => hfi ?_, hsurj⟩
  simp only [hf, LinearMap.comp_apply, hab]

/-- **The cap is surjective once the caps of a family of cohomology classes SPAN `H₂(M;ℤ)`.** The
usable geometric shape: exhibit classes `a i ∈ H²(M;ℤ)` whose cap-images generate the integral
homology lattice — no basis-hood, no rank bookkeeping. -/
theorem capSurjective_of_span {zM : Homology X 4} {ι : Type*} (a : ι → Cohomology X 2)
    (hspan : Submodule.span ℤ (Set.range fun i => capHInt 2 1 (a i) zM) = ⊤) :
    Function.Surjective (capMapLin zM) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← hspan]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨a i, rfl⟩

/-- **Integral Poincaré duality from a cap-SPANNING family** — the packaged §4 route: geometric
cohomology classes whose caps generate `H₂(M;ℤ)`, plus the abstract `H₂ ≃ₗ H²` the UCT supplies,
deliver the whole `IntPoincareDuality` datum. Strictly weaker input than
`IntPDCapOnly.intPoincareDualityOfCapDualBasis` (which needs the cap-images to be a basis). -/
noncomputable def intPoincareDualityOfCapSpan {zM : Homology X 4} {ι : Type*}
    [Module.Free ℤ (Homology X 2)] [Module.Finite ℤ (Homology X 2)]
    [Module.Finite ℤ (Cohomology X 2)] [Module.Projective ℤ (boundaries X 1)]
    (e : Homology X 2 ≃ₗ[ℤ] Cohomology X 2) (a : ι → Cohomology X 2)
    (hspan : Submodule.span ℤ (Set.range fun i => capHInt 2 1 (a i) zM) = ⊤) :
    IntPoincareDuality (intFundamentalClassOfHomology zM) :=
  IntPDCapOnly.intPoincareDualityOfCapBijective
    (capBijective_of_capSurjective e (capSurjective_of_span a hspan))

end IntPDDetCriterion

end SKEFTHawking
