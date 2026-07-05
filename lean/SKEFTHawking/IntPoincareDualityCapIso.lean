/-
# Phase 5q.H · E1 — the integral cap-iso `IntCapIso` reduced to a CONCRETE determinant datum, plus
# the mod-2 shadow (`nondeg_of_closed`) partial on the cap.

Substrate-G foundation brick (Option-A from-scratch). Sharpens the reduction of `IntPoincareDuality`
one step further. Brick 9 (`IntCapProductInt`) reduced `IntPoincareDuality` to `IntCapIso zM` — the two
geometric equivalences (i) the integral cap `·⌢[M] : H²(M;ℤ) ≃ H₂(M;ℤ)` and (ii) the integral Kronecker
`H₂(M;ℤ) ≃ Dual ℤ (H²(M;ℤ))`. Those two fields were carried as ABSTRACT `≃ₗ[ℤ]` equivalences plus their
`_apply` compatibilities — the community-scale integral-PD core, but disclosed as abstract isos.

This module replaces those abstract isos with a **concrete, checkable determinant datum** `IntCapIsoData`:

* the *linear maps* themselves are BUILT from existing infrastructure, not disclosed —
  `capMapLin := capHInt 2 1 · zM` and `kronMapLin := (kroneckerHInt 2).flip`;
* the only disclosed inputs become (a) a finite free basis of `H₂(M;ℤ)` (the homology-side analogue of the
  already-disclosed `IntH2Basis` on `H²`), and (b) TWO integer determinants being units:
  `IsUnit (det (matrix of capMapLin))` and `IsUnit (det (matrix of kronMapLin))`.

Mathlib bridge: `LinearEquiv.ofIsUnitDet` (`f : M →ₗ M'` with `IsUnit ((toMatrix v v') f).det` is a
`≃ₗ` whose underlying map is `f`, `LinearEquiv.ofIsUnitDet_apply`). So `IntCapIsoData → IntCapIso` is a
genuine reduction: the abstract-iso fields collapse to two unimodular-determinant facts on concretely-built
maps — the exact integer analogue of the `IntH2Basis`+`interMatrix` datum on the H² side.

The mod-2 shadow: the on-main `SingularPD4Instances.nondeg_of_closed` gives INJECTIVITY of the mod-2 cap
`·⌢[M]₂`. Over ℤ, `det (matrix of capMapLin)` is therefore ODD (its mod-2 reduction is the determinant of an
injective — hence, for a square matrix over the field `ZMod 2`, invertible — matrix). This ODD-determinant
partial is strictly weaker than `IsUnit det` (= `±1`), and is exactly the honest partial the (A) integral-PD
core admits from the mod-2 shadow: `nondeg_of_closed` gives `det ≢ 0 mod 2`, NOT `det = ±1`. Carrying the
full `IsUnit det` is the residual community-scale geometric input (the local-global integral PD = MV +
Euclidean local cap-iso), cleanly isolated as ONE integer-determinant Prop per map.

All proofs kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom. The disclosed geometric inputs are structure fields, not axioms.
-/
import Mathlib
import SKEFTHawking.IntCapProductInt

namespace SKEFTHawking.SingularCohomologyInt

open SKEFTHawking.SingularHomologyInt

variable {X : TopCat}

/-! ## §1. The two integral-PD maps, BUILT from existing infrastructure -/

/-- **The integral cap map `·⌢[M] : H²(M;ℤ) →ₗ[ℤ] H₂(M;ℤ)`** as a plain ℤ-linear map, obtained by
evaluating the built integral cap `capHInt 2 1` against the integral fundamental class `[M] : Homology X 4`.
This is the map whose iso-ness is the geometric heart of Poincaré duality (field (i) of `IntCapIso`). -/
noncomputable def capMapLin (zM : Homology X 4) : Cohomology X 2 →ₗ[ℤ] Homology X 2 :=
  (capHInt 2 1).flip zM

/-- **The integral Kronecker map `H₂(M;ℤ) →ₗ[ℤ] Dual ℤ (H²(M;ℤ))`**, `h ↦ ⟨·, h⟩`, obtained by flipping the
built integral Kronecker pairing `kroneckerHInt 2 : H² →ₗ H₂ →ₗ ℤ`. Its iso-ness is field (ii) of
`IntCapIso` (the integral perfect pairing / UCT-torsion-free datum). -/
noncomputable def kronMapLin : Homology X 2 →ₗ[ℤ] Module.Dual ℤ (Cohomology X 2) :=
  (kroneckerHInt 2).flip

/-- `capMapLin zM a = capHInt 2 1 a zM` — the cap map evaluated at a class is the built cap. -/
@[simp] theorem capMapLin_apply (zM : Homology X 4) (a : Cohomology X 2) :
    capMapLin zM a = capHInt 2 1 a zM :=
  rfl

/-- `kronMapLin h b = kroneckerHInt 2 b h` — the Kronecker map evaluated at `(h, b)` is the built pairing. -/
@[simp] theorem kronMapLin_apply (h : Homology X 2) (b : Cohomology X 2) :
    kronMapLin h b = kroneckerHInt 2 b h :=
  rfl

/-! ## §2. The concrete determinant datum `IntCapIsoData` and the reduction `→ IntCapIso` -/

/-- **The concrete integral cap-iso datum** — the sharpened, checkable replacement for `IntCapIso`'s two
abstract `≃ₗ` fields.

Instead of disclosing the cap and Kronecker isomorphisms abstractly, this datum discloses only:
* `h2Basis` — a finite free basis of `H₂(M;ℤ)`, indexed by the SAME `Fin B.rank` as the `H²` basis `B`
  (the equal-rank index IS the Poincaré-duality fact `b₂(H₂) = b₂(H²)`; the homology-side analogue of the
  already-disclosed `IntH2Basis` on `H²`). Mathlib has no manifold homology, so — exactly as `[M]` is
  `IntFundamentalClass` and the `H²` basis is `IntH2Basis` — this is a datum;
* `capUnit` — the cap matrix `(toMatrix B.basis h2Basis) (capMapLin [M])` has UNIT determinant;
* `kronUnit` — the Kronecker matrix `(toMatrix h2Basis B.basis.dualBasis) kronMapLin` has UNIT determinant.

Both determinants live in `ℤ`, so `IsUnit d ↔ d = ±1` (`Int.isUnit_iff`) — genuinely checkable integer data.
The maps `capMapLin`/`kronMapLin` are BUILT (§1), not disclosed; only their invertibility (as one integer
determinant each) is the disclosed input. This is the exact integer analogue of the H²-side `interMatrix`
datum, and strictly sharper than `IntCapIso`'s abstract isos. Discharge of each unit-det fact = build
integral singular homology + prove the local-global integral PD (MV + Euclidean local cap-iso). -/
structure IntCapIsoData (zM : Homology X 4) (B : IntH2Basis X) where
  /-- The disclosed finite free basis of `H₂(M;ℤ)`, indexed by the SAME `Fin B.rank` as the `H²` basis
  (equal-rank = Poincaré duality `b₂ = b₂`). -/
  h2Basis : Module.Basis (Fin B.rank) ℤ (Homology X 2)
  /-- The integral cap matrix has unit determinant (the cap `·⌢[M] : H² → H₂` is an iso). -/
  capUnit : IsUnit ((LinearMap.toMatrix B.basis h2Basis) (capMapLin zM)).det
  /-- The integral Kronecker matrix has unit determinant (the pairing `H₂ → Dual H²` is perfect). -/
  kronUnit : IsUnit ((LinearMap.toMatrix h2Basis B.basis.dualBasis) kronMapLin).det

/-- **The cap equivalence from the cap unit-determinant datum** — `capMapLin [M] : H²(M;ℤ) ≃ₗ[ℤ] H₂(M;ℤ)`,
built via `LinearEquiv.ofIsUnitDet` from the disclosed `capUnit`. Its underlying map is exactly
`capMapLin zM` (`LinearEquiv.ofIsUnitDet_apply`), i.e. `a ↦ capHInt 2 1 a [M]`. -/
noncomputable def IntCapIsoData.capEquivOf {zM : Homology X 4} {B : IntH2Basis X}
    (C : IntCapIsoData zM B) : Cohomology X 2 ≃ₗ[ℤ] Homology X 2 :=
  LinearEquiv.ofIsUnitDet C.capUnit

/-- **The Kronecker equivalence from the Kronecker unit-determinant datum** —
`kronMapLin : H₂(M;ℤ) ≃ₗ[ℤ] Dual ℤ (H²(M;ℤ))`, built via `LinearEquiv.ofIsUnitDet` from `kronUnit`. Its
underlying map is exactly `kronMapLin`, i.e. `h ↦ ⟨·, h⟩`. -/
noncomputable def IntCapIsoData.kronEquivOf {zM : Homology X 4} {B : IntH2Basis X}
    (C : IntCapIsoData zM B) : Homology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2) :=
  LinearEquiv.ofIsUnitDet C.kronUnit

/-- **`IntCapIso` from the concrete determinant datum** — the reduction: given `IntCapIsoData zM B` (the two
built maps `capMapLin`/`kronMapLin` each with unit determinant on the disclosed bases), the abstract-iso
`IntCapIso zM` is inhabited, with `capEquiv := capEquivOf` and `kronEquiv := kronEquivOf`. The `_apply`
compatibilities come from `LinearEquiv.ofIsUnitDet_apply` + the `capMapLin_apply`/`kronMapLin_apply`
defeq. This replaces `IntCapIso`'s two abstract `≃ₗ` disclosures with two integer-determinant units. -/
noncomputable def IntCapIsoData.toIntCapIso {zM : Homology X 4} {B : IntH2Basis X}
    (C : IntCapIsoData zM B) : IntCapIso zM where
  capEquiv := C.capEquivOf
  capEquiv_apply a := by rw [IntCapIsoData.capEquivOf, LinearEquiv.ofIsUnitDet_apply, capMapLin_apply]
  kronEquiv := C.kronEquivOf
  kronEquiv_apply h b := by
    rw [IntCapIsoData.kronEquivOf, LinearEquiv.ofIsUnitDet_apply, kronMapLin_apply]

/-- **`IntPoincareDuality` from the concrete determinant datum** — composing `IntCapIsoData.toIntCapIso`
with brick 9's `intPoincareDualityOfCapIso`. The disclosed `IntPoincareDuality` is now anchored on the two
unimodular-determinant facts of concretely-built maps. -/
noncomputable def intPoincareDualityOfCapIsoData {zM : Homology X 4} {B : IntH2Basis X}
    (C : IntCapIsoData zM B) : IntPoincareDuality (intFundamentalClassOfHomology zM) :=
  intPoincareDualityOfCapIso C.toIntCapIso

/-- **Unimodularity of the intersection matrix from the concrete determinant datum** — the end-to-end
reduction landing on the CONCRETE integer-determinant inputs: given `IntCapIsoData zM B`, the integer
intersection matrix `interMatrix (intFundamentalClassOfHomology [M]) B` is unimodular. Composes
`intPoincareDualityOfCapIsoData` with the DONE `interMatrix_isUnimodular_of_intPD`. -/
theorem interMatrix_isUnimodular_of_capIsoData {zM : Homology X 4} (B : IntH2Basis X)
    (C : IntCapIsoData zM B) :
    IsUnimodular (interMatrix (intFundamentalClassOfHomology zM) B) :=
  interMatrix_isUnimodular_of_intPD _ B (intPoincareDualityOfCapIsoData C)

/-! ## §3. The mod-2 shadow partial — the honest gap between `nondeg_of_closed` and unimodularity

The on-main mod-2 non-degeneracy `SingularPD4Instances.nondeg_of_closed` proves the mod-2 cap
`·⌢[M]₂` INJECTIVE. In a matching-rank mod-2 basis this makes the *mod-2 reduction* of the integral cap
matrix invertible over the field `ZMod 2` — hence its determinant is a unit there. What that buys for the
INTEGRAL cap matrix is captured by the purely-algebraic bridge below: a unit mod-2 reduction forces the
integer determinant ODD (`¬ 2 ∣ det`), which is STRICTLY WEAKER than `det = ±1` (unimodular). E.g. `⟨3⟩` has
odd — indeed unit-mod-2 — determinant `3` but is not unimodular. So the mod-2 shadow gives `Odd det`, never
`IsUnit det`; the residual gap to full integral PD is exactly this parity-to-unit strengthening — the
community-scale geometric input isolated cleanly. -/

/-- **The mod-2 reduction ring hom `ℤ →+* ZMod 2`** — pointwise `Int.cast` on determinants/matrices. -/
private abbrev redZ2 : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

/-- **A unit mod-2 reduction of an integer matrix forces its determinant ODD** (the honest content of the
mod-2 shadow). If the entrywise-mod-2 reduction `M.map (·:ℤ→ZMod 2)` of a square integer matrix `M` has
UNIT determinant over the field `ZMod 2` (equivalently: is invertible — the algebraic content of the mod-2
cap being injective in matching rank, `nondeg_of_closed`), then `M.det` is odd, i.e. `¬ 2 ∣ M.det`.
`RingHom.map_det` identifies `(M.det : ZMod 2)` with `det (M mod 2)`; a unit in a field is nonzero; and over
`ZMod 2`, `(n : ZMod 2) ≠ 0 ↔ ¬ 2 ∣ n ↔ Odd n`. Strictly weaker than `IsUnimodular` — the parity floor. -/
theorem odd_det_of_isUnit_det_map_zmod2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (h : IsUnit (redZ2.mapMatrix M).det) : Odd M.det := by
  have hne : (redZ2 M.det) ≠ 0 := by
    rw [RingHom.map_det]
    exact h.ne_zero
  rw [Int.odd_iff, ← Int.two_dvd_ne_zero]
  intro hdvd
  apply hne
  simpa [redZ2, ZMod.intCast_zmod_eq_zero_iff_dvd] using hdvd

/-- **The integral cap matrix has ODD determinant, given a unit mod-2 cap reduction** — the mod-2-shadow
partial on field (i) of `IntCapIso`, specialized to the concrete cap matrix `(toMatrix B.basis Bh)
(capMapLin [M])`. The hypothesis `hmod2` (the mod-2 reduction of the cap matrix is invertible over `ZMod 2`)
is exactly what the on-main mod-2 injective `nondeg_of_closed` delivers in a matching-rank mod-2 basis; the
conclusion `Odd det` is the honest floor the mod-2 shadow gives for the integral cap determinant — one step
short of the full `IsUnit det` (unimodular) that full integral PD needs. -/
theorem odd_capMatrix_det_of_mod2_unit {zM : Homology X 4} (B : IntH2Basis X)
    (Bh : Module.Basis (Fin B.rank) ℤ (Homology X 2))
    (hmod2 : IsUnit (redZ2.mapMatrix ((LinearMap.toMatrix B.basis Bh) (capMapLin zM))).det) :
    Odd ((LinearMap.toMatrix B.basis Bh) (capMapLin zM)).det :=
  odd_det_of_isUnit_det_map_zmod2 _ hmod2

end SKEFTHawking.SingularCohomologyInt
