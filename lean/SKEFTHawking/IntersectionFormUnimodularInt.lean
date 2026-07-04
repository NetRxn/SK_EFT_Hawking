/-
# Phase 5q.H · E1 — the UNIMODULAR conjunct of `IsEvenUnimodular interMatrix` via integral Poincaré duality

Substrate-G foundation brick. Discharges the **unimodular** conjunct (`IsUnimodular`, i.e. `det = ±1`)
of `AlgebraicRokhlin.IsEvenUnimodular (interMatrix fc B)` — the LAST of the three conjuncts
(`symmetric ∧ unimodular ∧ even`). The `symmetric` conjunct is discharged upstream
(`IntersectionMatrixInt.interMatrix_isSymmetricInt`); `even` from the mod-2 Wu criterion
(`IntersectionFormEvenInt.interMatrix_even_of_spinWu`). This module reduces `unimodular` to a SINGLE
clean disclosed geometric Prop: **integral Poincaré duality** = the integral intersection form is a
PERFECT pairing.

## The idea (standard: perfect pairing ⟹ unimodular Gram matrix)

The integral intersection form `interFormInt fc : H²(M;ℤ) →ₗ[ℤ] H²(M;ℤ) →ₗ[ℤ] ℤ` is, curried, a map
`H²(M;ℤ) →ₗ[ℤ] Module.Dual ℤ (H²(M;ℤ))` (since `Module.Dual ℤ V = V →ₗ[ℤ] ℤ`), `a ↦ ⟨a ∪ ·, [M]⟩`.
**Integral Poincaré duality** is exactly the statement that THIS map is an ISOMORPHISM — a perfect
pairing (equivalently the integral cap map `·⌢[M] : H²(M;ℤ) → H₂(M;ℤ)` is an iso, since `H₂(M;ℤ)`
is dual to `H²(M;ℤ)`). Over `ZMod 2` the analogue is the on-main non-degeneracy
`SingularPD4Instances.nondeg_of_closed` (INJECTIVITY of the mod-2 form); over ℤ the iso statement is
STRICTLY STRONGER than mod-2 non-degeneracy (which only gives `det` odd, i.e. `2` is nondegenerate but
not unimodular).

Given the perfect-pairing iso `PD : H²(M;ℤ) ≃ₗ[ℤ] Module.Dual ℤ (H²(M;ℤ))` whose underlying map is
`interFormInt fc`, the Gram matrix in the basis `B.basis` and its dual basis is exactly `interMatrix`:

  `(LinearMap.toMatrix B.basis B.basis.dualBasis) PD i j`
    `= (B.basis.dualBasis.repr (PD (B.basis j))) i`          -- `LinearMap.toMatrix_apply`
    `= (PD (B.basis j)) (B.basis i)`                          -- `Module.Basis.dualBasis_repr`
    `= interFormInt fc (B.basis j) (B.basis i)`               -- `PD` underlies `interFormInt fc`
    `= interFormInt fc (B.basis i) (B.basis j)`               -- symmetry `interFormInt_symm`
    `= interMatrix fc B i j`.

By `LinearEquiv.isUnit_det`, `IsUnit ((toMatrix B.basis B.basis.dualBasis) PD).det`, hence
`IsUnit (interMatrix fc B).det`; over ℤ (`Int.isUnit_iff`) `IsUnit n ↔ n = 1 ∨ n = -1`, which is
exactly `IsUnimodular (interMatrix fc B)`.

## What is proved vs. disclosed

PROVED (kernel-pure, `{propext, Classical.choice, Quot.sound}`; no `sorry`/`native_decide`/
`maxHeartbeats`/axiom):
* `IntPoincareDuality` — the disclosed datum: a ℤ-linear-equivalence `H²(M;ℤ) ≃ₗ[ℤ] Dual ℤ H²(M;ℤ)`
  whose underlying map is `interFormInt fc` (integral PD, the perfect-pairing form);
* `interMatrix_eq_toMatrix_intPD` — the Gram matrix `interMatrix fc B` IS the matrix of the PD iso in
  the basis/dual-basis pair;
* `interMatrix_isUnit_det_of_intPD` — the determinant of `interMatrix` is a unit (`LinearEquiv.isUnit_det`);
* `interMatrix_isUnimodular_of_intPD` — **`IsUnimodular (interMatrix fc B)`** (`Int.isUnit_iff`);
* `isEvenUnimodular_of_intPD` — the FULL `IsEvenUnimodular (interMatrix fc B)` assembled from the three
  now-reduced conjuncts (symmetric ✓, even ✓ via `SpinWuDatum`, unimodular ✓ via `IntPoincareDuality`);
* `sixteen_dvd_manifold_sig_of_intPD` — the manifold-level `σ÷16` with `IsEvenUnimodular` fully
  reduced to its two disclosed geometric data + the topological Rokhlin factor.

DISCLOSED DATUM (structure field, not axiom): `IntPoincareDuality fc` = the integral-PD perfect-pairing
iso. Registered in `HYPOTHESIS_REGISTRY` as `intPoincareDuality_perfectPairing_datum`. Discharge = build
integral homology `H₂(M;ℤ)` + the integral cap product `·⌢[M]` + prove it an iso (the community-scale
integral-PD core, of which the mod-2 injective `nondeg_of_closed` is the char-2 shadow).

This completes the `IsEvenUnimodular` analysis: all three conjuncts are now either PROVED (symmetric) or
reduced to a single clean disclosed geometric datum (even = `SpinWuDatum`, unimodular = `IntPoincareDuality`).
-/
import Mathlib
import SKEFTHawking.SingularIntersectionFormInt
import SKEFTHawking.IntersectionMatrixInt
import SKEFTHawking.IntersectionFormEvenInt
import SKEFTHawking.AlgebraicRokhlin

namespace SKEFTHawking.SingularCohomologyInt

open SKEFTHawking SKEFTHawking.SingularCohomologyInt

variable {X : TopCat}

/-! ## §1. Integral Poincaré duality as a disclosed perfect-pairing datum -/

/-- **Integral Poincaré duality, carried as the perfect-pairing isomorphism** — a disclosed datum
(NOT an axiom).

For a closed oriented 4-manifold `M`, the integral intersection form `interFormInt fc`, curried, is a
ℤ-linear map `H²(M;ℤ) →ₗ[ℤ] Module.Dual ℤ (H²(M;ℤ))` (since `Module.Dual ℤ V = V →ₗ[ℤ] ℤ`),
`a ↦ ⟨a ∪ ·, [M]⟩`. **Poincaré duality** is the statement that this map is an ISOMORPHISM: the form is
a PERFECT pairing (equivalently the integral cap map `·⌢[M] : H²(M;ℤ) → H₂(M;ℤ)` is an iso, `H₂` being
dual to `H²`). This is the community-scale integral-PD core; its char-2 shadow is the on-main injective
non-degeneracy `SingularPD4Instances.nondeg_of_closed`.

Carried as the equivalence `toDualEquiv` PLUS the compatibility `toDualEquiv_apply` fixing its
underlying map to be `interFormInt fc`. Disclosed tracked hypothesis
`intPoincareDuality_perfectPairing_datum` (`HYPOTHESIS_REGISTRY`, tier `discharge_future`). Discharge =
build `H₂(M;ℤ)` + `·⌢[M]` + prove the iso (integral PD). Every result here holds for an arbitrary such
datum, so it is the ONLY unproved input to unimodularity. -/
structure IntPoincareDuality (fc : IntFundamentalClass X) where
  /-- The perfect-pairing isomorphism `H²(M;ℤ) ≃ₗ[ℤ] Module.Dual ℤ (H²(M;ℤ))` of integral PD. -/
  toDualEquiv : Cohomology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2)
  /-- The equivalence's underlying map is the intersection form (curried to the dual):
  `PD a b = ⟨a ∪ b, [M]⟩`. -/
  toDualEquiv_apply : ∀ a b : Cohomology X 2, toDualEquiv a b = interFormInt fc a b

/-! ## §2. The Gram matrix is the matrix of the PD iso -/

/-- **The intersection matrix is the matrix of the integral-PD iso** in the basis/dual-basis pair:
`interMatrix fc B = (LinearMap.toMatrix B.basis B.basis.dualBasis) PD.toDualEquiv`.

Entrywise: `toMatrix B.basis B.basis.dualBasis PD i j = (B.basis.dualBasis.repr (PD (B.basis j))) i =
(PD (B.basis j)) (B.basis i) = interFormInt fc (B.basis j) (B.basis i) = interFormInt fc (B.basis i)
(B.basis j) = interMatrix fc B i j` (last step by symmetry `interFormInt_symm`). -/
theorem interMatrix_eq_toMatrix_intPD (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (PD : IntPoincareDuality fc) :
    interMatrix fc B
      = (LinearMap.toMatrix B.basis B.basis.dualBasis) (PD.toDualEquiv : Cohomology X 2 →ₗ[ℤ] _) := by
  ext i j
  rw [LinearMap.toMatrix_apply, interMatrix_apply, Module.Basis.dualBasis_repr,
    LinearEquiv.coe_coe, PD.toDualEquiv_apply, interFormInt_symm]

/-! ## §3. Unimodularity via `LinearEquiv.isUnit_det` -/

/-- **The determinant of the intersection matrix is a unit**, given integral PD. Immediate from
`LinearEquiv.isUnit_det` applied to the perfect-pairing equivalence `PD.toDualEquiv` (a genuine
`≃ₗ[ℤ]`) in the basis/dual-basis pair, transported through `interMatrix_eq_toMatrix_intPD`. -/
theorem interMatrix_isUnit_det_of_intPD (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (PD : IntPoincareDuality fc) :
    IsUnit (interMatrix fc B).det := by
  rw [interMatrix_eq_toMatrix_intPD fc B PD]
  exact LinearEquiv.isUnit_det PD.toDualEquiv B.basis B.basis.dualBasis

/-- **The integer intersection matrix is UNIMODULAR** (`AlgebraicRokhlin.IsUnimodular`, `det = ±1`),
given integral PD. From `interMatrix_isUnit_det_of_intPD` + `Int.isUnit_iff` (`IsUnit n ↔ n = 1 ∨
n = -1` over ℤ). This is the **UNIMODULAR conjunct** of `IsEvenUnimodular (interMatrix fc B)` — the last
of the three, reduced to the single disclosed integral-PD perfect-pairing datum. -/
theorem interMatrix_isUnimodular_of_intPD (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (PD : IntPoincareDuality fc) :
    IsUnimodular (interMatrix fc B) :=
  Int.isUnit_iff.mp (interMatrix_isUnit_det_of_intPD fc B PD)

/-! ## §4. The full `IsEvenUnimodular` — all three conjuncts reduced -/

/-- **`IsEvenUnimodular (interMatrix fc B)` from the two disclosed geometric data.**

The complete even-unimodular hypothesis the DONE lattice `σ÷16` leg consumes, assembled from all three
conjuncts now discharged/reduced:
* `symmetric` — PROVED (`interMatrix_isSymmetricInt`, graded-commutativity of the cup product);
* `even` — from the mod-2 Wu criterion through the ℤ→ℤ/2 reduction bridge (`interMatrix_even_of_spinWu`),
  under the disclosed `SpinWuDatum D` (`w₂ = 0`, Spin);
* `unimodular` — from integral Poincaré duality (`interMatrix_isUnimodular_of_intPD`), under the disclosed
  `IntPoincareDuality PD` (the perfect-pairing iso).

So `IsEvenUnimodular interMatrix` is now reduced to EXACTLY two clean disclosed geometric data —
`SpinWuDatum` (Spin/Wu) and `IntPoincareDuality` (perfect pairing) — with no residual algebraic gap. -/
theorem isEvenUnimodular_of_intPD (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (D : SpinWuDatum fc) (PD : IntPoincareDuality fc) :
    IsEvenUnimodular (interMatrix fc B) :=
  ⟨interMatrix_isSymmetricInt fc B, interMatrix_isUnimodular_of_intPD fc B PD,
    interMatrix_even_of_spinWu fc B D⟩

/-- **The manifold-level Rokhlin `σ÷16` with `IsEvenUnimodular` fully reduced to disclosed geometry.**

`sixteen_dvd_manifold_sig` with its `IsEvenUnimodular` hypothesis now supplied from the two disclosed
geometric data (`SpinWuDatum` + `IntPoincareDuality`) rather than assumed as a black box. The remaining
inputs are exactly: the Spin/Wu datum (`w₂ = 0`), the integral-PD perfect pairing (`·⌢[M]` iso), and the
topological Rokhlin factor `2 ∣ σ/8` (Guillou–Marin — provably not algebraic, `nogo_lattice_arf_not_sigma8`).
The orientation `[M]`/`IntFundamentalClass` and finite free basis `IntH2Basis` are disclosed upstream. -/
theorem sixteen_dvd_manifold_sig_of_intPD (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (D : SpinWuDatum fc) (PD : IntPoincareDuality fc)
    (htopo : (2 : ℤ) ∣ latticeSig (interMatrix fc B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix fc B) :=
  sixteen_dvd_manifold_sig fc B (isEvenUnimodular_of_intPD fc B D PD) htopo

end SKEFTHawking.SingularCohomologyInt
