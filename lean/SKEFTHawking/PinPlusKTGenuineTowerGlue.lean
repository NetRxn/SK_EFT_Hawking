/-
# Phase 5q.H close-out (#205) — THE COORDINATIZATION GLUE: the spec-1-compliant tower population

`#201` landed the GENUINE integral-tower maps as honest cohomology objects:
`restrictHInt` (the integral `ι*`), `deltaRelHIntLin` (the pair connecting map `δ` as a genuine
`ℤ`-`LinearMap` via the two-quotient descent), the pair-LES composite `δ ∘ ι* = 0`
(`deltaRelHIntLin_restrictHInt`), the object-level PD-square `coord_hadj_deltaRelHIntLin`, and the
δ⊣∂ adjunction `relKroneckerHInt_deltaRelHIntLin`. It named the residual atom
`GenuineBoundingWTower` and the population path into `NovikovGeometricPairLESData`.

This module lands THE GLUE. The population is **round-13 spec-1 compliant BY DESIGN**: `rest2`, `delta`
and `pairing` are the ⊗ℝ coordinatizations of the GENUINE `#201` integral maps `restrictHInt`,
`deltaRelHIntLin`, and `relKroneckerHInt (·) (capRelHInt · Z)` — each merely expressed through
finite-free `ℤ`-bases OF THE GENUINE COHOMOLOGY OBJECTS (`Cohomology X 2`,
`RelativeCohomologyInt S 3`) and the disclosed boundary basis `B`, NOT posited matrices and NOT a
quotient-of-coordinate-space `H3rel` (the reverted `BoundingWCoordData` refuted shape). DATA
INSPECTION of `rest2Coord`/`deltaCoord`/`pairingCoord` traces every entry to the genuine map.

## The base-change discipline (basis-repr-direct, NO TensorProduct)

For a finite-free `ℤ`-basis `bM`/`bN` of the genuine objects, the ⊗ℝ coordinatization of a genuine
`ℤ`-linear `f : M →ₗ[ℤ] N` is `realizeZR bM bN f := Matrix.toLin' ((LinearMap.toMatrix bM bN f).map
Int.cast)` — the integer representing matrix `Int.cast`-lifted to `ℝ`. Its defining semantics
(`realizeZR_coordR`) is that on the real coordinate vector of an actual class `x` it returns the real
coordinate vector of `f x` (`Int.cast` commutes with `mulVec`; `LinearMap.toMatrix_mulVec_repr`). This
is exactly the `#196` `coord = Int.cast ∘ repr` pattern generalized to an arbitrary basis, with NO
`TensorProduct`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTNovikovTowerPopulate
import SKEFTHawking.SingularRelativeUCInt

namespace SKEFTHawking.PinPlusKTGenuineTowerGlue

open scoped Matrix
open SKEFTHawking
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeUCInt
open SKEFTHawking.SingularRelativeCohomDeltaInt
open SKEFTHawking.SingularRelativeCapHomologyInt
open SKEFTHawking.SingularRelativeCapConnectingInt
open SKEFTHawking.SingularRelativeCapHadjInt
open SKEFTHawking.SingularRelativeRealBaseChange
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.PinPlusKTNovikovTowerInstantiate
open SKEFTHawking.PinPlusKTNovikovTowerPopulate

/-! ## §1. The base-change of a genuine `ℤ`-linear map through finite-free `ℤ`-bases (basis-repr-direct) -/

/-- The real coordinate vector of a class `x` in a finite-free `ℤ`-module through a basis `b`
(`Int.cast ∘ repr`; the `#196` `coord` pattern generalized to an arbitrary basis). -/
noncomputable def coordR {M : Type*} [AddCommGroup M] [Module ℤ M] {m : ℕ}
    (b : Module.Basis (Fin m) ℤ M) (x : M) : Fin m → ℝ :=
  fun i => ((b.repr x i : ℤ) : ℝ)

/-- **The ⊗ℝ coordinatization of a genuine `ℤ`-linear map.** For finite-free `ℤ`-bases `bM`, `bN`, the
integer representing matrix of `f` `Int.cast`-lifted to `ℝ`, as an `ℝ`-`LinearMap` on coordinate
spaces. This is the honest base-change: NO `TensorProduct`, just the representing matrix. -/
noncomputable def realizeZR {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    {m n : ℕ} (bM : Module.Basis (Fin m) ℤ M) (bN : Module.Basis (Fin n) ℤ N) (f : M →ₗ[ℤ] N) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLin' ((LinearMap.toMatrix bM bN f).map (Int.cast : ℤ → ℝ))

/-- **The defining semantics of `realizeZR`.** On the real coordinate vector of an actual class `x`,
`realizeZR bM bN f` returns the real coordinate vector of `f x` — the coordinatization genuinely
tracks the map. Proof: `Int.cast` commutes with `mulVec`, then `LinearMap.toMatrix_mulVec_repr`. -/
theorem realizeZR_coordR {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    {m n : ℕ} (bM : Module.Basis (Fin m) ℤ M) (bN : Module.Basis (Fin n) ℤ N) (f : M →ₗ[ℤ] N)
    (x : M) :
    realizeZR bM bN f (coordR bM x) = coordR bN (f x) := by
  ext i
  rw [realizeZR, Matrix.toLin'_apply]
  have key : ((LinearMap.toMatrix bM bN) f).mulVec (⇑(bM.repr x)) i = (bN.repr (f x)) i :=
    congrFun (LinearMap.toMatrix_mulVec_repr bM bN f x) i
  simp only [coordR, Matrix.mulVec, Matrix.map_apply, dotProduct]
  rw [← key, Matrix.mulVec, dotProduct]
  push_cast
  rfl

/-- Two-basis bilinear expansion over `ℤ`: `g a c = ∑ᵢⱼ (repr a)ᵢ (repr c)ⱼ · g(bMᵢ)(bNⱼ)`. -/
theorem bilin_expand_two_basis {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {p q : ℕ} (bM : Module.Basis (Fin p) ℤ M)
    (bN : Module.Basis (Fin q) ℤ N) (g : M →ₗ[ℤ] N →ₗ[ℤ] ℤ) (a : M) (c : N) :
    g a c = ∑ i, ∑ j, bM.repr a i * bN.repr c j * g (bM i) (bN j) := by
  conv_lhs => rw [← bM.sum_repr a, ← bN.sum_repr c]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- **The ⊗ℝ coordinatization of a genuine `ℤ`-bilinear form** `g : M × N → ℤ`, through finite-free
`ℤ`-bases `bM`, `bN`: the integer Gram matrix `gᵢⱼ = g(bMᵢ)(bNⱼ)` `Int.cast`-lifted to `ℝ`. -/
noncomputable def realizeBilinZR {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {p q : ℕ} (bM : Module.Basis (Fin p) ℤ M)
    (bN : Module.Basis (Fin q) ℤ N) (g : M →ₗ[ℤ] N →ₗ[ℤ] ℤ) :
    (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ) →ₗ[ℝ] ℝ :=
  Matrix.toLinearMap₂' ℝ ((Matrix.of fun i j => g (bM i) (bN j)).map (Int.cast : ℤ → ℝ))

/-- **The defining semantics of `realizeBilinZR`.** On the real coordinate vectors of actual classes
`a`, `c`, it returns the `ℝ`-cast of `g a c` — the coordinatization genuinely tracks the form. -/
theorem realizeBilinZR_coordR {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {p q : ℕ} (bM : Module.Basis (Fin p) ℤ M)
    (bN : Module.Basis (Fin q) ℤ N) (g : M →ₗ[ℤ] N →ₗ[ℤ] ℤ) (a : M) (c : N) :
    realizeBilinZR bM bN g (coordR bM a) (coordR bN c) = ((g a c : ℤ) : ℝ) := by
  rw [realizeBilinZR, Matrix.toLinearMap₂'_apply, bilin_expand_two_basis bM bN g a c]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [coordR, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  ring

variable {X : TopCat} {S : Set X}

/-! ## §2. The genuine integral tower maps and their ⊗ℝ coordinatizations -/

/-- **The genuine integral pairing** `⟨a, r⟩ := ⟨r, a ⌢ [W,∂W]⟩` — `relKroneckerHInt` of the relative
cap of an absolute `H²(W)` class `a` with the tethered relative fundamental class of `Z`. The genuine
`#201`/`#196` `relKroneckerHInt`/`capRelHInt` chain, packaged as a `ℤ`-bilinear form. -/
noncomputable def pairingInt (Z : relCycleLift S (2 + 1 + 1)) :
    Cohomology X 2 →ₗ[ℤ] RelativeCohomologyInt S (2 + 1) →ₗ[ℤ] ℤ :=
  (relKroneckerHInt S).flip.comp ((capRelHInt 2 2).flip (relCycleToHom S (2 + 1 + 1) Z))

@[simp] theorem pairingInt_apply (Z : relCycleLift S (2 + 1 + 1)) (a : Cohomology X 2)
    (r : RelativeCohomologyInt S (2 + 1)) :
    pairingInt Z a r
      = relKroneckerHInt S r (capRelHInt 2 2 a (relCycleToHom S (2 + 1 + 1) Z)) := rfl

/-- **`rest2` — the ⊗ℝ coordinatization of the GENUINE integral restriction `ι* = restrictHInt`**
(`#201`) through the disclosed bases `Bw` of `H²(W;ℤ)` and `B` of `H²(∂W;ℤ)`. DATA INSPECTION: the
map IS `realizeZR Bw.basis B.basis restrictHInt` — no posited matrix. -/
noncomputable def rest2Coord (Bw : IntH2Basis X) (B : IntH2Basis (sub S)) :
    (Fin Bw.rank → ℝ) →ₗ[ℝ] (Fin B.rank → ℝ) :=
  realizeZR Bw.basis B.basis (restrictHInt (S := S))

/-- **`delta` — the ⊗ℝ coordinatization of the GENUINE integral connecting map `δ = deltaRelHIntLin`**
(`#201`) through `B` of `H²(∂W;ℤ)` and `Br` of `H³(W,∂W;ℤ)`. DATA INSPECTION: the map IS
`realizeZR B.basis Br deltaRelHIntLin` — no posited matrix. -/
noncomputable def deltaCoord {q : ℕ} (B : IntH2Basis (sub S))
    (Br : Module.Basis (Fin q) ℤ (RelativeCohomologyInt S (2 + 1))) :
    (Fin B.rank → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
  realizeZR B.basis Br (deltaRelHIntLin (S := S))

/-- **`pairing` — the ⊗ℝ coordinatization of the GENUINE integral relative-Kronecker/cap pairing**
`pairingInt Z` through `Bw` of `H²(W;ℤ)` and `Br` of `H³(W,∂W;ℤ)`. DATA INSPECTION: the form IS
`realizeBilinZR Bw.basis Br (pairingInt Z)` — no posited matrix. -/
noncomputable def pairingCoord {q : ℕ} (Bw : IntH2Basis X)
    (Br : Module.Basis (Fin q) ℤ (RelativeCohomologyInt S (2 + 1)))
    (Z : relCycleLift S (2 + 1 + 1)) :
    (Fin Bw.rank → ℝ) →ₗ[ℝ] (Fin q → ℝ) →ₗ[ℝ] ℝ :=
  realizeBilinZR Bw.basis Br (pairingInt Z)

end SKEFTHawking.PinPlusKTGenuineTowerGlue
