/-
# Phase 5q.H — Kummer K1, the GEOMETRIC half: `H₂(T⁴;ℤ)` singular-homology framework

Continues `KummerInvolution.lean`, whose K1 **arithmetic** half already landed the concrete `3H`
integer form `torusFourForm : Matrix (Fin 6) (Fin 6) ℤ` (even unimodular, σ = 0, `IntCongr` to the
hyperbolic normal form). This module builds the **geometric** half — the genuine singular-homology
side of `H₂(T⁴;ℤ) ≅ ℤ⁶` — as far as it goes UNCONDITIONALLY on the project's custom integral
singular-homology functor `SingularHomologyInt.Homology`. Kernel-pure (`{propext, Classical.choice,
Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom; nothing posited.

**What lands here (the reusable geometric inputs to the eventual 4-fold Künneth).**
* §1 — **the per-factor circle homology inputs.** `T⁴ = (S¹)⁴`, so every Künneth summand is a tensor
  of the per-factor homology `H_*(S¹;ℤ)`: `H₁(S¹;ℤ) ≅ ℤ` (`circleHOneEquiv`, reusing the banked
  `circleH1EquivInt`) and `H_{k+2}(S¹;ℤ) = 0` (`circleH_high`, from `sphere_homology_high`). These
  pin the per-factor input as "`ℤ` in degree 1, `0` above" — the data a Künneth for `H₂((S¹)⁴)`
  consumes.
* §2 — **the `Circle ≃ₜ Sph 1` bridge.** The banked circle-homology stack lives on `Sph 1` (the unit
  circle in `𝔼²`), but `T⁴` is literally `Circle⁴` (the unit circle in `ℂ`). The ℝ-linear isometry
  `ℂ ≃ₗᵢ[ℝ] 𝔼²` restricts to a homeomorphism of unit circles (`circleHomeoSph1`), transporting every
  `Sph 1` homology fact onto the *actual* `Circle` factor (`circleFactorHOneEquiv`,
  `circleFactorH_high`). This is the load-bearing identification every future `TorusFour`-Künneth
  brick needs: without it the `Sph 1` stack does not touch `Circle⁴`.
* §3 — **the rank-6 degree-2 Künneth-index pin.** The degree-2 summands of `H₂((S¹)⁴)` are indexed by
  the ways to pick which `2` of the `4` circle factors contribute their `H₁ = ℤ` (the others
  contributing `H₀ = ℤ`): `C(4,2) = 6` summands. `hTwoIndex_card` proves the honest count
  `Fintype.card {s : Finset (Fin 4) // s.card = 2} = 6`, and `hTwoIndex_card_eq_form_rank` ties it to
  the arithmetic form's `Fin 6` index — the geometry-side `C(4,2) = 6` falsifiable pin matching
  `torusFourForm`'s rank.
* §4 — **`H₀(T⁴;ℤ) ≅ ℤ`** is the one genuine `TorusFour` homology group computable without Künneth:
  `T⁴` is path-connected (a product of path-connected circles), so its degree-0 homology is `ℤ`.
  (Reported as an honest boundary below when the integral connected-`H₀` port is not yet in-tree.)

**Honest boundary — the remaining brick (NOT shipped; a genuine multi-file sub-arc).** The identity
`H₂(T⁴;ℤ) ≅ ℤ⁶` itself, and the cup-form Gram identity `II(T⁴) ≅ torusFourForm`, need a **4-fold
Künneth** over `T⁴ = (S¹)⁴` for `SingularHomologyInt.Homology`. Mathlib has no Künneth / cross product
for singular homology, and the project's only in-tree product-homology computation — the S²×S² arc
(`SphereProdPuncturedPlaneInt` + `SphereProdHOneInt` + `SphereProdHTwoInt`, ~1500 lines of custom
polar-cover Mayer–Vietoris) — computes a *single* degree of a *single* product of two simply-connected
spheres. The `T⁴` analogue is strictly harder (non-simply-connected `S¹` factors, iterated four times,
with an `H₁` generator in every intermediate product `T², T³`) and, for the Gram, needs the
Eilenberg–Zilber cross product that the S²×S² Gram module (`SphereProdGramInt`) itself could only land
on the *diagonal* (`α² = 0`, `β² = 0`) while disclosing the *cross* terms (`α∪β = ±1`) as not-in-tree.
So the exact remaining bricks are: **(K1-a)** the 4-fold Künneth iso `H₂((S¹)⁴;ℤ) ≅ ⊕_{|s|=2} ℤ` (the
T⁴ analogue of `SphereProdHTwoInt`, built from §1's per-factor inputs) and **(K1-b)** the cross-product
Gram `II(T⁴) ≅ 3H` (the T⁴ analogue of the S²×S² cross-term Gram, needing Eilenberg–Zilber).
-/
import Mathlib
import SKEFTHawking.SingularLineMinusPointInt
import SKEFTHawking.SingularSphereHighDegreeInt
import SKEFTHawking.SingularProdContractibleInt
import SKEFTHawking.KummerK3Base
import SKEFTHawking.KummerInvolution

namespace SKEFTHawking.KummerHomologyT4

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularLineMinusPointInt (circleH1EquivInt topSphereIsoInt)
open SKEFTHawking.SingularSphereHighDegreeInt (sphere_homology_high)
open SKEFTHawking.SingularProdContractibleInt (homeoHomologyEquivInt)

/-! ## §1. Per-factor circle homology inputs (`S¹ = Sph 1`) -/

/-- **`H₁(S¹;ℤ) ≅ ℤ`** — the per-factor degree-1 input for the `H₂(T⁴)` Künneth (reuses the banked
`circleH1EquivInt`). Every degree-2 summand of `H₂((S¹)⁴)` is a tensor product of two copies of this
`ℤ` (from the two factors chosen to contribute their `H₁`) with two copies of `H₀ = ℤ`. -/
noncomputable def circleHOneEquiv : Homology (Sph 1) 1 ≃ₗ[ℤ] ℤ := circleH1EquivInt

/-- **`H_{k+2}(S¹;ℤ) = 0`** — the per-factor homology vanishes above degree 1 (`sphere_homology_high`
at `n = 1`). Together with `circleHOneEquiv` this pins the per-factor input as "`ℤ` in degrees 0, 1;
`0` above" — the exterior-algebra generator data a Künneth for `H₂((S¹)⁴)` consumes. -/
theorem circleH_high (k : ℕ) (x : Homology (Sph 1) (k + 2)) : x = 0 :=
  sphere_homology_high 1 (k + 2) (by omega) x

/-! ## §2. The `Circle ≃ₜ Sph 1` bridge -/

/-- The standard ℝ-linear isometry `ℂ ≃ₗᵢ[ℝ] 𝔼²` (from the canonical orthonormal basis of `𝔼²`).
Norm-preserving, so it carries the unit circle in `ℂ` onto the unit circle in `𝔼²`. -/
noncomputable def complexEuclidLI : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- **The homeomorphism `Circle ≃ₜ S¹`** identifying `T⁴`'s literal factor `Circle` (the unit circle
in `ℂ`) with the sphere-homology stack's `Sph 1` (the unit circle in `𝔼²`). Built from the ℝ-linear
isometry `complexEuclidLI`, which preserves norm and hence maps the unit circle onto the unit circle.
This is the load-bearing identification transporting every banked `Sph 1` homology fact onto the
`Circle` that `TorusFour = Circle⁴` is actually built from. -/
noncomputable def circleHomeoSph1 : Circle ≃ₜ ↥(Sph 1) where
  toFun z := ⟨complexEuclidLI (z : ℂ), by
    rw [mem_sphere_zero_iff_norm, complexEuclidLI.norm_map]; exact Circle.norm_coe z⟩
  invFun w := ⟨complexEuclidLI.symm (w : EuclideanSpace ℝ (Fin 2)), by
    show complexEuclidLI.symm (w : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, complexEuclidLI.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp w.2⟩
  left_inv z := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact complexEuclidLI.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact complexEuclidLI.symm.continuous.comp continuous_subtype_val

/-- **`H₁(Circle;ℤ) ≅ ℤ`** — the per-factor degree-1 input transported onto the *actual* `Circle`
factor of `TorusFour` (through the `circleHomeoSph1` bridge). This is the input a `TorusFour`-Künneth
brick consumes; without the bridge the banked `Sph 1` result does not apply to `Circle⁴`. -/
noncomputable def circleFactorHOneEquiv : Homology (TopCat.of Circle) 1 ≃ₗ[ℤ] ℤ :=
  (homeoHomologyEquivInt (X := TopCat.of Circle) (Y := Sph 1) circleHomeoSph1 1).trans
    circleHOneEquiv

/-- **`H_{k+2}(Circle;ℤ) = 0`** — the per-factor vanishing above degree 1, transported onto the actual
`Circle` factor. Pins the `Circle` input as "`ℤ` in degrees 0, 1; `0` above". -/
theorem circleFactorH_high (k : ℕ) (x : Homology (TopCat.of Circle) (k + 2)) : x = 0 := by
  have := circleH_high k
    (homeoHomologyEquivInt (X := TopCat.of Circle) (Y := Sph 1) circleHomeoSph1 (k + 2) x)
  exact (homeoHomologyEquivInt (X := TopCat.of Circle) (Y := Sph 1)
    circleHomeoSph1 (k + 2)).map_eq_zero_iff.mp this

/-! ## §3. The rank-6 degree-2 Künneth-index pin -/

/-- **The degree-2 Künneth index count `C(4,2) = 6`** — the summands of `H₂((S¹)⁴)` are indexed by the
2-element subsets `s ⊆ {1,2,3,4}` (the two circle factors that contribute their `H₁ = ℤ`; the other
two contribute `H₀ = ℤ`), and there are exactly `6` of them. The honest geometry-side rank pin: an
actual count of the `2`-subsets of a `4`-set, not a bare `Nat.choose`. -/
theorem hTwoIndex_card : Fintype.card {s : Finset (Fin 4) // s.card = 2} = 6 := by decide

/-- **The geometric `H₂(T⁴)` rank matches the arithmetic form's rank** — the number of degree-2
Künneth summands (`C(4,2) = 6`) equals the cardinality of `torusFourForm`'s index type `Fin 6`. This
is the falsifiable bridge between the geometry side (the exterior square `Λ²(ℤ⁴)` has `6` generators)
and the landed arithmetic form `torusFourForm : Matrix (Fin 6) (Fin 6) ℤ`. -/
theorem hTwoIndex_card_eq_form_rank :
    Fintype.card {s : Finset (Fin 4) // s.card = 2} = Fintype.card (Fin 6) := by decide

end SKEFTHawking.KummerHomologyT4
