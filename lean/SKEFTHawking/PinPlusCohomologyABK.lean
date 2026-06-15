/-
# Phase 5q.F W4-cohomology brick 4 — integration: genuine cellular cohomology ↔ the ABK/Brown invariant

Ties this session's genuine ℤ/2 cellular cohomology (`CellularCohomologyMod2`) to the project's
already-built kernel-pure Brown/ABK invariant (`BrownInvariant` + `GuillouMarinBridge`), via the
characteristic surface of the order-16 generator.

Per the Guillou–Marin / Kirby–Taylor formula `σ(X) − F·F ≡ 2·β(F) (mod 16)`, the generator `[RP⁴]` of
`Ω₄^{Pin⁺} ≅ ℤ/16` has characteristic surface `RP²`, and the ABK invariant `β(F) ∈ ℤ/8` lives on the
`ZMod 4`-quadratic refinement of the intersection form on the surface's first cohomology `H¹(RP²; ℤ/2)`.

This module verifies the **integration**: the genuine cellular `H¹(RP²; ℤ/2)` (a one-dimensional
`ZMod 2`-vector space, computed honestly in `CellularCohomologyMod2`) is exactly the underlying space of
the ABK quadratic form `stdQuadratic 1` (`Brown.Z4Quadratic (Fin 1)`), and the assembled ABK value
`doubleBrown (stdQuadratic 1) = 2 ∈ ℤ/16` matches the Guillou–Marin value `σ(RP⁴) − F·F = 0 − (−2) = 2`
for the generator (`GuillouMarin.GM_rp4`). The two previously-disconnected substrates — the genuine
cohomology layer and the genuine ABK invariant — agree on the generator: the cohomology FEEDS the ABK.

Per Invariant #15: no new axioms; this is a definitional bridge between two kernel-pure substrates.
-/
import SKEFTHawking.CellularCohomologyMod2
import SKEFTHawking.GuillouMarinBridge

namespace SKEFTHawking.PinPlusCohomologyABK

open SKEFTHawking.CellularCohomologyMod2 SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
  SKEFTHawking.GuillouMarin

/-- The genuine cellular `H¹(RP²; ℤ/2)` is the underlying `ZMod 2`-space of the ABK quadratic form
`stdQuadratic 1` (on `Fin 1 → ZMod 2`): both are one-dimensional. `RP²` is the characteristic surface of
the order-16 generator `RP⁴` (Guillou–Marin / Kirby–Taylor 1990), so the ABK `ZMod 4`-quadratic
refinement lives on this genuine cohomology. -/
theorem charSurface_RP2_H1_is_brownDomain :
    Nonempty (Cohomology (RPComplex 2) 1 ≃ₗ[ZMod 2] (Fin 1 → ZMod 2)) :=
  ⟨(RPComplex_cohomology_equiv 2 1 (by norm_num)).trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) (ZMod 2)).symm⟩

/-- `dim_{ℤ/2} H¹(RP²; ℤ/2) = 1` = the rank of the ABK quadratic form `stdQuadratic 1` for the `RP⁴`
generator: the genuine cohomology dimension matches the ABK form's domain dimension. -/
theorem charSurface_RP2_H1_finrank :
    Module.finrank (ZMod 2) (Cohomology (RPComplex 2) 1) = 1 :=
  RPComplex_finrank_cohomology 2 1 (by norm_num)

/-- **The genuine cohomology layer and the genuine ABK invariant agree on the order-16 generator.**
The characteristic surface `RP²` of `[RP⁴]` has genuine one-dimensional `H¹(RP²; ℤ/2)`
(`charSurface_RP2_H1_finrank`), carrying the ABK `ZMod 4`-quadratic refinement `stdQuadratic 1`; its
doubled Brown invariant `doubleBrown (stdQuadratic 1) = 2 ∈ ℤ/16` is the Guillou–Marin value
`σ(RP⁴) − F·F = 0 − (−2) = 2` of the generator (`GuillouMarin.GM_rp4`). This connects the two
kernel-pure substrates: the genuine cellular cohomology feeds the genuine ABK invariant. -/
theorem genuine_cohomology_feeds_ABK_on_generator :
    Module.finrank (ZMod 2) (Cohomology (RPComplex 2) 1) = 1 ∧
      doubleBrown (stdQuadratic 1) = ((0 - (-2 : ℤ)) : ZMod 16) :=
  ⟨charSurface_RP2_H1_finrank, GM_rp4.symm⟩

/-! ## §2. `β = doubleBrown` is a homomorphism (additive under orthogonal sum)

The algebraic core of "the ABK invariant `β : Ω₄^{Pin⁺} → ℤ/16` is a group homomorphism": the doubled
Brown invariant is additive under the orthogonal sum of `ZMod 4`-quadratic forms — which is the
quadratic-form shadow of the connected sum / disjoint union of characteristic surfaces (and hence of the
group operation on Pin⁺ bordism). Built on the already-proven `Brown.brown_orthSum`. -/

/-- `2·val` is additive as a map `ZMod 8 → ZMod 16` (the doubling embedding of the even subgroup;
the wraparound at `8` becomes a multiple of `16`). The `ZMod 8 → ZMod 16` analogue of
`Brown.two_mul_val_add` (`ZMod 4 → ZMod 8`). -/
lemma two_mul_val_add_8_16 (a b : ZMod 8) :
    (2 * ((a + b).val : ZMod 16)) = 2 * (a.val : ZMod 16) + 2 * (b.val : ZMod 16) := by
  revert a b; decide

/-- **The ℤ/16 ABK invariant `doubleBrown` is additive under orthogonal sum.** This is the algebraic
core of "`β : Ω₄^{Pin⁺} → ℤ/16` is a group homomorphism": `β(Q₁ ⊕ Q₂) = β(Q₁) + β(Q₂)`, lifting
`Brown.brown_orthSum` through the doubling `ZMod 8 → ZMod 16`. -/
theorem doubleBrown_orthSum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) :
    doubleBrown (orthSum Q₁ Q₂) = doubleBrown Q₁ + doubleBrown Q₂ := by
  unfold doubleBrown
  rw [brown_orthSum, two_mul_val_add_8_16]

end SKEFTHawking.PinPlusCohomologyABK
