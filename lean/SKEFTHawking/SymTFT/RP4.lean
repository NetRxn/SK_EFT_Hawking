/-
# Phase 6r-prime M3 — Real Projective Space RP⁴ (Layer A topological)

This module ships **RP⁴** (real projective 4-space) as a Mathlib-PR-quality
concrete `Type` via the antipodal Z₂ quotient of `S⁴ ⊂ ℝ⁵`.

**Layer A (this module)**: topological RP⁴ as `Quotient antipodalSetoidS4`
+ `TopologicalSpace`, `CompactSpace` instances + concrete non-empty witness.

**Layer B (sibling module `RP4Smooth.lean`)**: `T2Space`, covering-map
properties, `ChartedSpace + IsManifold` smooth structure via parallel
`MulAction`-based construction + `Homeomorph` cross-bridge to the Layer A
form. Layer B is shipped separately to keep Layer A's API surface stable
for downstream consumers (`StiefelWhitney.lean`, `Phase6rPrimeClose.lean`).

## Substantive content

For `S⁴ ⊂ ℝ⁵`, define the antipodal equivalence
```
x ≈ y  ⟺  x = y ∨ x = -y
```
as a `Setoid`. Then `RP4 := Quotient antipodalSetoidS4`, with:

- `TopologicalSpace RP4` (induced from the sphere via the quotient
  topology).
- `CompactSpace RP4` (quotient of a compact space is compact).
- `Nonempty RP4` witness via the north pole class.

## References

- Hatcher, *Algebraic Topology* §1.3 (definition of RP^n via sphere
  quotient).
- Kirby-Taylor 1990 (Pin⁺ bordism — RP⁴ is the generator).
- Mathlib `Mathlib.Geometry.Manifold.Instances.Sphere`.
- Mathlib `Mathlib.Analysis.Normed.Group.BallSphere`.
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Group.BallSphere

namespace SKEFTHawking.SymTFT

open Metric

/-! ## §1. The 4-sphere -/

/-- **`S4`** — the unit 4-sphere in `EuclideanSpace ℝ (Fin 5)`. -/
abbrev S4 : Set (EuclideanSpace ℝ (Fin 5)) := sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

/-! ## §2. The antipodal Setoid on S⁴ -/

/-- **`antipodalSetoidS4`** — the equivalence relation on the unit
4-sphere identifying antipodal points: `x ≈ y ⟺ x = y ∨ x = -y`.
This is the Z₂ quotient relation that builds RP⁴ from S⁴. -/
def antipodalSetoidS4 : Setoid S4 where
  r x y := x = y ∨ x = -y
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        intro x y h
        rcases h with rfl | h
        · exact Or.inl rfl
        · refine Or.inr ?_
          rw [h]
          exact (neg_neg _).symm
      trans := by
        intro x y z hxy hyz
        rcases hxy with rfl | hxy
        · exact hyz
        rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · refine Or.inl ?_
          rw [hxy, hyz]
          exact neg_neg _ }

/-! ## §3. RP⁴ as the quotient -/

/-- **`RP4`** — real projective space of dimension 4, realized as the
quotient of the 4-sphere by the antipodal equivalence relation. -/
def RP4 : Type := Quotient antipodalSetoidS4

/-- Quotient topology on `RP4`. -/
instance : TopologicalSpace RP4 :=
  inferInstanceAs (TopologicalSpace (Quotient antipodalSetoidS4))

/-- The canonical projection `S⁴ → RP⁴`. -/
def S4.toRP4 : S4 → RP4 := Quotient.mk _

theorem S4.toRP4_surjective : Function.Surjective S4.toRP4 :=
  Quotient.mk_surjective

/-- The canonical projection is continuous (it is the quotient map). -/
theorem S4.toRP4_continuous : Continuous S4.toRP4 :=
  continuous_quotient_mk'

/-! ## §4. CompactSpace + topology properties -/

/-- The 4-sphere as a subspace of EuclideanSpace ℝ (Fin 5) is compact. -/
instance S4.compactSpace : CompactSpace S4 :=
  inferInstanceAs (CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin 5)) 1))

/-- `RP4` is compact (quotient of a compact space). -/
instance RP4.compactSpace : CompactSpace RP4 := by
  refine ⟨?_⟩
  rw [show (Set.univ : Set RP4) = S4.toRP4 '' Set.univ by
    rw [Set.image_univ]; exact (Set.range_eq_univ.mpr S4.toRP4_surjective).symm]
  exact (CompactSpace.isCompact_univ).image S4.toRP4_continuous

/-! ## §5. Non-empty witness -/

/-- **`rp4_topologically_concretizes_pinPlusRP4`** — the topological
RP⁴ Type is non-empty, witnessed by the projection of the north pole. -/
theorem rp4_topologically_concretizes_pinPlusRP4 :
    Nonempty RP4 := by
  refine ⟨S4.toRP4 ?_⟩
  refine ⟨EuclideanSpace.single (0 : Fin 5) (1 : ℝ), ?_⟩
  simp [Metric.mem_sphere, EuclideanSpace.norm_single]

end SKEFTHawking.SymTFT
