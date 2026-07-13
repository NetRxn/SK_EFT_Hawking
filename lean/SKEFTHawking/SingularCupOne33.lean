import Mathlib
import SKEFTHawking.SingularCohomologyMod2

/-!
# Phase 5q.F — the Steenrod cup-`1` product at degree `(3,3)` and `Sq² : H³ → H⁵`

This module builds the **Steenrod cup-`1` product** `⌣₁ : C³ × C³ → C⁵` on the in-tree singular
mod-`2` cochain complex (`SKEFTHawking.SingularCohomologyMod2`), mirroring the degree-`(2,2)` build
`cupOne22` in that file. Its load-bearing property is the **coboundary identity**
  `δ(a ⌣₁ b) = a ⌣ b + b ⌣ a`   (mod 2, for cocycles `a, b ∈ C³`),
proven by the direct Steenrod telescoping expanded into `ZMod 2` atoms on the `35` tetrahedral
`3`-faces of a `6`-simplex `τ`. Setting `a = b = x` gives `δ(x ⌣₁ x) = 0`, so `x ⌣₁ x` is a
`5`-cocycle and `Sq²[x] := [x ⌣₁ x] ∈ H⁵` is the sub-top Steenrod square on `H³` — the `(2,3)`-leg
Wu datum for a `5`-manifold.

The Steenrod `(3,3)` formula on a `5`-simplex `σ = [0,…,5]` is the three-term sum
  `(a ⌣₁ b)(σ) = a(σ|{0,3,4,5})·b(σ|{0,1,2,3}) + a(σ|{0,1,4,5})·b(σ|{1,2,3,4})`
              `+ a(σ|{0,1,2,5})·b(σ|{2,3,4,5})`.
-/

namespace SKEFTHawking.SingularCohomologyMod2

open CategoryTheory Opposite

variable {X : TopCat}

/-! ### The six cup-`1` `(3,3)` face inclusions `[3] ⟶ [5]`. -/

/-- cup-`1` `(3,3)` inclusion `[3] ⟶ [5]` onto vertices `{0,3,4,5}`. -/
def cuA0 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 3, 4, 5], by decide⟩

/-- cup-`1` `(3,3)` inclusion `[3] ⟶ [5]` onto vertices `{0,1,2,3}`. -/
def cuB0 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 3], by decide⟩

/-- cup-`1` `(3,3)` inclusion `[3] ⟶ [5]` onto vertices `{0,1,4,5}`. -/
def cuA1 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 4, 5], by decide⟩

/-- cup-`1` `(3,3)` inclusion `[3] ⟶ [5]` onto vertices `{1,2,3,4}`. -/
def cuB1 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![1, 2, 3, 4], by decide⟩

/-- cup-`1` `(3,3)` inclusion `[3] ⟶ [5]` onto vertices `{0,1,2,5}`. -/
def cuA2 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 5], by decide⟩

/-- cup-`1` `(3,3)` inclusion `[3] ⟶ [5]` onto vertices `{2,3,4,5}`. -/
def cuB2 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![2, 3, 4, 5], by decide⟩

/-- The **Steenrod cup-`1` product at degree `(3,3)`** `⌣₁ : C³ × C³ → C⁵`,
`(a ⌣₁ b)(σ) = a(σ|{0,3,4,5})·b(σ|{0,1,2,3}) + a(σ|{0,1,4,5})·b(σ|{1,2,3,4})`
`+ a(σ|{0,1,2,5})·b(σ|{2,3,4,5})` (the three-term `j=0,1,2` sum). The chain homotopy realising
graded commutativity of the cup product in degree `3`. -/
noncomputable def cupOne33 (a b : SingularCochain X 3) : SingularCochain X 5 :=
  fun σ =>
    a ((TopCat.toSSet.obj X).map cuA0.op σ) * b ((TopCat.toSSet.obj X).map cuB0.op σ)
    + a ((TopCat.toSSet.obj X).map cuA1.op σ) * b ((TopCat.toSSet.obj X).map cuB1.op σ)
    + a ((TopCat.toSSet.obj X).map cuA2.op σ) * b ((TopCat.toSSet.obj X).map cuB2.op σ)

/-- Left-additivity of the cup-`1` product. -/
theorem cupOne33_add_left (a₁ a₂ b : SingularCochain X 3) :
    cupOne33 (a₁ + a₂) b = cupOne33 a₁ b + cupOne33 a₂ b := by
  funext σ; simp only [cupOne33, Pi.add_apply]; ring

/-- Right-additivity of the cup-`1` product. -/
theorem cupOne33_add_right (a b₁ b₂ : SingularCochain X 3) :
    cupOne33 a (b₁ + b₂) = cupOne33 a b₁ + cupOne33 a b₂ := by
  funext σ; simp only [cupOne33, Pi.add_apply]; ring

/-! ### The tetrahedral atom inclusions `[3] ⟶ [6]`
Every `3`-face of a singular `6`-simplex is a restriction along one of the strictly monotone
`[3] ⟶ [6]`. We name `tetIJKL` the one selecting vertices `{I,J,K,L}`. -/

/-- `[3] ⟶ [6]` selecting `{0,1,2,3}`. -/
def tet0123 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 3], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,1,2,4}`. -/
def tet0124 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 4], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,1,2,5}`. -/
def tet0125 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 5], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,1,2,6}`. -/
def tet0126 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,1,3,4}`. -/
def tet0134 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 3, 4], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,1,3,6}`. -/
def tet0136 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 3, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,1,4,5}`. -/
def tet0145 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 4, 5], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,1,4,6}`. -/
def tet0146 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 4, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,1,5,6}`. -/
def tet0156 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 5, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,2,3,4}`. -/
def tet0234 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 2, 3, 4], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,2,3,6}`. -/
def tet0236 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 2, 3, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,2,5,6}`. -/
def tet0256 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 2, 5, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,3,4,5}`. -/
def tet0345 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 3, 4, 5], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,3,4,6}`. -/
def tet0346 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 3, 4, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,3,5,6}`. -/
def tet0356 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 3, 5, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{0,4,5,6}`. -/
def tet0456 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 4, 5, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{1,2,3,4}`. -/
def tet1234 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![1, 2, 3, 4], by decide⟩

/-- `[3] ⟶ [6]` selecting `{1,2,3,5}`. -/
def tet1235 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![1, 2, 3, 5], by decide⟩

/-- `[3] ⟶ [6]` selecting `{1,2,3,6}`. -/
def tet1236 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![1, 2, 3, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{1,2,4,5}`. -/
def tet1245 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![1, 2, 4, 5], by decide⟩

/-- `[3] ⟶ [6]` selecting `{1,2,5,6}`. -/
def tet1256 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![1, 2, 5, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{1,3,4,5}`. -/
def tet1345 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![1, 3, 4, 5], by decide⟩

/-- `[3] ⟶ [6]` selecting `{1,4,5,6}`. -/
def tet1456 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![1, 4, 5, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{2,3,4,5}`. -/
def tet2345 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![2, 3, 4, 5], by decide⟩

/-- `[3] ⟶ [6]` selecting `{2,3,4,6}`. -/
def tet2346 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![2, 3, 4, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{2,3,5,6}`. -/
def tet2356 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![2, 3, 5, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{2,4,5,6}`. -/
def tet2456 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![2, 4, 5, 6], by decide⟩

/-- `[3] ⟶ [6]` selecting `{3,4,5,6}`. -/
def tet3456 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![3, 4, 5, 6], by decide⟩

/-! ### The seven codimension-`2` pentachoron inclusions `[4] ⟶ [6]` (cocycle carriers). -/

/-- `[4] ⟶ [6]` selecting `{0,3,4,5,6}` (cocycle carrier `A0`). -/
def pen03456 : SimplexCategory.mk 4 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 3, 4, 5, 6], by decide⟩

/-- `[4] ⟶ [6]` selecting `{0,1,4,5,6}` (cocycle carrier `A1`). -/
def pen01456 : SimplexCategory.mk 4 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 4, 5, 6], by decide⟩

/-- `[4] ⟶ [6]` selecting `{0,1,2,5,6}` (cocycle carrier `A2`). -/
def pen01256 : SimplexCategory.mk 4 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 5, 6], by decide⟩

/-- `[4] ⟶ [6]` selecting `{0,1,2,3,6}` (cocycle carrier `A3`). -/
def pen01236 : SimplexCategory.mk 4 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 3, 6], by decide⟩

/-- `[4] ⟶ [6]` selecting `{0,1,2,3,4}` (cocycle carrier `B0`). -/
def pen01234 : SimplexCategory.mk 4 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 3, 4], by decide⟩

/-- `[4] ⟶ [6]` selecting `{1,2,3,4,5}` (cocycle carrier `B1`). -/
def pen12345 : SimplexCategory.mk 4 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![1, 2, 3, 4, 5], by decide⟩

/-- `[4] ⟶ [6]` selecting `{2,3,4,5,6}` (cocycle carrier `B2`). -/
def pen23456 : SimplexCategory.mk 4 ⟶ SimplexCategory.mk 6 :=
  SimplexCategory.mkHom ⟨![2, 3, 4, 5, 6], by decide⟩

/-! ### The seven face-expansions of `cupOne33 a b (∂ᵢτ)`
For a `6`-simplex `τ` and each vertex `i ∈ {0,…,6}`, `cupOne33 a b` at the face `∂ᵢτ` expands via the
three-term Steenrod formula and the decidable face-composition identities `(cuXj ≫ δᵢ) = tetIJKL`. -/

variable (a b : SingularCochain X 3)
  (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (5 + 1))))

/-- Face expansion at `i = 0`. -/
theorem cupOne33_face0 :
    cupOne33 a b (face (0 : Fin 7) τ)
      = a ((TopCat.toSSet.obj X).map tet1456.op τ) * b ((TopCat.toSSet.obj X).map tet1234.op τ)
        + a ((TopCat.toSSet.obj X).map tet1256.op τ) * b ((TopCat.toSSet.obj X).map tet2345.op τ)
        + a ((TopCat.toSSet.obj X).map tet1236.op τ) * b ((TopCat.toSSet.obj X).map tet3456.op τ) := by
  unfold cupOne33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cuA0 ≫ SimplexCategory.δ (0 : Fin 7) = tet1456 from by decide,
    show cuB0 ≫ SimplexCategory.δ (0 : Fin 7) = tet1234 from by decide,
    show cuA1 ≫ SimplexCategory.δ (0 : Fin 7) = tet1256 from by decide,
    show cuB1 ≫ SimplexCategory.δ (0 : Fin 7) = tet2345 from by decide,
    show cuA2 ≫ SimplexCategory.δ (0 : Fin 7) = tet1236 from by decide,
    show cuB2 ≫ SimplexCategory.δ (0 : Fin 7) = tet3456 from by decide]

/-- Face expansion at `i = 1`. -/
theorem cupOne33_face1 :
    cupOne33 a b (face (1 : Fin 7) τ)
      = a ((TopCat.toSSet.obj X).map tet0456.op τ) * b ((TopCat.toSSet.obj X).map tet0234.op τ)
        + a ((TopCat.toSSet.obj X).map tet0256.op τ) * b ((TopCat.toSSet.obj X).map tet2345.op τ)
        + a ((TopCat.toSSet.obj X).map tet0236.op τ) * b ((TopCat.toSSet.obj X).map tet3456.op τ) := by
  unfold cupOne33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cuA0 ≫ SimplexCategory.δ (1 : Fin 7) = tet0456 from by decide,
    show cuB0 ≫ SimplexCategory.δ (1 : Fin 7) = tet0234 from by decide,
    show cuA1 ≫ SimplexCategory.δ (1 : Fin 7) = tet0256 from by decide,
    show cuB1 ≫ SimplexCategory.δ (1 : Fin 7) = tet2345 from by decide,
    show cuA2 ≫ SimplexCategory.δ (1 : Fin 7) = tet0236 from by decide,
    show cuB2 ≫ SimplexCategory.δ (1 : Fin 7) = tet3456 from by decide]

/-- Face expansion at `i = 2`. -/
theorem cupOne33_face2 :
    cupOne33 a b (face (2 : Fin 7) τ)
      = a ((TopCat.toSSet.obj X).map tet0456.op τ) * b ((TopCat.toSSet.obj X).map tet0134.op τ)
        + a ((TopCat.toSSet.obj X).map tet0156.op τ) * b ((TopCat.toSSet.obj X).map tet1345.op τ)
        + a ((TopCat.toSSet.obj X).map tet0136.op τ) * b ((TopCat.toSSet.obj X).map tet3456.op τ) := by
  unfold cupOne33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cuA0 ≫ SimplexCategory.δ (2 : Fin 7) = tet0456 from by decide,
    show cuB0 ≫ SimplexCategory.δ (2 : Fin 7) = tet0134 from by decide,
    show cuA1 ≫ SimplexCategory.δ (2 : Fin 7) = tet0156 from by decide,
    show cuB1 ≫ SimplexCategory.δ (2 : Fin 7) = tet1345 from by decide,
    show cuA2 ≫ SimplexCategory.δ (2 : Fin 7) = tet0136 from by decide,
    show cuB2 ≫ SimplexCategory.δ (2 : Fin 7) = tet3456 from by decide]

/-- Face expansion at `i = 3`. -/
theorem cupOne33_face3 :
    cupOne33 a b (face (3 : Fin 7) τ)
      = a ((TopCat.toSSet.obj X).map tet0456.op τ) * b ((TopCat.toSSet.obj X).map tet0124.op τ)
        + a ((TopCat.toSSet.obj X).map tet0156.op τ) * b ((TopCat.toSSet.obj X).map tet1245.op τ)
        + a ((TopCat.toSSet.obj X).map tet0126.op τ) * b ((TopCat.toSSet.obj X).map tet2456.op τ) := by
  unfold cupOne33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cuA0 ≫ SimplexCategory.δ (3 : Fin 7) = tet0456 from by decide,
    show cuB0 ≫ SimplexCategory.δ (3 : Fin 7) = tet0124 from by decide,
    show cuA1 ≫ SimplexCategory.δ (3 : Fin 7) = tet0156 from by decide,
    show cuB1 ≫ SimplexCategory.δ (3 : Fin 7) = tet1245 from by decide,
    show cuA2 ≫ SimplexCategory.δ (3 : Fin 7) = tet0126 from by decide,
    show cuB2 ≫ SimplexCategory.δ (3 : Fin 7) = tet2456 from by decide]

/-- Face expansion at `i = 4`. -/
theorem cupOne33_face4 :
    cupOne33 a b (face (4 : Fin 7) τ)
      = a ((TopCat.toSSet.obj X).map tet0356.op τ) * b ((TopCat.toSSet.obj X).map tet0123.op τ)
        + a ((TopCat.toSSet.obj X).map tet0156.op τ) * b ((TopCat.toSSet.obj X).map tet1235.op τ)
        + a ((TopCat.toSSet.obj X).map tet0126.op τ) * b ((TopCat.toSSet.obj X).map tet2356.op τ) := by
  unfold cupOne33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cuA0 ≫ SimplexCategory.δ (4 : Fin 7) = tet0356 from by decide,
    show cuB0 ≫ SimplexCategory.δ (4 : Fin 7) = tet0123 from by decide,
    show cuA1 ≫ SimplexCategory.δ (4 : Fin 7) = tet0156 from by decide,
    show cuB1 ≫ SimplexCategory.δ (4 : Fin 7) = tet1235 from by decide,
    show cuA2 ≫ SimplexCategory.δ (4 : Fin 7) = tet0126 from by decide,
    show cuB2 ≫ SimplexCategory.δ (4 : Fin 7) = tet2356 from by decide]

/-- Face expansion at `i = 5`. -/
theorem cupOne33_face5 :
    cupOne33 a b (face (5 : Fin 7) τ)
      = a ((TopCat.toSSet.obj X).map tet0346.op τ) * b ((TopCat.toSSet.obj X).map tet0123.op τ)
        + a ((TopCat.toSSet.obj X).map tet0146.op τ) * b ((TopCat.toSSet.obj X).map tet1234.op τ)
        + a ((TopCat.toSSet.obj X).map tet0126.op τ) * b ((TopCat.toSSet.obj X).map tet2346.op τ) := by
  unfold cupOne33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cuA0 ≫ SimplexCategory.δ (5 : Fin 7) = tet0346 from by decide,
    show cuB0 ≫ SimplexCategory.δ (5 : Fin 7) = tet0123 from by decide,
    show cuA1 ≫ SimplexCategory.δ (5 : Fin 7) = tet0146 from by decide,
    show cuB1 ≫ SimplexCategory.δ (5 : Fin 7) = tet1234 from by decide,
    show cuA2 ≫ SimplexCategory.δ (5 : Fin 7) = tet0126 from by decide,
    show cuB2 ≫ SimplexCategory.δ (5 : Fin 7) = tet2346 from by decide]

/-- Face expansion at `i = 6`. -/
theorem cupOne33_face6 :
    cupOne33 a b (face (6 : Fin 7) τ)
      = a ((TopCat.toSSet.obj X).map tet0345.op τ) * b ((TopCat.toSSet.obj X).map tet0123.op τ)
        + a ((TopCat.toSSet.obj X).map tet0145.op τ) * b ((TopCat.toSSet.obj X).map tet1234.op τ)
        + a ((TopCat.toSSet.obj X).map tet0125.op τ) * b ((TopCat.toSSet.obj X).map tet2345.op τ) := by
  unfold cupOne33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cuA0 ≫ SimplexCategory.δ (6 : Fin 7) = tet0345 from by decide,
    show cuB0 ≫ SimplexCategory.δ (6 : Fin 7) = tet0123 from by decide,
    show cuA1 ≫ SimplexCategory.δ (6 : Fin 7) = tet0145 from by decide,
    show cuB1 ≫ SimplexCategory.δ (6 : Fin 7) = tet1234 from by decide,
    show cuA2 ≫ SimplexCategory.δ (6 : Fin 7) = tet0125 from by decide,
    show cuB2 ≫ SimplexCategory.δ (6 : Fin 7) = tet2345 from by decide]

/-! ### The seven codimension-`2` cocycle relations
For `f ∈ C³` with `δf = 0`, on each pentachoron `4`-face `τ|S` (`S` a `5`-subset) the mod-`2` sum of
`f` over the five tetrahedral `3`-faces vanishes. Each is `congrFun (δf = 0)` on the restriction
`τ|S`, expanded via `Fin.sum_univ_five` and the decidable composites `(δₖ ≫ penS) = tetIJKL`. -/

/-- Cocycle relation on the pentachoron `{0,3,4,5,6}`. -/
theorem cocycle_penta_A0 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tet3456.op τ)
      + f ((TopCat.toSSet.obj X).map tet0456.op τ)
      + f ((TopCat.toSSet.obj X).map tet0356.op τ)
      + f ((TopCat.toSSet.obj X).map tet0346.op τ)
      + f ((TopCat.toSSet.obj X).map tet0345.op τ) = 0 := by
  have h : coboundary X 3 f ((TopCat.toSSet.obj X).map pen03456.op τ) = 0 := congrFun hf _
  rw [coboundary_apply, Fin.sum_univ_five] at h
  unfold face at h
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 5) ≫ pen03456 = tet3456 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ pen03456 = tet0456 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ pen03456 = tet0356 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ pen03456 = tet0346 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ pen03456 = tet0345 from by decide] at h
  exact h

/-- Cocycle relation on the pentachoron `{0,1,4,5,6}`. -/
theorem cocycle_penta_A1 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tet1456.op τ)
      + f ((TopCat.toSSet.obj X).map tet0456.op τ)
      + f ((TopCat.toSSet.obj X).map tet0156.op τ)
      + f ((TopCat.toSSet.obj X).map tet0146.op τ)
      + f ((TopCat.toSSet.obj X).map tet0145.op τ) = 0 := by
  have h : coboundary X 3 f ((TopCat.toSSet.obj X).map pen01456.op τ) = 0 := congrFun hf _
  rw [coboundary_apply, Fin.sum_univ_five] at h
  unfold face at h
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 5) ≫ pen01456 = tet1456 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ pen01456 = tet0456 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ pen01456 = tet0156 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ pen01456 = tet0146 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ pen01456 = tet0145 from by decide] at h
  exact h

/-- Cocycle relation on the pentachoron `{0,1,2,5,6}`. -/
theorem cocycle_penta_A2 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tet1256.op τ)
      + f ((TopCat.toSSet.obj X).map tet0256.op τ)
      + f ((TopCat.toSSet.obj X).map tet0156.op τ)
      + f ((TopCat.toSSet.obj X).map tet0126.op τ)
      + f ((TopCat.toSSet.obj X).map tet0125.op τ) = 0 := by
  have h : coboundary X 3 f ((TopCat.toSSet.obj X).map pen01256.op τ) = 0 := congrFun hf _
  rw [coboundary_apply, Fin.sum_univ_five] at h
  unfold face at h
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 5) ≫ pen01256 = tet1256 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ pen01256 = tet0256 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ pen01256 = tet0156 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ pen01256 = tet0126 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ pen01256 = tet0125 from by decide] at h
  exact h

/-- Cocycle relation on the pentachoron `{0,1,2,3,6}`. -/
theorem cocycle_penta_A3 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tet1236.op τ)
      + f ((TopCat.toSSet.obj X).map tet0236.op τ)
      + f ((TopCat.toSSet.obj X).map tet0136.op τ)
      + f ((TopCat.toSSet.obj X).map tet0126.op τ)
      + f ((TopCat.toSSet.obj X).map tet0123.op τ) = 0 := by
  have h : coboundary X 3 f ((TopCat.toSSet.obj X).map pen01236.op τ) = 0 := congrFun hf _
  rw [coboundary_apply, Fin.sum_univ_five] at h
  unfold face at h
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 5) ≫ pen01236 = tet1236 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ pen01236 = tet0236 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ pen01236 = tet0136 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ pen01236 = tet0126 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ pen01236 = tet0123 from by decide] at h
  exact h

/-- Cocycle relation on the pentachoron `{0,1,2,3,4}`. -/
theorem cocycle_penta_B0 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tet1234.op τ)
      + f ((TopCat.toSSet.obj X).map tet0234.op τ)
      + f ((TopCat.toSSet.obj X).map tet0134.op τ)
      + f ((TopCat.toSSet.obj X).map tet0124.op τ)
      + f ((TopCat.toSSet.obj X).map tet0123.op τ) = 0 := by
  have h : coboundary X 3 f ((TopCat.toSSet.obj X).map pen01234.op τ) = 0 := congrFun hf _
  rw [coboundary_apply, Fin.sum_univ_five] at h
  unfold face at h
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 5) ≫ pen01234 = tet1234 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ pen01234 = tet0234 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ pen01234 = tet0134 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ pen01234 = tet0124 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ pen01234 = tet0123 from by decide] at h
  exact h

/-- Cocycle relation on the pentachoron `{1,2,3,4,5}`. -/
theorem cocycle_penta_B1 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tet2345.op τ)
      + f ((TopCat.toSSet.obj X).map tet1345.op τ)
      + f ((TopCat.toSSet.obj X).map tet1245.op τ)
      + f ((TopCat.toSSet.obj X).map tet1235.op τ)
      + f ((TopCat.toSSet.obj X).map tet1234.op τ) = 0 := by
  have h : coboundary X 3 f ((TopCat.toSSet.obj X).map pen12345.op τ) = 0 := congrFun hf _
  rw [coboundary_apply, Fin.sum_univ_five] at h
  unfold face at h
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 5) ≫ pen12345 = tet2345 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ pen12345 = tet1345 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ pen12345 = tet1245 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ pen12345 = tet1235 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ pen12345 = tet1234 from by decide] at h
  exact h

/-- Cocycle relation on the pentachoron `{2,3,4,5,6}`. -/
theorem cocycle_penta_B2 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tet3456.op τ)
      + f ((TopCat.toSSet.obj X).map tet2456.op τ)
      + f ((TopCat.toSSet.obj X).map tet2356.op τ)
      + f ((TopCat.toSSet.obj X).map tet2346.op τ)
      + f ((TopCat.toSSet.obj X).map tet2345.op τ) = 0 := by
  have h : coboundary X 3 f ((TopCat.toSSet.obj X).map pen23456.op τ) = 0 := congrFun hf _
  rw [coboundary_apply, Fin.sum_univ_five] at h
  unfold face at h
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 5) ≫ pen23456 = tet3456 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ pen23456 = tet2456 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ pen23456 = tet2356 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ pen23456 = tet2346 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ pen23456 = tet2345 from by decide] at h
  exact h

/-! ### The cup-`1` coboundary identity at degree `(3,3)`

The Steenrod homotopy identity for cocycles: `δ(a ⌣₁ b) = a ⌣ b + b ⌣ a` (mod 2). The left side
sums the seven face-expansions `cupOne33 a b (∂ᵢτ)` (`21` products on `3`-faces of `τ`); the right
side is the two cup terms `a(τ|{0,1,2,3})·b(τ|{3,4,5,6}) + b(τ|{0,1,2,3})·a(τ|{3,4,5,6})`. The `21`
products collapse to the two cup terms using the seven cocycle relations (four for `a`, three for
`b`) — the exact Steenrod telescoping certificate `Σⱼ (δa ⌣₁ b)ⱼ + (a ⌣₁ δb)ⱼ`, a pure `ZMod 2`
computation. The degree-`3` analogue of `cupOne22_coboundary`. -/
theorem cupOne33_coboundary (a b : SingularCochain X 3)
    (ha : coboundaryₗ X 3 a = 0) (hb : coboundaryₗ X 3 b = 0) :
    coboundary X 5 (cupOne33 a b) = cup a b + cup b a := by
  funext τ
  have hA := cocycle_penta_A0 τ a ha
  have hB := cocycle_penta_A1 τ a ha
  have hC := cocycle_penta_A2 τ a ha
  have hD := cocycle_penta_A3 τ a ha
  have hP := cocycle_penta_B0 τ b hb
  have hQ := cocycle_penta_B1 τ b hb
  have hR := cocycle_penta_B2 τ b hb
  rw [coboundary_apply, Fin.sum_univ_seven, cupOne33_face0, cupOne33_face1, cupOne33_face2,
    cupOne33_face3, cupOne33_face4, cupOne33_face5, cupOne33_face6]
  show _ = (cup a b + cup b a) τ
  rw [Pi.add_apply, cup_apply, cup_apply]
  unfold frontFace backFace
  rw [show frontIncl 3 3 = tet0123 from by decide, show backIncl 3 3 = tet3456 from by decide]
  set b0123 := b ((TopCat.toSSet.obj X).map tet0123.op τ)
  set b1234 := b ((TopCat.toSSet.obj X).map tet1234.op τ)
  set b2345 := b ((TopCat.toSSet.obj X).map tet2345.op τ)
  set b3456 := b ((TopCat.toSSet.obj X).map tet3456.op τ)
  set a0456 := a ((TopCat.toSSet.obj X).map tet0456.op τ)
  set a0156 := a ((TopCat.toSSet.obj X).map tet0156.op τ)
  set a0126 := a ((TopCat.toSSet.obj X).map tet0126.op τ)
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    b0123 * hA + b1234 * hB + b2345 * hC + b3456 * hD
    + a0456 * hP + a0156 * hQ + a0126 * hR

/-! ### The diagonal `x ⌣₁ x` is a `5`-cocycle, and the cocycle-level Steenrod square

For a `3`-cocycle `x`, `δ(x ⌣₁ x) = x ⌣ x + x ⌣ x = 0` (mod 2) by `cupOne33_coboundary` at `a=b=x`.
So `x ⌣₁ x ∈ ker δ⁵` and its class `[x ⌣₁ x] ∈ H⁵` is the value the sub-top Steenrod square `Sq²`
takes on `[x] ∈ H³` — the `(2,3)`-leg `5`-manifold Wu datum. -/
theorem cupOne33_diag_cocycle (x : SingularCochain X 3) (hx : coboundaryₗ X 3 x = 0) :
    coboundaryₗ X 5 (cupOne33 x x) = 0 := by
  have h := cupOne33_coboundary x x hx hx
  show coboundary X 5 (cupOne33 x x) = 0
  rw [h]; funext τ; simp only [Pi.add_apply, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _

/-- The **cocycle-level Steenrod square** `Sq² : Z³ → Z⁵` on singular `ℤ/2` cocycles,
`x ↦ x ⌣₁ x` (a `5`-cocycle by `cupOne33_diag_cocycle`). This is the sub-top Steenrod square before
descent to cohomology; it is a *quadratic* (not linear) map of cocycles — the cross term
`x ⌣₁ y + y ⌣₁ x` becomes a coboundary only after passing to `H⁵` (via the cup-`2` product). -/
noncomputable def sq2Cocycle (x : LinearMap.ker (coboundaryₗ X 3)) :
    LinearMap.ker (coboundaryₗ X 5) :=
  ⟨cupOne33 x.1 x.1, cupOne33_diag_cocycle x.1 (LinearMap.mem_ker.mp x.2)⟩

/-! ### The cup product on cohomology `H³ × H³ → H⁶` and its graded commutativity

The degree-`(3,3)` analogue of `cupH24`. `cupH33` is the cup pairing `H³(X) × H³(X) → H⁶(X)`; its
symmetry `cupH33_symm` (graded commutativity in degree `3`) is the direct `H`-level payoff of the
cup-`1` coboundary identity `cupOne33_coboundary`: `δ(a ⌣₁ b) = a ⌣ b + b ⌣ a` makes `a ⌣ b` and
`b ⌣ a` cohomologous. Mirrors the `(2,2)→4` construction with degrees bumped `2→3`, `4→6`. -/

/-- **Coboundary ⌣ cocycle is a coboundary** (left argument, degrees `2,3`): if `g : C³` is a cocycle
then `δa ⌣ g = δ(a ⌣ g)` for `a : C²`. The degree-`(2,3)` mirror of `cup_coboundary_left_1_2`, the
left-descent that kills `H³`-coboundaries in the left argument of `cupH33`. -/
theorem cup_coboundary_left_2_3 (a : SingularCochain X 2) (g : SingularCochain X 3)
    (hg : coboundaryₗ X 3 g = 0) :
    coboundaryₗ X (2 + 3) (cup a g) = cup (coboundaryₗ X 2 a) g := by
  funext τ
  show coboundary X (2 + 3) (cup a g) τ = cup (coboundaryₗ X 2 a) g τ
  rw [coboundary_cup, cup_apply]
  have hg' : coboundary X 3 g (backSmall τ) = 0 := congrFun hg (backSmall τ)
  rw [hg', mul_zero, add_zero]
  rfl

/-- For a fixed degree-`3` cocycle `fc`, cup-with-`fc` descends to a linear map `H³ → H⁶`. -/
noncomputable def cupRightH33 (fc : LinearMap.ker (coboundaryₗ X 3)) :
    Cohomology X 3 →ₗ[ZMod 2] Cohomology X 6 :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((cupₗ 3 3 fc.1).domRestrict (LinearMap.ker (coboundaryₗ X 3))).codRestrict
        (LinearMap.ker (coboundaryₗ X 6)) fun gc => by
          rw [LinearMap.mem_ker]
          exact cup_cocycle fc.1 gc.1 (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)))
    (by
      intro gc hgc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hgc
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, cupₗ_apply]
      show cup fc.1 gc.1 ∈ LinearMap.range (coboundaryₗ X 5)
      obtain ⟨b, hb⟩ := hgc
      refine ⟨cup fc.1 b, ?_⟩
      rw [← hb]
      exact cup_coboundary_right fc.1 b (LinearMap.mem_ker.mp fc.2))

/-- The computation rule for `cupRightH33` on a representative cocycle `gc`. -/
theorem cupRightH33_apply_mk (fc gc : LinearMap.ker (coboundaryₗ X 3)) :
    cupRightH33 fc (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨cup fc.1 gc.1, cup_cocycle fc.1 gc.1
          (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X 6)) := by
  rfl

/-- **The cup product on `H³ × H³ → H⁶`** — a genuine `ℤ/2`-bilinear map. Well-defined:
`cup_cocycle` lands it in cocycles; `cup_coboundary_right`/`cup_coboundary_left_2_3` kill coboundaries
in each argument. The degree-`(3,3)` analogue of `cupH24`. -/
noncomputable def cupH33 : Cohomology X 3 →ₗ[ZMod 2] Cohomology X 3 →ₗ[ZMod 2] Cohomology X 6 :=
  Submodule.liftQ _
    { toFun := cupRightH33
      map_add' := fun fc fc' => by
        ext x
        obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        simp only [LinearMap.add_apply, cupRightH33_apply_mk]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_add, cup_add_left]
      map_smul' := fun c fc => by
        ext x
        obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        simp only [LinearMap.smul_apply, RingHom.id_apply, cupRightH33_apply_mk]
        congr 1
        apply Subtype.ext
        simp only [SetLike.val_smul, cup_smul_left] }
    (by
      intro fc hfc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hfc
      rw [LinearMap.mem_ker]
      ext x
      obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.zero_apply]
      change cupRightH33 fc (Submodule.Quotient.mk gc) = 0
      rw [cupRightH33_apply_mk]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
      show cup fc.1 gc.1 ∈ LinearMap.range (coboundaryₗ X 5)
      obtain ⟨a, ha⟩ := hfc
      refine ⟨cup a gc.1, ?_⟩
      rw [← ha]
      exact cup_coboundary_left_2_3 a gc.1 (LinearMap.mem_ker.mp gc.2))

@[simp] theorem cupH33_mk_mk (fc gc : LinearMap.ker (coboundaryₗ X 3)) :
    cupH33 (Submodule.Quotient.mk fc) (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨cup fc.1 gc.1, cup_cocycle fc.1 gc.1
          (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X 6)) := by
  show cupRightH33 fc (Submodule.Quotient.mk gc) = _
  exact cupRightH33_apply_mk fc gc

/-- **`cupH33` is graded-commutative** — `[a ⌣ b] = [b ⌣ a]` in `H⁶(X;ℤ/2)`. The witness is the
Steenrod cup-`1` product `cupOne33`, whose coboundary is `a ⌣ b + b ⌣ a` for cocycle representatives
(`cupOne33_coboundary`). The degree-`3` analogue of `cupH24_symm` — the direct `H`-level payoff of the
`(3,3)` cup-`1` construction. -/
theorem cupH33_symm (x y : Cohomology X 3) : cupH33 x y = cupH33 y x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [cupH33_mk_mk, cupH33_mk_mk]
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  show cup a.1 b.1 - cup b.1 a.1 ∈ LinearMap.range (coboundaryₗ X 5)
  refine ⟨cupOne33 a.1 b.1, ?_⟩
  show coboundary X 5 (cupOne33 a.1 b.1) = cup a.1 b.1 - cup b.1 a.1
  rw [cupOne33_coboundary a.1 b.1 (LinearMap.mem_ker.mp a.2) (LinearMap.mem_ker.mp b.2)]
  funext σ
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [CharTwo.sub_eq_add]

end SKEFTHawking.SingularCohomologyMod2
