import Mathlib
import SKEFTHawking.SingularCupOne33

/-!
# Phase 5q.F — the Steenrod cup-`2`/cup-`1`(2,3) legs and `Sq² : H³ → H⁵`

This module completes the sub-top Steenrod square `Sq² : H³(X;ℤ/2) → H⁵(X;ℤ/2)` (the `(2,3)`-leg
Wu datum for a `5`-manifold), building on the cup-`1` `(3,3)` product `cupOne33` and its coboundary
identity `δ(a ⌣₁ b) = a ⌣ b + b ⌣ a` (`SKEFTHawking.SingularCupOne33`).

The cocycle-level square `x ↦ x ⌣₁ x` (`sq2Cocycle`) is *quadratic*, and its descent to cohomology
needs two more Steenrod homotopies:

* **cup-`2` at `(3,3)`** `cupTwo33 : C³ × C³ → C⁴` (Steenrod's next higher homotopy `⌣₂`), with
  `δ(x ⌣₂ y) = x ⌣₁ y + y ⌣₁ x` (mod `2`, for cocycles) — the `⌣₁`-commutator killer. This both
  makes `Sq²` additive (`[x ⌣₁ y + y ⌣₁ x] = 0`) and supplies the `x ⌣₁ d + d ⌣₁ x = δ(x ⌣₂ d)`
  piece of the well-definedness cobounding.
* **cup-`1` at `(2,3)`** `cupOne23 : C² × C³ → C⁴`, with the Hirsch coboundary
  `δ(c ⌣₁ d) = (δc) ⌣₁ d + c ⌣ d + d ⌣ c` (mod `2`, for a cocycle `d`). Together with the plain
  cup Leibniz `δ(c ⌣ c) = c ⌣ d + d ⌣ c` this closes `d ⌣₁ d = δ(c ⌣₁ d + c ⌣ c)` (`d = δc`).

Both `⌣₂` and `⌣₁`(2,3) are the standard surjection-operad `(1,2,1,2)` / `(1,2,1)` interval-cut
formulas (only the non-degenerate/injective terms), on `4`-simplices — the `δ`-expansions live on the
`5`-simplex `τ = [0,…,5]`, with the products collapsing to the target via the six pentachoron
cocycle relations. The `[3] ⟶ [5]` tetrahedral atoms are named `tfIJKL` (distinct from
`SingularCupOne33`'s `[3] ⟶ [6]` `tetIJKL`).
-/

namespace SKEFTHawking.SingularCohomologyMod2

open CategoryTheory Opposite

variable {X : TopCat}

/-! ### The cup-`2` `(3,3)` building-block inclusions `[3] ⟶ [4]`
`cupTwo33` is the surjection-word `(1,2,1,2)` cup-`2`: on a `4`-simplex `σ = [0,…,4]` its four
non-degenerate interval-cut terms are
  `x(σ|{0,1,2,3})·y(σ|{0,1,3,4}) + x(σ|{0,2,3,4})·y(σ|{0,1,2,4})`
  `+ x(σ|{0,1,2,3})·y(σ|{1,2,3,4}) + x(σ|{0,1,3,4})·y(σ|{1,2,3,4})`. -/

/-- `[3] ⟶ [4]` selecting `{0,1,2,3}` (`x`-restriction, terms 1 & 3). -/
def cwx0123 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 4 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 3], by decide⟩
/-- `[3] ⟶ [4]` selecting `{0,2,3,4}` (`x`-restriction, term 2). -/
def cwx0234 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 4 :=
  SimplexCategory.mkHom ⟨![0, 2, 3, 4], by decide⟩
/-- `[3] ⟶ [4]` selecting `{0,1,3,4}` (`x`-restriction term 4 / `y`-restriction term 1). -/
def cwx0134 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 4 :=
  SimplexCategory.mkHom ⟨![0, 1, 3, 4], by decide⟩
/-- `[3] ⟶ [4]` selecting `{0,1,2,4}` (`y`-restriction, term 2). -/
def cwy0124 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 4 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 4], by decide⟩
/-- `[3] ⟶ [4]` selecting `{1,2,3,4}` (`y`-restriction, terms 3 & 4). -/
def cwy1234 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 4 :=
  SimplexCategory.mkHom ⟨![1, 2, 3, 4], by decide⟩

/-- The **Steenrod cup-`2` product at degree `(3,3)`** `⌣₂ : C³ × C³ → C⁴`, the surjection-word
`(1,2,1,2)` interval-cut formula (four non-degenerate terms). Its coboundary is the `⌣₁`-commutator
`x ⌣₁ y + y ⌣₁ x` (for cocycles), the next Steenrod homotopy above `cupOne33`. -/
noncomputable def cupTwo33 (x y : SingularCochain X 3) : SingularCochain X 4 :=
  fun σ =>
    x ((TopCat.toSSet.obj X).map cwx0123.op σ) * y ((TopCat.toSSet.obj X).map cwx0134.op σ)
    + x ((TopCat.toSSet.obj X).map cwx0234.op σ) * y ((TopCat.toSSet.obj X).map cwy0124.op σ)
    + x ((TopCat.toSSet.obj X).map cwx0123.op σ) * y ((TopCat.toSSet.obj X).map cwy1234.op σ)
    + x ((TopCat.toSSet.obj X).map cwx0134.op σ) * y ((TopCat.toSSet.obj X).map cwy1234.op σ)

/-- Left-additivity of the cup-`2` product. -/
theorem cupTwo33_add_left (x₁ x₂ y : SingularCochain X 3) :
    cupTwo33 (x₁ + x₂) y = cupTwo33 x₁ y + cupTwo33 x₂ y := by
  funext σ; simp only [cupTwo33, Pi.add_apply]; ring

/-- Right-additivity of the cup-`2` product. -/
theorem cupTwo33_add_right (x y₁ y₂ : SingularCochain X 3) :
    cupTwo33 x (y₁ + y₂) = cupTwo33 x y₁ + cupTwo33 x y₂ := by
  funext σ; simp only [cupTwo33, Pi.add_apply]; ring

/-! ### The cup-`1` `(2,3)` building-block inclusions
`cupOne23` is the surjection-word `(1,2,1)` cup-`1` at degrees `(2,3)` (`c` outer degree `2`, `d`
inner degree `3`): on a `4`-simplex `σ = [0,…,4]` its two non-degenerate terms are
  `c(σ|{0,3,4})·d(σ|{0,1,2,3}) + c(σ|{0,1,4})·d(σ|{1,2,3,4})`. -/

/-- `[2] ⟶ [4]` selecting `{0,3,4}` (`c`-restriction, term 1). -/
def cwc034 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 4 :=
  SimplexCategory.mkHom ⟨![0, 3, 4], by decide⟩
/-- `[2] ⟶ [4]` selecting `{0,1,4}` (`c`-restriction, term 2). -/
def cwc014 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 4 :=
  SimplexCategory.mkHom ⟨![0, 1, 4], by decide⟩

/-- The **Steenrod cup-`1` product at degree `(2,3)`** `⌣₁ : C² × C³ → C⁴`, the surjection-word
`(1,2,1)` interval-cut formula (two non-degenerate terms). Its Hirsch coboundary is
`δ(c ⌣₁ d) = (δc) ⌣₁ d + c ⌣ d + d ⌣ c` (for a cocycle `d`), the `(2,3)` mirror of `cupOne33`. -/
noncomputable def cupOne23 (c : SingularCochain X 2) (d : SingularCochain X 3) :
    SingularCochain X 4 :=
  fun σ =>
    c ((TopCat.toSSet.obj X).map cwc034.op σ) * d ((TopCat.toSSet.obj X).map cwx0123.op σ)
    + c ((TopCat.toSSet.obj X).map cwc014.op σ) * d ((TopCat.toSSet.obj X).map cwy1234.op σ)

/-! ### The fifteen tetrahedral atom inclusions `[3] ⟶ [5]`
Every `3`-face of a singular `5`-simplex `τ` is a restriction along one of the `C(6,4)=15` strictly
monotone `[3] ⟶ [5]`. `tetIJKL` selects vertices `{I,J,K,L} ⊂ {0,…,5}`. -/

/-- `[3] ⟶ [5]` selecting `{0,1,2,3}`. -/
def tf0123 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 3], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,1,2,4}`. -/
def tf0124 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 4], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,1,2,5}`. -/
def tf0125 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 2, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,1,3,4}`. -/
def tf0134 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 3, 4], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,1,3,5}`. -/
def tf0135 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 3, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,1,4,5}`. -/
def tf0145 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 4, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,2,3,4}`. -/
def tf0234 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 2, 3, 4], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,2,3,5}`. -/
def tf0235 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 2, 3, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,2,4,5}`. -/
def tf0245 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 2, 4, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{0,3,4,5}`. -/
def tf0345 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 3, 4, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{1,2,3,4}`. -/
def tf1234 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![1, 2, 3, 4], by decide⟩
/-- `[3] ⟶ [5]` selecting `{1,2,3,5}`. -/
def tf1235 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![1, 2, 3, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{1,2,4,5}`. -/
def tf1245 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![1, 2, 4, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{1,3,4,5}`. -/
def tf1345 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![1, 3, 4, 5], by decide⟩
/-- `[3] ⟶ [5]` selecting `{2,3,4,5}`. -/
def tf2345 : SimplexCategory.mk 3 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![2, 3, 4, 5], by decide⟩

/-! ### The six face-expansions of `cupTwo33 x y (∂ᵢτ)`
For a `5`-simplex `τ` and each vertex `i ∈ {0,…,5}`, `cupTwo33 x y` at the face `∂ᵢτ` expands via the
four-term `(1,2,1,2)` formula and the decidable face-composition identities `(cwXᵢ ≫ δᵢ) = tetIJKL`. -/

variable (x y : SingularCochain X 3)
  (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (4 + 1))))

/-- Face expansion at `i = 0`. -/
theorem cupTwo33_face0 :
    cupTwo33 x y (face (0 : Fin 6) τ)
      = x ((TopCat.toSSet.obj X).map tf1234.op τ) * y ((TopCat.toSSet.obj X).map tf1245.op τ)
        + x ((TopCat.toSSet.obj X).map tf1345.op τ) * y ((TopCat.toSSet.obj X).map tf1235.op τ)
        + x ((TopCat.toSSet.obj X).map tf1234.op τ) * y ((TopCat.toSSet.obj X).map tf2345.op τ)
        + x ((TopCat.toSSet.obj X).map tf1245.op τ) * y ((TopCat.toSSet.obj X).map tf2345.op τ) := by
  unfold cupTwo33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwx0123 ≫ SimplexCategory.δ (0 : Fin 6) = tf1234 from by decide,
    show cwx0134 ≫ SimplexCategory.δ (0 : Fin 6) = tf1245 from by decide,
    show cwx0234 ≫ SimplexCategory.δ (0 : Fin 6) = tf1345 from by decide,
    show cwy0124 ≫ SimplexCategory.δ (0 : Fin 6) = tf1235 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (0 : Fin 6) = tf2345 from by decide]

/-- Face expansion at `i = 1`. -/
theorem cupTwo33_face1 :
    cupTwo33 x y (face (1 : Fin 6) τ)
      = x ((TopCat.toSSet.obj X).map tf0234.op τ) * y ((TopCat.toSSet.obj X).map tf0245.op τ)
        + x ((TopCat.toSSet.obj X).map tf0345.op τ) * y ((TopCat.toSSet.obj X).map tf0235.op τ)
        + x ((TopCat.toSSet.obj X).map tf0234.op τ) * y ((TopCat.toSSet.obj X).map tf2345.op τ)
        + x ((TopCat.toSSet.obj X).map tf0245.op τ) * y ((TopCat.toSSet.obj X).map tf2345.op τ) := by
  unfold cupTwo33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwx0123 ≫ SimplexCategory.δ (1 : Fin 6) = tf0234 from by decide,
    show cwx0134 ≫ SimplexCategory.δ (1 : Fin 6) = tf0245 from by decide,
    show cwx0234 ≫ SimplexCategory.δ (1 : Fin 6) = tf0345 from by decide,
    show cwy0124 ≫ SimplexCategory.δ (1 : Fin 6) = tf0235 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (1 : Fin 6) = tf2345 from by decide]

/-- Face expansion at `i = 2`. -/
theorem cupTwo33_face2 :
    cupTwo33 x y (face (2 : Fin 6) τ)
      = x ((TopCat.toSSet.obj X).map tf0134.op τ) * y ((TopCat.toSSet.obj X).map tf0145.op τ)
        + x ((TopCat.toSSet.obj X).map tf0345.op τ) * y ((TopCat.toSSet.obj X).map tf0135.op τ)
        + x ((TopCat.toSSet.obj X).map tf0134.op τ) * y ((TopCat.toSSet.obj X).map tf1345.op τ)
        + x ((TopCat.toSSet.obj X).map tf0145.op τ) * y ((TopCat.toSSet.obj X).map tf1345.op τ) := by
  unfold cupTwo33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwx0123 ≫ SimplexCategory.δ (2 : Fin 6) = tf0134 from by decide,
    show cwx0134 ≫ SimplexCategory.δ (2 : Fin 6) = tf0145 from by decide,
    show cwx0234 ≫ SimplexCategory.δ (2 : Fin 6) = tf0345 from by decide,
    show cwy0124 ≫ SimplexCategory.δ (2 : Fin 6) = tf0135 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (2 : Fin 6) = tf1345 from by decide]

/-- Face expansion at `i = 3`. -/
theorem cupTwo33_face3 :
    cupTwo33 x y (face (3 : Fin 6) τ)
      = x ((TopCat.toSSet.obj X).map tf0124.op τ) * y ((TopCat.toSSet.obj X).map tf0145.op τ)
        + x ((TopCat.toSSet.obj X).map tf0245.op τ) * y ((TopCat.toSSet.obj X).map tf0125.op τ)
        + x ((TopCat.toSSet.obj X).map tf0124.op τ) * y ((TopCat.toSSet.obj X).map tf1245.op τ)
        + x ((TopCat.toSSet.obj X).map tf0145.op τ) * y ((TopCat.toSSet.obj X).map tf1245.op τ) := by
  unfold cupTwo33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwx0123 ≫ SimplexCategory.δ (3 : Fin 6) = tf0124 from by decide,
    show cwx0134 ≫ SimplexCategory.δ (3 : Fin 6) = tf0145 from by decide,
    show cwx0234 ≫ SimplexCategory.δ (3 : Fin 6) = tf0245 from by decide,
    show cwy0124 ≫ SimplexCategory.δ (3 : Fin 6) = tf0125 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (3 : Fin 6) = tf1245 from by decide]

/-- Face expansion at `i = 4`. -/
theorem cupTwo33_face4 :
    cupTwo33 x y (face (4 : Fin 6) τ)
      = x ((TopCat.toSSet.obj X).map tf0123.op τ) * y ((TopCat.toSSet.obj X).map tf0135.op τ)
        + x ((TopCat.toSSet.obj X).map tf0235.op τ) * y ((TopCat.toSSet.obj X).map tf0125.op τ)
        + x ((TopCat.toSSet.obj X).map tf0123.op τ) * y ((TopCat.toSSet.obj X).map tf1235.op τ)
        + x ((TopCat.toSSet.obj X).map tf0135.op τ) * y ((TopCat.toSSet.obj X).map tf1235.op τ) := by
  unfold cupTwo33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwx0123 ≫ SimplexCategory.δ (4 : Fin 6) = tf0123 from by decide,
    show cwx0134 ≫ SimplexCategory.δ (4 : Fin 6) = tf0135 from by decide,
    show cwx0234 ≫ SimplexCategory.δ (4 : Fin 6) = tf0235 from by decide,
    show cwy0124 ≫ SimplexCategory.δ (4 : Fin 6) = tf0125 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (4 : Fin 6) = tf1235 from by decide]

/-- Face expansion at `i = 5`. -/
theorem cupTwo33_face5 :
    cupTwo33 x y (face (5 : Fin 6) τ)
      = x ((TopCat.toSSet.obj X).map tf0123.op τ) * y ((TopCat.toSSet.obj X).map tf0134.op τ)
        + x ((TopCat.toSSet.obj X).map tf0234.op τ) * y ((TopCat.toSSet.obj X).map tf0124.op τ)
        + x ((TopCat.toSSet.obj X).map tf0123.op τ) * y ((TopCat.toSSet.obj X).map tf1234.op τ)
        + x ((TopCat.toSSet.obj X).map tf0134.op τ) * y ((TopCat.toSSet.obj X).map tf1234.op τ) := by
  unfold cupTwo33 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwx0123 ≫ SimplexCategory.δ (5 : Fin 6) = tf0123 from by decide,
    show cwx0134 ≫ SimplexCategory.δ (5 : Fin 6) = tf0134 from by decide,
    show cwx0234 ≫ SimplexCategory.δ (5 : Fin 6) = tf0234 from by decide,
    show cwy0124 ≫ SimplexCategory.δ (5 : Fin 6) = tf0124 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (5 : Fin 6) = tf1234 from by decide]

/-! ### The six pentachoron cocycle relations
`τ = [0,…,5]` has exactly six `4`-faces (pentachora) `∂ᵢτ` (drop vertex `i`). For a `3`-cocycle `f`
(`δf = 0`), on each the mod-`2` sum of `f` over its five tetrahedral `3`-faces vanishes — this is
`congrFun (δf = 0)` at `∂ᵢτ`, expanded via `Fin.sum_univ_five` and the decidable composites
`(δₖ ≫ δᵢ) = tfIJKL`. Stated once per pentachoron, reused for `x` and `y`. -/

/-- Cocycle relation on pentachoron `∂₀τ` (drop `0`; faces of `{1,2,3,4,5}`). -/
theorem cocycle_pent0 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tf2345.op τ) + f ((TopCat.toSSet.obj X).map tf1345.op τ)
      + f ((TopCat.toSSet.obj X).map tf1245.op τ) + f ((TopCat.toSSet.obj X).map tf1235.op τ)
      + f ((TopCat.toSSet.obj X).map tf1234.op τ) = 0 := by
  have h : coboundary X 3 f (face (0 : Fin 6) τ) = 0 := congrFun hf (face (0 : Fin 6) τ)
  rw [coboundary_apply, Fin.sum_univ_five, face_face (0 : Fin 6) (0 : Fin 5) τ,
    face_face (0 : Fin 6) (1 : Fin 5) τ, face_face (0 : Fin 6) (2 : Fin 5) τ,
    face_face (0 : Fin 6) (3 : Fin 5) τ, face_face (0 : Fin 6) (4 : Fin 5) τ,
    show SimplexCategory.δ (0 : Fin 5) ≫ SimplexCategory.δ (0 : Fin 6) = tf2345 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ SimplexCategory.δ (0 : Fin 6) = tf1345 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ SimplexCategory.δ (0 : Fin 6) = tf1245 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ SimplexCategory.δ (0 : Fin 6) = tf1235 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ SimplexCategory.δ (0 : Fin 6) = tf1234 from by decide] at h
  exact h

/-- Cocycle relation on pentachoron `∂₁τ` (drop `1`; faces of `{0,2,3,4,5}`). -/
theorem cocycle_pent1 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tf2345.op τ) + f ((TopCat.toSSet.obj X).map tf0345.op τ)
      + f ((TopCat.toSSet.obj X).map tf0245.op τ) + f ((TopCat.toSSet.obj X).map tf0235.op τ)
      + f ((TopCat.toSSet.obj X).map tf0234.op τ) = 0 := by
  have h : coboundary X 3 f (face (1 : Fin 6) τ) = 0 := congrFun hf (face (1 : Fin 6) τ)
  rw [coboundary_apply, Fin.sum_univ_five, face_face (1 : Fin 6) (0 : Fin 5) τ,
    face_face (1 : Fin 6) (1 : Fin 5) τ, face_face (1 : Fin 6) (2 : Fin 5) τ,
    face_face (1 : Fin 6) (3 : Fin 5) τ, face_face (1 : Fin 6) (4 : Fin 5) τ,
    show SimplexCategory.δ (0 : Fin 5) ≫ SimplexCategory.δ (1 : Fin 6) = tf2345 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ SimplexCategory.δ (1 : Fin 6) = tf0345 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ SimplexCategory.δ (1 : Fin 6) = tf0245 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ SimplexCategory.δ (1 : Fin 6) = tf0235 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ SimplexCategory.δ (1 : Fin 6) = tf0234 from by decide] at h
  exact h

/-- Cocycle relation on pentachoron `∂₂τ` (drop `2`; faces of `{0,1,3,4,5}`). -/
theorem cocycle_pent2 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tf1345.op τ) + f ((TopCat.toSSet.obj X).map tf0345.op τ)
      + f ((TopCat.toSSet.obj X).map tf0145.op τ) + f ((TopCat.toSSet.obj X).map tf0135.op τ)
      + f ((TopCat.toSSet.obj X).map tf0134.op τ) = 0 := by
  have h : coboundary X 3 f (face (2 : Fin 6) τ) = 0 := congrFun hf (face (2 : Fin 6) τ)
  rw [coboundary_apply, Fin.sum_univ_five, face_face (2 : Fin 6) (0 : Fin 5) τ,
    face_face (2 : Fin 6) (1 : Fin 5) τ, face_face (2 : Fin 6) (2 : Fin 5) τ,
    face_face (2 : Fin 6) (3 : Fin 5) τ, face_face (2 : Fin 6) (4 : Fin 5) τ,
    show SimplexCategory.δ (0 : Fin 5) ≫ SimplexCategory.δ (2 : Fin 6) = tf1345 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ SimplexCategory.δ (2 : Fin 6) = tf0345 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ SimplexCategory.δ (2 : Fin 6) = tf0145 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ SimplexCategory.δ (2 : Fin 6) = tf0135 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ SimplexCategory.δ (2 : Fin 6) = tf0134 from by decide] at h
  exact h

/-- Cocycle relation on pentachoron `∂₃τ` (drop `3`; faces of `{0,1,2,4,5}`). -/
theorem cocycle_pent3 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tf1245.op τ) + f ((TopCat.toSSet.obj X).map tf0245.op τ)
      + f ((TopCat.toSSet.obj X).map tf0145.op τ) + f ((TopCat.toSSet.obj X).map tf0125.op τ)
      + f ((TopCat.toSSet.obj X).map tf0124.op τ) = 0 := by
  have h : coboundary X 3 f (face (3 : Fin 6) τ) = 0 := congrFun hf (face (3 : Fin 6) τ)
  rw [coboundary_apply, Fin.sum_univ_five, face_face (3 : Fin 6) (0 : Fin 5) τ,
    face_face (3 : Fin 6) (1 : Fin 5) τ, face_face (3 : Fin 6) (2 : Fin 5) τ,
    face_face (3 : Fin 6) (3 : Fin 5) τ, face_face (3 : Fin 6) (4 : Fin 5) τ,
    show SimplexCategory.δ (0 : Fin 5) ≫ SimplexCategory.δ (3 : Fin 6) = tf1245 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ SimplexCategory.δ (3 : Fin 6) = tf0245 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ SimplexCategory.δ (3 : Fin 6) = tf0145 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ SimplexCategory.δ (3 : Fin 6) = tf0125 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ SimplexCategory.δ (3 : Fin 6) = tf0124 from by decide] at h
  exact h

/-- Cocycle relation on pentachoron `∂₄τ` (drop `4`; faces of `{0,1,2,3,5}`). -/
theorem cocycle_pent4 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tf1235.op τ) + f ((TopCat.toSSet.obj X).map tf0235.op τ)
      + f ((TopCat.toSSet.obj X).map tf0135.op τ) + f ((TopCat.toSSet.obj X).map tf0125.op τ)
      + f ((TopCat.toSSet.obj X).map tf0123.op τ) = 0 := by
  have h : coboundary X 3 f (face (4 : Fin 6) τ) = 0 := congrFun hf (face (4 : Fin 6) τ)
  rw [coboundary_apply, Fin.sum_univ_five, face_face (4 : Fin 6) (0 : Fin 5) τ,
    face_face (4 : Fin 6) (1 : Fin 5) τ, face_face (4 : Fin 6) (2 : Fin 5) τ,
    face_face (4 : Fin 6) (3 : Fin 5) τ, face_face (4 : Fin 6) (4 : Fin 5) τ,
    show SimplexCategory.δ (0 : Fin 5) ≫ SimplexCategory.δ (4 : Fin 6) = tf1235 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ SimplexCategory.δ (4 : Fin 6) = tf0235 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ SimplexCategory.δ (4 : Fin 6) = tf0135 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ SimplexCategory.δ (4 : Fin 6) = tf0125 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ SimplexCategory.δ (4 : Fin 6) = tf0123 from by decide] at h
  exact h

/-- Cocycle relation on pentachoron `∂₅τ` (drop `5`; faces of `{0,1,2,3,4}`). -/
theorem cocycle_pent5 (f : SingularCochain X 3) (hf : coboundaryₗ X 3 f = 0) :
    f ((TopCat.toSSet.obj X).map tf1234.op τ) + f ((TopCat.toSSet.obj X).map tf0234.op τ)
      + f ((TopCat.toSSet.obj X).map tf0134.op τ) + f ((TopCat.toSSet.obj X).map tf0124.op τ)
      + f ((TopCat.toSSet.obj X).map tf0123.op τ) = 0 := by
  have h : coboundary X 3 f (face (5 : Fin 6) τ) = 0 := congrFun hf (face (5 : Fin 6) τ)
  rw [coboundary_apply, Fin.sum_univ_five, face_face (5 : Fin 6) (0 : Fin 5) τ,
    face_face (5 : Fin 6) (1 : Fin 5) τ, face_face (5 : Fin 6) (2 : Fin 5) τ,
    face_face (5 : Fin 6) (3 : Fin 5) τ, face_face (5 : Fin 6) (4 : Fin 5) τ,
    show SimplexCategory.δ (0 : Fin 5) ≫ SimplexCategory.δ (5 : Fin 6) = tf1234 from by decide,
    show SimplexCategory.δ (1 : Fin 5) ≫ SimplexCategory.δ (5 : Fin 6) = tf0234 from by decide,
    show SimplexCategory.δ (2 : Fin 5) ≫ SimplexCategory.δ (5 : Fin 6) = tf0134 from by decide,
    show SimplexCategory.δ (3 : Fin 5) ≫ SimplexCategory.δ (5 : Fin 6) = tf0124 from by decide,
    show SimplexCategory.δ (4 : Fin 5) ≫ SimplexCategory.δ (5 : Fin 6) = tf0123 from by decide] at h
  exact h

/-! ### The cup-`2` coboundary identity — the `⌣₁`-commutator killer
The Steenrod homotopy above `cupOne33`: `δ(x ⌣₂ y) = x ⌣₁ y + y ⌣₁ x` (mod `2`, for cocycles). The
left side sums the six face-expansions `cupTwo33 x y (∂ᵢτ)` (`24` products on `3`-faces of `τ`); the
right side is `cupOne33 x y + cupOne33 y x` (`6` products). The collapse is a pure `ZMod 2`
telescoping certificate over the six pentachoron cocycle relations (four for `x`, four for `y`). -/
theorem cupTwo33_coboundary (x y : SingularCochain X 3)
    (hx : coboundaryₗ X 3 x = 0) (hy : coboundaryₗ X 3 y = 0) :
    coboundary X 4 (cupTwo33 x y) = cupOne33 x y + cupOne33 y x := by
  funext τ
  have hx1 := cocycle_pent1 τ x hx
  have hx2 := cocycle_pent2 τ x hx
  have hx3 := cocycle_pent3 τ x hx
  have hx5 := cocycle_pent5 τ x hx
  have hy0 := cocycle_pent0 τ y hy
  have hy2 := cocycle_pent2 τ y hy
  have hy3 := cocycle_pent3 τ y hy
  have hy4 := cocycle_pent4 τ y hy
  rw [coboundary_apply, Fin.sum_univ_six, cupTwo33_face0, cupTwo33_face1, cupTwo33_face2,
    cupTwo33_face3, cupTwo33_face4, cupTwo33_face5]
  show _ = (cupOne33 x y + cupOne33 y x) τ
  rw [Pi.add_apply]
  unfold cupOne33
  rw [show cuA0 = tf0345 from by decide, show cuB0 = tf0123 from by decide,
    show cuA1 = tf0145 from by decide, show cuB1 = tf1234 from by decide,
    show cuA2 = tf0125 from by decide, show cuB2 = tf2345 from by decide]
  set x0123 := x ((TopCat.toSSet.obj X).map tf0123.op τ)
  set x0134 := x ((TopCat.toSSet.obj X).map tf0134.op τ)
  set x0145 := x ((TopCat.toSSet.obj X).map tf0145.op τ)
  set x0234 := x ((TopCat.toSSet.obj X).map tf0234.op τ)
  set x0345 := x ((TopCat.toSSet.obj X).map tf0345.op τ)
  set y0125 := y ((TopCat.toSSet.obj X).map tf0125.op τ)
  set y0145 := y ((TopCat.toSSet.obj X).map tf0145.op τ)
  set y1235 := y ((TopCat.toSSet.obj X).map tf1235.op τ)
  set y1245 := y ((TopCat.toSSet.obj X).map tf1245.op τ)
  set y2345 := y ((TopCat.toSSet.obj X).map tf2345.op τ)
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    y0125 * hx1 + y1235 * hx2 + y2345 * hx3 + (y0145 + y1245 + y2345) * hx5
    + (x0123 + x0134 + x0145) * hy0 + x0123 * hy2 + x0234 * hy3 + x0345 * hy4

/-! ### The ten triangular atom inclusions `[2] ⟶ [5]` (for the `(2,3)` Hirsch leg)
`cupOne23`'s `δ`-expansion, the plain cup terms, and the `δc`-expansions all pair `c` on triangular
`2`-faces `trfIJK` (`{I,J,K} ⊂ {0,…,5}`) against `d` on the `tfIJKL` tetrahedra. -/

/-- `[2] ⟶ [5]` selecting `{0,1,2}`. -/
def trf012 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 2], by decide⟩
/-- `[2] ⟶ [5]` selecting `{0,1,4}`. -/
def trf014 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 4], by decide⟩
/-- `[2] ⟶ [5]` selecting `{0,1,5}`. -/
def trf015 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 1, 5], by decide⟩
/-- `[2] ⟶ [5]` selecting `{0,2,5}`. -/
def trf025 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 2, 5], by decide⟩
/-- `[2] ⟶ [5]` selecting `{0,3,4}`. -/
def trf034 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 3, 4], by decide⟩
/-- `[2] ⟶ [5]` selecting `{0,3,5}`. -/
def trf035 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 3, 5], by decide⟩
/-- `[2] ⟶ [5]` selecting `{0,4,5}`. -/
def trf045 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![0, 4, 5], by decide⟩
/-- `[2] ⟶ [5]` selecting `{1,2,5}`. -/
def trf125 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![1, 2, 5], by decide⟩
/-- `[2] ⟶ [5]` selecting `{1,4,5}`. -/
def trf145 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![1, 4, 5], by decide⟩
/-- `[2] ⟶ [5]` selecting `{3,4,5}`. -/
def trf345 : SimplexCategory.mk 2 ⟶ SimplexCategory.mk 5 :=
  SimplexCategory.mkHom ⟨![3, 4, 5], by decide⟩

/-! ### The six face-expansions of `cupOne23 c d (∂ᵢτ)` -/

variable (c : SingularCochain X 2) (d : SingularCochain X 3)

/-- Face expansion at `i = 0`. -/
theorem cupOne23_face0 :
    cupOne23 c d (face (0 : Fin 6) τ)
      = c ((TopCat.toSSet.obj X).map trf145.op τ) * d ((TopCat.toSSet.obj X).map tf1234.op τ)
        + c ((TopCat.toSSet.obj X).map trf125.op τ) * d ((TopCat.toSSet.obj X).map tf2345.op τ) := by
  unfold cupOne23 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwc034 ≫ SimplexCategory.δ (0 : Fin 6) = trf145 from by decide,
    show cwx0123 ≫ SimplexCategory.δ (0 : Fin 6) = tf1234 from by decide,
    show cwc014 ≫ SimplexCategory.δ (0 : Fin 6) = trf125 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (0 : Fin 6) = tf2345 from by decide]

/-- Face expansion at `i = 1`. -/
theorem cupOne23_face1 :
    cupOne23 c d (face (1 : Fin 6) τ)
      = c ((TopCat.toSSet.obj X).map trf045.op τ) * d ((TopCat.toSSet.obj X).map tf0234.op τ)
        + c ((TopCat.toSSet.obj X).map trf025.op τ) * d ((TopCat.toSSet.obj X).map tf2345.op τ) := by
  unfold cupOne23 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwc034 ≫ SimplexCategory.δ (1 : Fin 6) = trf045 from by decide,
    show cwx0123 ≫ SimplexCategory.δ (1 : Fin 6) = tf0234 from by decide,
    show cwc014 ≫ SimplexCategory.δ (1 : Fin 6) = trf025 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (1 : Fin 6) = tf2345 from by decide]

/-- Face expansion at `i = 2`. -/
theorem cupOne23_face2 :
    cupOne23 c d (face (2 : Fin 6) τ)
      = c ((TopCat.toSSet.obj X).map trf045.op τ) * d ((TopCat.toSSet.obj X).map tf0134.op τ)
        + c ((TopCat.toSSet.obj X).map trf015.op τ) * d ((TopCat.toSSet.obj X).map tf1345.op τ) := by
  unfold cupOne23 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwc034 ≫ SimplexCategory.δ (2 : Fin 6) = trf045 from by decide,
    show cwx0123 ≫ SimplexCategory.δ (2 : Fin 6) = tf0134 from by decide,
    show cwc014 ≫ SimplexCategory.δ (2 : Fin 6) = trf015 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (2 : Fin 6) = tf1345 from by decide]

/-- Face expansion at `i = 3`. -/
theorem cupOne23_face3 :
    cupOne23 c d (face (3 : Fin 6) τ)
      = c ((TopCat.toSSet.obj X).map trf045.op τ) * d ((TopCat.toSSet.obj X).map tf0124.op τ)
        + c ((TopCat.toSSet.obj X).map trf015.op τ) * d ((TopCat.toSSet.obj X).map tf1245.op τ) := by
  unfold cupOne23 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwc034 ≫ SimplexCategory.δ (3 : Fin 6) = trf045 from by decide,
    show cwx0123 ≫ SimplexCategory.δ (3 : Fin 6) = tf0124 from by decide,
    show cwc014 ≫ SimplexCategory.δ (3 : Fin 6) = trf015 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (3 : Fin 6) = tf1245 from by decide]

/-- Face expansion at `i = 4`. -/
theorem cupOne23_face4 :
    cupOne23 c d (face (4 : Fin 6) τ)
      = c ((TopCat.toSSet.obj X).map trf035.op τ) * d ((TopCat.toSSet.obj X).map tf0123.op τ)
        + c ((TopCat.toSSet.obj X).map trf015.op τ) * d ((TopCat.toSSet.obj X).map tf1235.op τ) := by
  unfold cupOne23 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwc034 ≫ SimplexCategory.δ (4 : Fin 6) = trf035 from by decide,
    show cwx0123 ≫ SimplexCategory.δ (4 : Fin 6) = tf0123 from by decide,
    show cwc014 ≫ SimplexCategory.δ (4 : Fin 6) = trf015 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (4 : Fin 6) = tf1235 from by decide]

/-- Face expansion at `i = 5`. -/
theorem cupOne23_face5 :
    cupOne23 c d (face (5 : Fin 6) τ)
      = c ((TopCat.toSSet.obj X).map trf034.op τ) * d ((TopCat.toSSet.obj X).map tf0123.op τ)
        + c ((TopCat.toSSet.obj X).map trf014.op τ) * d ((TopCat.toSSet.obj X).map tf1234.op τ) := by
  unfold cupOne23 face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show cwc034 ≫ SimplexCategory.δ (5 : Fin 6) = trf034 from by decide,
    show cwx0123 ≫ SimplexCategory.δ (5 : Fin 6) = tf0123 from by decide,
    show cwc014 ≫ SimplexCategory.δ (5 : Fin 6) = trf014 from by decide,
    show cwy1234 ≫ SimplexCategory.δ (5 : Fin 6) = tf1234 from by decide]

/-! ### The three `δc`-expansions on the `cupOne33` `x`-carrier tetrahedra `cuAⱼ`
The `(δc) ⌣₁ d` term of the Hirsch identity unfolds to `(δc)` evaluated on `cupOne33`'s three
`x`-inclusions `cuA0 = {0,3,4,5}`, `cuA1 = {0,1,4,5}`, `cuA2 = {0,1,2,5}`. Each `(δc)` on such a
tetrahedron is the mod-`2` sum of `c` over its four triangular faces (`coboundary`'s definition,
expanded via the decidable composites `(δₖ ≫ cuAⱼ) = trfIJK`). -/

/-- `(δc)` on `cuA0 = {0,3,4,5}`. -/
theorem deltaC_cuA0 :
    coboundaryₗ X 2 c ((TopCat.toSSet.obj X).map cuA0.op τ)
      = c ((TopCat.toSSet.obj X).map trf345.op τ) + c ((TopCat.toSSet.obj X).map trf045.op τ)
        + c ((TopCat.toSSet.obj X).map trf035.op τ) + c ((TopCat.toSSet.obj X).map trf034.op τ) := by
  show coboundary X 2 c _ = _
  rw [coboundary_apply, Fin.sum_univ_four]
  unfold face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 4) ≫ cuA0 = trf345 from by decide,
    show SimplexCategory.δ (1 : Fin 4) ≫ cuA0 = trf045 from by decide,
    show SimplexCategory.δ (2 : Fin 4) ≫ cuA0 = trf035 from by decide,
    show SimplexCategory.δ (3 : Fin 4) ≫ cuA0 = trf034 from by decide]

/-- `(δc)` on `cuA1 = {0,1,4,5}`. -/
theorem deltaC_cuA1 :
    coboundaryₗ X 2 c ((TopCat.toSSet.obj X).map cuA1.op τ)
      = c ((TopCat.toSSet.obj X).map trf145.op τ) + c ((TopCat.toSSet.obj X).map trf045.op τ)
        + c ((TopCat.toSSet.obj X).map trf015.op τ) + c ((TopCat.toSSet.obj X).map trf014.op τ) := by
  show coboundary X 2 c _ = _
  rw [coboundary_apply, Fin.sum_univ_four]
  unfold face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 4) ≫ cuA1 = trf145 from by decide,
    show SimplexCategory.δ (1 : Fin 4) ≫ cuA1 = trf045 from by decide,
    show SimplexCategory.δ (2 : Fin 4) ≫ cuA1 = trf015 from by decide,
    show SimplexCategory.δ (3 : Fin 4) ≫ cuA1 = trf014 from by decide]

/-- `(δc)` on `cuA2 = {0,1,2,5}`. -/
theorem deltaC_cuA2 :
    coboundaryₗ X 2 c ((TopCat.toSSet.obj X).map cuA2.op τ)
      = c ((TopCat.toSSet.obj X).map trf125.op τ) + c ((TopCat.toSSet.obj X).map trf025.op τ)
        + c ((TopCat.toSSet.obj X).map trf015.op τ) + c ((TopCat.toSSet.obj X).map trf012.op τ) := by
  show coboundary X 2 c _ = _
  rw [coboundary_apply, Fin.sum_univ_four]
  unfold face
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, ← op_comp,
    show SimplexCategory.δ (0 : Fin 4) ≫ cuA2 = trf125 from by decide,
    show SimplexCategory.δ (1 : Fin 4) ≫ cuA2 = trf025 from by decide,
    show SimplexCategory.δ (2 : Fin 4) ≫ cuA2 = trf015 from by decide,
    show SimplexCategory.δ (3 : Fin 4) ≫ cuA2 = trf012 from by decide]

/-! ### The cup-`1` `(2,3)` Hirsch coboundary identity
`δ(c ⌣₁ d) = (δc) ⌣₁ d + c ⌣ d + d ⌣ c` (mod `2`, for a cocycle `d`). Expanding the left side (six
face-expansions), the `(δc) ⌣₁ d = cupOne33 (δc) d` term (via the three `δc`-expansions), and the two
plain cup terms, the identity closes over the two pentachoron cocycle relations of `d` (`pent0` and
`pent5`) — the leftover `c ⌣₁ (δd)` boundary term. -/
theorem cupOne23_coboundary (c : SingularCochain X 2) (d : SingularCochain X 3)
    (hd : coboundaryₗ X 3 d = 0) :
    coboundary X 4 (cupOne23 c d) = cupOne33 (coboundaryₗ X 2 c) d + cup c d + cup d c := by
  funext τ
  have hd0 := cocycle_pent0 τ d hd
  have hd5 := cocycle_pent5 τ d hd
  rw [coboundary_apply, Fin.sum_univ_six, cupOne23_face0, cupOne23_face1, cupOne23_face2,
    cupOne23_face3, cupOne23_face4, cupOne23_face5]
  show _ = (cupOne33 (coboundaryₗ X 2 c) d + cup c d + cup d c) τ
  rw [Pi.add_apply, Pi.add_apply]
  unfold cupOne33
  rw [deltaC_cuA0, deltaC_cuA1, deltaC_cuA2,
    show cuB0 = tf0123 from by decide, show cuB1 = tf1234 from by decide,
    show cuB2 = tf2345 from by decide, cup_apply, cup_apply]
  unfold frontFace backFace
  rw [show frontIncl 2 3 = trf012 from by decide, show backIncl 2 3 = tf2345 from by decide,
    show frontIncl 3 2 = tf0123 from by decide, show backIncl 3 2 = trf345 from by decide]
  set c015 := c ((TopCat.toSSet.obj X).map trf015.op τ)
  set c045 := c ((TopCat.toSSet.obj X).map trf045.op τ)
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) c015 * hd0 + c045 * hd5

/-! ## §2. The sub-top Steenrod square `Sq² : H³ → H⁵`

The cocycle-level square `x ↦ x ⌣₁ x` (`sq2Cocycle`, `SingularCupOne33`) descends to cohomology.
Well-definedness: for `x' = x + δc` (a cohomologous cocycle, `d := δc`, `δd = 0`), bi-additivity of
`⌣₁` gives `x' ⌣₁ x' − x ⌣₁ x = x ⌣₁ d + d ⌣₁ x + d ⌣₁ d`, and
* `x ⌣₁ d + d ⌣₁ x = δ(x ⌣₂ d)` (`cupTwo33_coboundary`, since `x, d` are cocycles);
* `d ⌣₁ d = δ(c ⌣₁ d + c ⌣ c)` (`cupOne23_coboundary` with the plain cup Leibniz `δ(c ⌣ c) = c ⌣ d
  + d ⌣ c`), because `(δc) ⌣₁ d = d ⌣₁ d`.
So `x' ⌣₁ x' − x ⌣₁ x = δ(x ⌣₂ d + c ⌣₁ d + c ⌣ c) ∈ B⁵`. Additivity uses the same
`cupTwo33_coboundary` to kill the cross term `x ⌣₁ y + y ⌣₁ x` in `H⁵`. -/

/-- **The full cup Leibniz at degree `(2,2)`** `δ(c ⌣ c) = δc ⌣ c + c ⌣ δc` (mod `2`). Both terms of
the pointwise `coboundary_cup` are, definitionally, the two cup terms at the shifted split. -/
theorem cup_leibniz22 (c : SingularCochain X 2) :
    coboundaryₗ X 4 (cup c c) = cup (coboundaryₗ X 2 c) c + cup c (coboundaryₗ X 2 c) := by
  funext τ
  show coboundary X (2 + 2) (cup c c) τ
    = (cup (coboundaryₗ X 2 c) c + cup c (coboundaryₗ X 2 c)) τ
  rw [coboundary_cup, Pi.add_apply]
  rfl

/-- The diagonal `d ⌣₁ d` for a coboundary `d = δc` is itself the coboundary
`δ(c ⌣₁ d + c ⌣ c)`. Combines `cupOne23_coboundary` (giving `d ⌣₁ d + c ⌣ d + d ⌣ c`) with the cup
Leibniz `cup_leibniz22` (giving `c ⌣ d + d ⌣ c`); the two cross terms cancel mod `2`. -/
theorem cupOne33_delta_diag (c : SingularCochain X 2) :
    cupOne33 (coboundaryₗ X 2 c) (coboundaryₗ X 2 c)
      = coboundaryₗ X 4 (cupOne23 c (coboundaryₗ X 2 c) + cup c c) := by
  have hd : coboundaryₗ X 3 (coboundaryₗ X 2 c) = 0 := coboundary_comp_coboundary X 2 c
  have h1 := cupOne23_coboundary c (coboundaryₗ X 2 c) hd
  have h2 := cup_leibniz22 c
  rw [map_add, show coboundaryₗ X 4 (cupOne23 c (coboundaryₗ X 2 c))
      = coboundary X 4 (cupOne23 c (coboundaryₗ X 2 c)) from rfl, h1, h2]
  funext τ
  simp only [Pi.add_apply]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- **The `Sq²` well-definedness cochain identity**: shifting a `3`-cocycle `z` by a coboundary `δc`
changes `z ⌣₁ z` by an explicit `5`-coboundary `δ(z ⌣₂ δc + (c ⌣₁ δc + c ⌣ c))`. Bi-additivity of
`⌣₁`, the cup-`2` cross-term identity (`cupTwo33_coboundary`), and `cupOne33_delta_diag`. -/
theorem sq2_cochain_shift (z : SingularCochain X 3) (c : SingularCochain X 2)
    (hz : coboundaryₗ X 3 z = 0) :
    cupOne33 (z + coboundaryₗ X 2 c) (z + coboundaryₗ X 2 c)
      = cupOne33 z z + coboundaryₗ X 4 (cupTwo33 z (coboundaryₗ X 2 c)
          + (cupOne23 c (coboundaryₗ X 2 c) + cup c c)) := by
  have hd : coboundaryₗ X 3 (coboundaryₗ X 2 c) = 0 := coboundary_comp_coboundary X 2 c
  have hcross := cupTwo33_coboundary z (coboundaryₗ X 2 c) hz hd
  have hdd := cupOne33_delta_diag c
  rw [map_add (coboundaryₗ X 4), show coboundaryₗ X 4 (cupTwo33 z (coboundaryₗ X 2 c))
      = coboundary X 4 (cupTwo33 z (coboundaryₗ X 2 c)) from rfl, hcross, ← hdd,
    cupOne33_add_left, cupOne33_add_right, cupOne33_add_right]
  abel

/-- **The `Sq²` additivity cochain identity**: `(x+y) ⌣₁ (x+y) = x ⌣₁ x + y ⌣₁ y + δ(x ⌣₂ y)` for
cocycles `x, y`. Bi-additivity of `⌣₁` plus the cup-`2` cross-term identity `cupTwo33_coboundary`. -/
theorem sq2_cochain_add (x y : SingularCochain X 3)
    (hx : coboundaryₗ X 3 x = 0) (hy : coboundaryₗ X 3 y = 0) :
    cupOne33 (x + y) (x + y) = cupOne33 x x + cupOne33 y y + coboundaryₗ X 4 (cupTwo33 x y) := by
  have hcross := cupTwo33_coboundary x y hx hy
  rw [show coboundaryₗ X 4 (cupTwo33 x y) = coboundary X 4 (cupTwo33 x y) from rfl, hcross,
    cupOne33_add_left, cupOne33_add_right, cupOne33_add_right]
  abel

/-- The difference `x ⌣₁ x − x' ⌣₁ x'` of cohomologous `3`-cocycles (`δβ = x − x'`) is an explicit
`5`-coboundary — the range-membership witness for `Sq²` well-definedness (`sq2_cochain_shift`). -/
theorem sq2Cocycle_sub_mem_range (a a' : LinearMap.ker (coboundaryₗ X 3))
    (β : SingularCochain X 2) (hβ : coboundaryₗ X 2 β = a.1 - a'.1) :
    ∃ w : SingularCochain X 4,
      coboundaryₗ X 4 w = cupOne33 a.1 a.1 - cupOne33 a'.1 a'.1 := by
  refine ⟨cupTwo33 a'.1 (coboundaryₗ X 2 β) + (cupOne23 β (coboundaryₗ X 2 β) + cup β β), ?_⟩
  have hz : coboundaryₗ X 3 a'.1 = 0 := LinearMap.mem_ker.mp a'.2
  have hac : a.1 = a'.1 + coboundaryₗ X 2 β := by rw [hβ]; abel
  rw [hac, sq2_cochain_shift a'.1 β hz]
  abel

/-- The **`Sq²` set-function** `[x] ↦ [x ⌣₁ x]` on `H³(X;ℤ/2)`. Well-defined by `sq2Cocycle` (lands in
`5`-cocycles, `SingularCupOne33`) and `sq2Cocycle_sub_mem_range` (the difference of cohomologous
representatives is a `5`-coboundary). -/
noncomputable def sq2fun (x : Cohomology X 3) : Cohomology X 5 := by
  refine Quotient.liftOn' x (fun a => Cohomology.mk X 5 (sq2Cocycle a)) ?_
  rintro a a' hrel
  rw [Submodule.quotientRel_def] at hrel
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub] at hrel
  rw [show coboundaryRange X 3 = LinearMap.range (coboundaryₗ X 2) from rfl] at hrel
  obtain ⟨β, hβ⟩ := hrel
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  rw [show coboundaryRange X 5 = LinearMap.range (coboundaryₗ X 4) from rfl]
  exact sq2Cocycle_sub_mem_range a a' β hβ

@[simp] theorem sq2fun_mk (a : LinearMap.ker (coboundaryₗ X 3)) :
    sq2fun (Cohomology.mk X 3 a) = Cohomology.mk X 5 (sq2Cocycle a) := rfl

/-- `sq2fun` is **additive**: the cross-term defect `x ⌣₁ y + y ⌣₁ x` of `sq2_cochain_add` is the
`5`-coboundary `δ(x ⌣₂ y)`, hence vanishes in `H⁵`. -/
theorem sq2fun_add (x y : Cohomology X 3) : sq2fun (x + y) = sq2fun x + sq2fun y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show sq2fun (Cohomology.mk X 3 (a + b))
      = sq2fun (Cohomology.mk X 3 a) + sq2fun (Cohomology.mk X 3 b)
  rw [sq2fun_mk, sq2fun_mk, sq2fun_mk]
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
  erw [← Submodule.Quotient.mk_add]
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub, AddMemClass.coe_add]
  rw [show coboundaryRange X 5 = LinearMap.range (coboundaryₗ X 4) from rfl]
  refine ⟨cupTwo33 a.1 b.1, ?_⟩
  have hadd := sq2_cochain_add a.1 b.1 (LinearMap.mem_ker.mp a.2) (LinearMap.mem_ker.mp b.2)
  show coboundaryₗ X 4 (cupTwo33 a.1 b.1)
      = cupOne33 (a.1 + b.1) (a.1 + b.1) - (cupOne33 a.1 a.1 + cupOne33 b.1 b.1)
  rw [hadd]; abel

/-- `sq2fun 0 = 0`, from additivity. -/
theorem sq2fun_zero : sq2fun (0 : Cohomology X 3) = 0 := by
  have h := sq2fun_add (0 : Cohomology X 3) 0
  rw [add_zero] at h
  have h2 : sq2fun (0 : Cohomology X 3) + 0 = sq2fun (0 : Cohomology X 3) + sq2fun 0 := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- **The sub-top Steenrod square** `Sq² : H³(X;ℤ/2) →ₗ[ℤ/2] H⁵(X;ℤ/2)`, `[x] ↦ [x ⌣₁ x]`. Additive
by `sq2fun_add` (the cross-term is the cup-`2` coboundary `δ(x ⌣₂ y)`); `ℤ/2`-linear because over
`ℤ/2` any additive map is linear (scalars `{0,1}`). This is the `(2,3)`-leg Wu datum `sqOp` for a
`5`-manifold — the value the Wu class `v₂` pairs against via `⟨Sq² a, [M]⟩ = ⟨v₂ ⌣ a, [M]⟩`. -/
noncomputable def Sq2 : Cohomology X 3 →ₗ[ZMod 2] Cohomology X 5 where
  toFun := sq2fun
  map_add' := sq2fun_add
  map_smul' r x := by
    fin_cases r
    · show sq2fun ((0 : ZMod 2) • x) = (0 : ZMod 2) • sq2fun x
      rw [zero_smul, zero_smul, sq2fun_zero]
    · show sq2fun ((1 : ZMod 2) • x) = (1 : ZMod 2) • sq2fun x
      rw [one_smul, one_smul]

@[simp] theorem Sq2_mk (a : LinearMap.ker (coboundaryₗ X 3)) :
    Sq2 (Cohomology.mk X 3 a) = Cohomology.mk X 5 (sq2Cocycle a) := rfl

end SKEFTHawking.SingularCohomologyMod2
