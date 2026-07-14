/-
# Phase 5q.H (W-A arm 4) — the concrete cylinder `[W,∂W]` candidate via the CROSS-PRODUCT

The honest product route `[W, ∂W] = [M] × [I, ∂I]` for the concrete reflexive cylinder
`W = M × [0,1]` over a **closed** charted `(m'+2)`-manifold `M`. Instantiates the generic mod-2
homology-level cross product `SingularRelativeCrossProduct.crossH`
(`Hₚ₊₁(M) → Hₚ₊₂(M × I, S)`) at `M := TopCat.of M`, `p := m'+1`, `S := ∂W = M × {⊥,⊤}`, fed with
`M`'s in-tree fundamental class `[M] ∈ Hₘ'₊₂(M)`
(`SingularFundamentalClass.fundamentalClass`). The output
`cylFundClassCandidate := [M] × [I, ∂I] ∈ Hₘ'₊₃(W, ∂W)` is the **concrete existence witness** the
cylinder datum's `hcls` hole consumes: it converts the abstract `HasRelFundClass` existential into
"*this specific* cross-product class restricts to the interior chart generator `cylGen`", the honest
named residual `cylFundClassCandidate_restricts` (the interior local-Künneth: the cross of the base
local generator `[M]|ₓ` with the interval local generator is the product local generator — a separate
deep arc).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCrossProduct
import SKEFTHawking.SingularFundamentalClassExist
import SKEFTHawking.PoincareLefschetzRelFundClassCylinder

open scoped Manifold
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-! ## §1. The endpoint-slice `MapsTo` facts (`∂W = M × {⊥,⊤}` contains both endpoint slices) -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- Both endpoint slices `M × {r}` (for `r ∈ {⊥,⊤}`) land in the cylinder boundary
`∂W = M × {⊥,⊤}` — the `S`-containment the cross-product engine's relative-cycle property needs. -/
theorem slice_mapsTo (r : unitInterval)
    (hr : (r : Set.Icc (0 : ℝ) 1) ∈ ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1))) :
    Set.MapsTo (slice (graphHom (TopCat.of M)) r) (Set.univ : Set ↑(TopCat.of M))
      ((cylModel m').boundary (cylW M)) := by
  intro x _
  rw [slice_graphHom, cyl_boundary_eq]
  exact ⟨Set.mem_univ x, hr⟩

omit [T2Space M] [CompactSpace M] [Nonempty M] in
theorem slice_one_mapsTo :
    Set.MapsTo (slice (graphHom (TopCat.of M)) 1) (Set.univ : Set ↑(TopCat.of M))
      ((cylModel m').boundary (cylW M)) :=
  slice_mapsTo (M := M) 1 (by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Subtype.ext rfl))

omit [T2Space M] [CompactSpace M] [Nonempty M] in
theorem slice_zero_mapsTo :
    Set.MapsTo (slice (graphHom (TopCat.of M)) 0) (Set.univ : Set ↑(TopCat.of M))
      ((cylModel m').boundary (cylW M)) :=
  slice_mapsTo (M := M) 0 (by
    rw [Set.mem_insert_iff]
    exact Or.inl (Subtype.ext rfl))

/-! ## §2. The concrete `[W,∂W]` candidate class -/

/-- **The concrete cylinder relative fundamental-class candidate** `[W, ∂W] := [M] × [I, ∂I]`, the
homology-level cross product of `M`'s in-tree fundamental class with the interval class, an element
of `Hₘ'₊₃(W, ∂W)`. This is the concrete existence witness the datum hole `hcls` consumes. -/
def cylFundClassCandidate :
    RelativeHomology (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) (m' + 1 + 2) :=
  crossH (M := TopCat.of M) (S := (cylModel m').boundary (cylW M))
    (slice_one_mapsTo (M := M) (m' := m')) (slice_zero_mapsTo (M := M) (m' := m')) (m' + 1)
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M))

/-! ## §3. The `hcls` reduction — the candidate restricts to the chart generator (named residual) -/

/-- **The `hcls` reduction along the concrete candidate.** IF the cross-product candidate
`[M] × [I, ∂I]` restricts to the interior chart generator `cylGen` at every interior point
(`hrestr`), THEN the cylinder's `HasRelFundClass` existence hole is filled *by it*. This pins the
abstract existential `hcls` to the restriction of ONE explicit class — the honest product route
`[W, ∂W] = [M] × [I, ∂I]`. The remaining residual is the interior local-Künneth: the cross of the
base local generator `[M]|ₓ` with the interval local generator is the product local generator (a
separate deep arc). -/
theorem hasRelFundClass_of_candidate_restricts [T1Space (cylW M)]
    (hrestr : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m'))
      (cylFundClassCandidate (M := M) (m' := m'))) :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) :=
  ⟨cylFundClassCandidate, hrestr⟩

/-- **The concrete cylinder datum from the named residual.** With the candidate's restriction
`hrestr`, the whole `RelFundClassDatum` — hence the `μ` functional feeding the Poincaré–Lefschetz Wu
tower — is available for the concrete cross-product class `[W, ∂W] = [M] × [I, ∂I]`. -/
def cylinderRelFundClassDatum_of_candidate_restricts [T1Space (cylW M)]
    (hrestr : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m'))
      (cylFundClassCandidate (M := M) (m' := m'))) :
    RelFundClassDatum (X := TopCat.of (cylW M)) (m := m' + 1) ((cylModel m').boundary (cylW M)) :=
  cylinderRelFundClassDatum (hasRelFundClass_of_candidate_restricts hrestr)

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
