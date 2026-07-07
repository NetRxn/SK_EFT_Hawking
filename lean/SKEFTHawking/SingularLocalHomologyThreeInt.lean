/-
# Phase 5q.H (E1 CSC-PD tower) — below-top local homology of a 4-manifold vanishes at degree 3 (integral)

`H₃(M, M∖x; ℤ) = 0` for `M` a `T1` topological 4-manifold and `x : M` — the below-top local homology.
The chart↔excision transport of `chartLocalIsoInt` (composed at the TOP degree 4 to `≅ ℤ`) run instead at
degree 3 lands in the Euclidean model `H₃(ℝ⁴, ℝ⁴∖0; ℤ)`, which `localHomologyInt_reduces_to_sphere 4 1`
bijects to `H₂(S³;ℤ)` — the MIDDLE sphere homology, `= 0` by `sphere_homology_middleInt`. Freeness of the
(trivial) module follows by `Module.Free.of_subsingleton`.

This discharges the below-top freeness posit `[Module.Free ℤ (RelHomologyInt {x}ᶜ 3)]` carried by the D⁰
base case (`openDuality₀_*_of_chartConvexInt`) — making that input ZERO-posit. It is the degree-3 mirror of
the top-degree `manifoldLocalHomologyIsoInt` (`H₄(M, M∖x; ℤ) ≅ ℤ`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularLocalHomologyIsoInt
import SKEFTHawking.SingularLocalHomologyInt
import SKEFTHawking.SingularSphereMiddleInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularPuncturedRetract (Sph normalize)
open SKEFTHawking.SingularLocalHomologyInt (localHomologyInt_reduces_to_sphere)
open SKEFTHawking.SingularSphereMiddleInt (sphere_homology_middleInt)
open SKEFTHawking.SingularLocalModelChart
  (transl transl_comp_transl_neg transl_neg_comp_transl mapsTo_transl mapsTo_transl_neg)
open SKEFTHawking.SingularRelativeFunctorialityInt
  (RelHomologyInt.map RelHomologyInt.map_bijective_of_comp_id)
open SKEFTHawking.SingularLocalHomologyIsoInt (openPointExcisionEquivInt chartPairEquivInt)

namespace SKEFTHawking.SingularLocalHomologyThreeInt

/-- **The Euclidean-model below-top local homology `H₃(ℝ⁴, ℝ⁴∖0; ℤ) = 0`.** Via
`localHomologyInt_reduces_to_sphere 4 1` (`H₃(ℝ⁴,ℝ⁴∖0;ℤ) ≅ H₂(S³;ℤ)`) and the middle sphere vanishing
`H₂(S³;ℤ) = 0` (`sphere_homology_middleInt 2 3`, using the defeq `Sph 4 (⊆ℝ⁴) ≡ Sⁿ⁻¹ = S³`). -/
theorem euclLocalHomologyThree_trivialInt :
    Subsingleton (RelHomologyInt (X := Eucl 4) {x | x ≠ 0} 3) := by
  haveI hsph : Subsingleton (Homology (Sph 4) 2) :=
    ⟨fun a b => by
      rw [sphere_homology_middleInt 2 3 (by omega) (by omega) a,
          sphere_homology_middleInt 2 3 (by omega) (by omega) b]⟩
  exact ⟨fun a b => (localHomologyInt_reduces_to_sphere 4 1).injective (Subsingleton.elim _ _)⟩

/-- **The translation local-homology iso at degree 3** `H₃(ℝ⁴, ℝ⁴∖q; ℤ) ≅ H₃(ℝ⁴, ℝ⁴∖0; ℤ)` (`y ↦ y − q`
is a homeomorphism of pairs). Degree-3 mirror of the translation piece of `localHomologyAtPointIsoInt`. -/
noncomputable def translThreeEquivInt (q : EuclideanSpace ℝ (Fin 4)) :
    RelHomologyInt (X := Eucl 4) {y | y ≠ q} 3 ≃ₗ[ℤ] RelHomologyInt (X := Eucl 4) {y | y ≠ 0} 3 :=
  LinearEquiv.ofBijective (RelHomologyInt.map (transl q) (mapsTo_transl q) 3)
    (RelHomologyInt.map_bijective_of_comp_id (transl q) (transl (-q)) (mapsTo_transl q)
      (mapsTo_transl_neg q) (transl_neg_comp_transl q) (transl_comp_transl_neg q) 3)

/-- **The degree-3 chart↔excision transport** `H₃(M, M∖x; ℤ) ≅ H₃(ℝ⁴, ℝ⁴∖0; ℤ)`. Degree-3 mirror of
`chartLocalIsoInt` (excise `M∖U` to a chart domain, transport by the chart homeo of pairs to `(V, V∖q) ⊆
ℝ⁴`, excise `ℝ⁴∖V`, translate `q ↦ 0`). -/
noncomputable def chartLocalThreeEquivInt {M : TopCat} [T1Space ↑M] {x : ↑M} {U : Set ↑M} (hU : IsOpen U)
    (hx : x ∈ U) {q : ↑(Eucl 4)} {V : Set ↑(Eucl 4)} (hV : IsOpen V)
    (hq : q ∈ V) (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl 4)) = q) :
    RelHomologyInt (X := M) {y | y ≠ x} 3 ≃ₗ[ℤ] RelHomologyInt (X := Eucl 4) {y | y ≠ 0} 3 :=
  (openPointExcisionEquivInt hU hx 2).symm.trans
    ((chartPairEquivInt hx e hex 3).trans
      ((openPointExcisionEquivInt hV hq 2).trans (translThreeEquivInt q)))

/-- **The below-top local homology of a `T1` topological 4-manifold vanishes at degree 3**:
`H₃(M, M∖x; ℤ) = 0`, by transporting the Euclidean-model vanishing along `chartLocalThreeEquivInt`. -/
theorem manifoldLocalHomologyThree_trivialInt {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) :
    Subsingleton (RelHomologyInt (X := TopCat.of M) {y | y ≠ x} 3) := by
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  haveI := euclLocalHomologyThree_trivialInt
  let c := chartAt (EuclideanSpace ℝ (Fin 4)) x
  have e := chartLocalThreeEquivInt (M := TopCat.of M) (x := x) (U := c.source) (V := c.target)
    (q := c x) c.open_source (mem_chart_source _ x) c.open_target (mem_chart_target _ x)
    c.toHomeomorphSourceTarget rfl
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- **Below-top local-homology freeness**: `Module.Free ℤ (RelHomologyInt {x}ᶜ 3)` at every point of a
`T1` topological 4-manifold — the trivial module is free. Discharges the D⁰ base case's carried `[Free H₃]`
posit. -/
theorem free_relHomologyThreeInt {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) :
    Module.Free ℤ (RelHomologyInt (X := TopCat.of M) {y | y ≠ x} 3) :=
  haveI := manifoldLocalHomologyThree_trivialInt x
  Module.Free.of_subsingleton ℤ _

end SKEFTHawking.SingularLocalHomologyThreeInt
