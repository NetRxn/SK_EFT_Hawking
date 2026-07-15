/-
# Phase 5q.H (W-A arm 4) — the above-top local vanishing `H_{m'+3}(M, M∖σ) = 0` and the `puncV` flank

Route-B δ-closer flank #1. In the relative-MV LES that computes the punctured-product local homology
`H_{m'+3}(M×I, {x}ᶜ)` (`…PuncturedCover`/`…PuncturedMVBookkeeping`), the `puncV`-piece flank sits in the
TOP target degree `m'+3`. This module proves it VANISHES:

  `H_{m'+3}(M×I, (M∖σ)×I) = 0`,

by reducing (interval-factor collapse, `puncVPieceEquiv`) to the **above-top local homology of the base**

  `H_{m'+3}(M, M∖σ) = 0`   (M a `T1` charted `(m'+2)`-manifold, σ ∈ M).

The base vanishing is the mirror, ONE DEGREE UP, of `SingularChartBridge.manifoldLocalIso`
(`H_{m'+2}(M, M∖σ) ≅ ℤ/2`): the SAME chart↔excision bridge (`openPointExcisionEquiv`/`chartPairEquiv`,
both degree-general) transports `H_{m'+3}(M, {σ}ᶜ)` to the translated Euclidean local model
`H_{m'+3}(ℝⁿ, ℝⁿ∖q)`; there the connecting iso (`ℝⁿ` acyclic) and the punctured-space retract
(`normalize`, `ℝⁿ∖0 ≃ Sⁿ⁻¹`) identify it with `H_{m'+2}(S^{m'+1})`, which vanishes by
`SingularSphereHighDegree.sphere_homology_high` (`m'+1 < m'+2`). No new sphere machinery — the top
local iso spent `H_{m'+1}(S^{m'+1}) ≅ ℤ/2`; one degree up spends `H_{m'+2}(S^{m'+1}) = 0`.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the Euclidean model at `0`** `euclLocalHom_above_eq_zero`: `H_{m+3}(ℝ^{m+2}, ℝ^{m+2}∖0) = 0`.
* **§2 — the Euclidean model at any `q`** `euclLocalHom_above_point_eq_zero` (translation-invariant).
* **§3 — the manifold base** `manifoldLocalHom_above_eq_zero`: `H_{m'+3}(M, M∖σ) = 0` via the chart bridge.
* **§4 — the `puncV` flank** `puncV_localHom_above_eq_zero` and its finrank corollary
  `finrank_puncV_localHom_above` (`= 0`): `H_{m'+3}(M×I, (M∖σ)×I) = 0`, the top-degree `puncV` piece
  the relative-MV LES dimension count needs.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularChartBridge
import SKEFTHawking.SingularSphereHighDegree
import SKEFTHawking.SingularLocalHomology
import SKEFTHawking.SingularPuncturedRetract
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPiece

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularEuclideanAcyclic
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularLocalHomology
open SKEFTHawking.SingularPuncturedRetract
open SKEFTHawking.SingularSphereHighDegree
open SKEFTHawking.SingularLocalModelChart
open SKEFTHawking.SingularChartBridge
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPiece

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedTopVanish

noncomputable section

/-! ## §1. The Euclidean local model at the origin, one degree above top -/

/-- **The above-top Euclidean local homology, identified with `H_{m+2}(S^{m+1})`.** The connecting iso
`H_{m+3}(ℝ^{m+2}, ℝ^{m+2}∖0) ≅ H_{m+2}(ℝ^{m+2}∖0)` (`ℝ^{m+2}` acyclic, `connecting_eucl_bijective`)
composed with the deformation retract `ℝ^{m+2}∖0 ≃ S^{m+1}` (`homology_map_normalize_bijective`) — the
mirror, one degree up, of `localHomologyIso`'s `H_{m+2}(ℝ^{m+2}, ℝ^{m+2}∖0) ≅ H_{m+1}(S^{m+1}) ≅ ℤ/2`. -/
def euclLocalHomAboveEquiv (m : ℕ) :
    RelativeHomology (X := Eucl (m + 2)) {x | x ≠ 0} (m + 3) ≃ₗ[ZMod 2]
      Homology (SingularSphereAcyclic.Sph (m + 1)) (m + 2) :=
  (LinearEquiv.ofBijective _ (connecting_eucl_bijective (m + 2) (m + 1))).trans
    (LinearEquiv.ofBijective _ (homology_map_normalize_bijective (n := m + 2) (m + 1)))

/-- **The above-top Euclidean local homology vanishes**: `H_{m+3}(ℝ^{m+2}, ℝ^{m+2}∖0) = 0`. Its image
under `euclLocalHomAboveEquiv` lies in `H_{m+2}(S^{m+1})`, which vanishes by `sphere_homology_high`
(`m+1 < m+2`). -/
theorem euclLocalHom_above_eq_zero (m : ℕ)
    (y : RelativeHomology (X := Eucl (m + 2)) {x | x ≠ 0} (m + 3)) : y = 0 := by
  refine (euclLocalHomAboveEquiv m).injective ?_
  rw [map_zero]
  exact sphere_homology_high (m + 1) (m + 2) (by omega) _

/-! ## §2. The Euclidean local model at an arbitrary point (translation-invariant) -/

/-- **The translation iso** `H_{m+3}(ℝ^{m+2}, ℝ^{m+2}∖p) ≅ H_{m+3}(ℝ^{m+2}, ℝ^{m+2}∖0)` — the
degree-`(m+3)` analogue of `localHomologyAtPointIso`'s bijection, `y ↦ y - p`. -/
def euclLocalHomAbovePointEquiv (m : ℕ) (p : EuclideanSpace ℝ (Fin (m + 2))) :
    RelativeHomology (X := Eucl (m + 2)) {y | y ≠ p} (m + 3) ≃ₗ[ZMod 2]
      RelativeHomology (X := Eucl (m + 2)) {y | y ≠ 0} (m + 3) :=
  LinearEquiv.ofBijective (RelativeHomology.map (transl p) (mapsTo_transl p) (m + 3))
    (RelativeHomology.map_bijective_of_comp_id (transl p) (transl (-p)) (mapsTo_transl p)
      (mapsTo_transl_neg p) (transl_neg_comp_transl p) (transl_comp_transl_neg p) (m + 3))

/-- **The above-top Euclidean local homology at any point vanishes**: `H_{m+3}(ℝ^{m+2}, ℝ^{m+2}∖p) = 0`. -/
theorem euclLocalHom_above_point_eq_zero (m : ℕ) (p : EuclideanSpace ℝ (Fin (m + 2)))
    (y : RelativeHomology (X := Eucl (m + 2)) {y | y ≠ p} (m + 3)) : y = 0 := by
  refine (euclLocalHomAbovePointEquiv m p).injective ?_
  rw [map_zero]
  exact euclLocalHom_above_eq_zero m _

/-! ## §3. The manifold base: `H_{m'+3}(M, M∖σ) = 0` via the chart↔excision bridge -/

/-- **The chart-transport iso, one degree above top** `H_{m+3}(M, M∖x) ≅ H_{m+3}(ℝ^{m+2}, ℝ^{m+2}∖q)`.
The `chartLocalIso` composition (`openPointExcisionEquiv`/`chartPairEquiv`, both degree-general) at
degree `m+3` instead of `m+2` — WITHOUT the terminal local-model iso, since the model here vanishes. -/
def chartLocalAboveEquiv {M : TopCat} [T1Space ↑M] {x : ↑M} {U : Set ↑M} (hU : IsOpen U)
    (hx : x ∈ U) {m : ℕ} {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (hV : IsOpen V)
    (hq : q ∈ V) (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q) :
    RelativeHomology (X := M) {y | y ≠ x} (m + 3) ≃ₗ[ZMod 2]
      RelativeHomology (X := Eucl (m + 2)) {y | y ≠ q} (m + 3) :=
  (openPointExcisionEquiv hU hx (m + 2)).symm.trans
    ((chartPairEquiv hx e hex (m + 3)).trans (openPointExcisionEquiv hV hq (m + 2)))

/-- **The above-top local homology of a chart vanishes**: transport `H_{m+3}(M, M∖x) ≅
H_{m+3}(ℝ^{m+2}, ℝ^{m+2}∖q)` and use the model vanishing. -/
theorem chartLocalHom_above_eq_zero {M : TopCat} [T1Space ↑M] {x : ↑M} {U : Set ↑M} (hU : IsOpen U)
    (hx : x ∈ U) {m : ℕ} {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (hV : IsOpen V)
    (hq : q ∈ V) (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q)
    (y : RelativeHomology (X := M) {y | y ≠ x} (m + 3)) : y = 0 := by
  refine (chartLocalAboveEquiv hU hx hV hq e hex).injective ?_
  rw [map_zero]
  exact euclLocalHom_above_point_eq_zero m q _

/-- **The above-top local homology of a topological manifold vanishes**: for `M` a `T1` topological
manifold modelled on `ℝ^{m'+2}`, `H_{m'+3}(M, M∖σ) = 0` at every point `σ`. The mirror, one degree up,
of `SingularChartBridge.manifoldLocalIso` (`H_{m'+2}(M, M∖σ) ≅ ℤ/2`). This is the flank #1 input the
relative-MV LES dimension count needs. -/
theorem manifoldLocalHom_above_eq_zero {m' : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] (x : M)
    (y : RelativeHomology (X := TopCat.of M) {y | y ≠ x} (m' + 3)) : y = 0 := by
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  let c := chartAt (EuclideanSpace ℝ (Fin (m' + 2))) x
  exact chartLocalHom_above_eq_zero (M := TopCat.of M) (x := x) (U := c.source) (V := c.target)
    (q := c x) c.open_source (mem_chart_source _ x) c.open_target (mem_chart_target _ x)
    c.toHomeomorphSourceTarget rfl y

/-! ## §4. The `puncV` flank: `H_{m'+3}(M×I, (M∖σ)×I) = 0` -/

/-- **The top-degree `puncV` MV piece vanishes**: `H_{m'+3}(M×I, (M∖σ)×I) = 0`. The interval-factor
collapse `puncVPieceEquiv` (degree-general) identifies it with the base above-top local homology
`H_{m'+3}(M, M∖σ)`, which vanishes (`manifoldLocalHom_above_eq_zero`). This is the `puncV` flank in the
TOP target degree `m'+3` of the relative-MV LES — the vanishing summand of the dimension count. -/
theorem puncV_localHom_above_eq_zero {m' : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] (x : ↑(cyl (TopCat.of M)))
    (y : RelativeHomology (X := cyl (TopCat.of M)) (puncV x) (m' + 3)) : y = 0 := by
  refine (puncVPieceEquiv x (m' + 2)).symm.injective ?_
  rw [map_zero]
  exact manifoldLocalHom_above_eq_zero x.1 _

/-- **`dim H_{m'+3}(M×I, (M∖σ)×I) = 0`** — the finrank form of the top-degree `puncV` vanishing, the
value the relative-MV LES flank bound (`…PuncturedMVBookkeeping.puncMv_target_finrank_le`) plugs in for
the `puncV` summand. -/
theorem finrank_puncV_localHom_above {m' : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] (x : ↑(cyl (TopCat.of M))) :
    Module.finrank (ZMod 2) (RelativeHomology (X := cyl (TopCat.of M)) (puncV x) (m' + 3)) = 0 := by
  have : Subsingleton (RelativeHomology (X := cyl (TopCat.of M)) (puncV x) (m' + 3)) :=
    ⟨fun a b => by rw [puncV_localHom_above_eq_zero x a, puncV_localHom_above_eq_zero x b]⟩
  exact Module.finrank_zero_of_subsingleton

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedTopVanish
