/-
# Phase 5q.H (E1 CSC-PD tower) — chart-convex stage below-top freeness `Free H₃(M|K)` (integral)

The integral below-top companion to the top-degree `restrictToPointInt_convexChart_bijective`: for a
compact stage `K` of a chart-convex open (chart `e : U ≃ₜ V` carrying `K` exactly onto a convex compact
`C ⊆ V ⊆ ℝ⁴`), the BELOW-top relative homology `H₃(M, M∖K; ℤ) = 0`. Transport the Euclidean convex-compact
middle vanishing `vanishMiddle_convexCompactInt` (`H₃(ℝ⁴, ℝ⁴∖C; ℤ) = 0`) back through excise → chart-pair →
excise (the set-level transport of `SingularConvexStageIso`, over ℤ, reusing the coefficient-free
`mapsTo_chart_stage`). Freeness of the trivial module follows.

This discharges the stage freeness `[Module.Free ℤ (RelHomologyInt (↑K'.1)ᶜ 3)]` that the B4c injectivity
flip (`relKroneckerHInt_flip_bijective_of_equiv` at a chart-convex-absorbed stage) needs over ℤ — mod-2 got
it for free from the field.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularRelativeFunctorialityInt
import SKEFTHawking.SingularConvexRadialMiddleInt
import SKEFTHawking.SingularConvexStageIso

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt)
open SKEFTHawking.SingularRelativeFunctorialityInt
  (RelHomologyInt.map RelHomologyInt.map_bijective_of_comp_id)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularConvexStageIso (mapsTo_chart_stage mapsTo_chart_stage_symm)
open SKEFTHawking.SingularConvexRadialMiddleInt (vanishMiddle_convexCompactInt)

namespace SKEFTHawking.SingularConvexStageIsoInt

/-- **Open-set excision** (integral) `Hₙ₊₁(V, V∖K; ℤ) ≅ Hₙ₊₁(X, X∖K; ℤ)`: integral mirror of
`SingularConvexStageIso.openSetExcisionEquiv` (`excisionEquivInt` at the cover `{X∖K, V}`). -/
noncomputable def openSetExcisionEquivInt {X : TopCat} {K V : Set ↑X}
    (hK : IsClosed K) (hV : IsOpen V) (hKV : K ⊆ V) (n : ℕ) :
    RelHomologyInt (restr (Kᶜ) V) (n + 1) ≃ₗ[ℤ] RelHomologyInt (Kᶜ) (n + 1) :=
  excisionEquivInt (Kᶜ) V n (by
    rw [Set.biUnion_pair, hK.isOpen_compl.interior_eq, hV.interior_eq, Set.eq_univ_iff_forall]
    intro x
    by_cases h : x ∈ K
    · exact Or.inr (hKV h)
    · exact Or.inl h)

/-- **The chart-pair homeomorphism induces an integral relative-homology iso at a carried stage**
`Hₖ(U, U∖K; ℤ) ≅ Hₖ(V, V∖C; ℤ)`: integral mirror of `SingularConvexStageIso.chartStagePairEquiv`
(reusing the coefficient-free `mapsTo_chart_stage`). -/
noncomputable def chartStagePairEquivInt {M : TopCat} {m : ℕ} {U : Set ↑M} {V : Set ↑(Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V) {KS : Set ↑M} {CS : Set ↑(Eucl (m + 2))}
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 2))) ∈ CS) ↔ (u : ↑M) ∈ KS) (k : ℕ) :
    RelHomologyInt (restr (KSᶜ) U) k ≃ₗ[ℤ] RelHomologyInt (restr (CSᶜ) V) k :=
  LinearEquiv.ofBijective
    (RelHomologyInt.map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (mapsTo_chart_stage e hcompat) k)
    (RelHomologyInt.map_bijective_of_comp_id (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V)))
      (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U)))
      (mapsTo_chart_stage e hcompat) (mapsTo_chart_stage_symm e hcompat)
      (ContinuousMap.ext fun v => e.symm_apply_apply v)
      (ContinuousMap.ext fun u => e.apply_symm_apply u) k)

/-- **The degree-3 chart-stage transport** `H₃(M, M∖K; ℤ) ≅ H₃(ℝ⁴, ℝ⁴∖C; ℤ)` for a chart-convex stage. -/
noncomputable def chartStageThreeEquivInt {M : TopCat} {U : Set ↑M} {V : Set ↑(Eucl 4)}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    {KS : Set ↑M} (hKcl : IsClosed KS) (hKU : KS ⊆ U)
    {CS : Set ↑(Eucl 4)} (hCcl : IsClosed CS) (hCV : CS ⊆ V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl 4)) ∈ CS) ↔ (u : ↑M) ∈ KS) :
    RelHomologyInt (X := M) (KSᶜ) 3 ≃ₗ[ℤ] RelHomologyInt (X := Eucl 4) (CSᶜ) 3 :=
  (openSetExcisionEquivInt hKcl hU hKU 2).symm.trans
    ((chartStagePairEquivInt (m := 2) e hcompat 3).trans
      (openSetExcisionEquivInt (X := Eucl 4) hCcl hV hCV 2))

/-- **Chart-convex stage below-top vanishing** `H₃(M, M∖K; ℤ) = 0`, by transporting the Euclidean
convex-compact middle vanishing along `chartStageThreeEquivInt`. -/
theorem stage3_convexChart_trivialInt {M : TopCat} {U : Set ↑M} {V : Set ↑(Eucl 4)}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    {KS : Set ↑M} (hKcl : IsClosed KS) (hKU : KS ⊆ U)
    {CS : Set ↑(Eucl 4)} (hCconv : Convex ℝ CS) (hCcomp : IsCompact CS) (hCV : CS ⊆ V)
    {O : EuclideanSpace ℝ (Fin 4)} (hOC : O ∈ CS)
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl 4)) ∈ CS) ↔ (u : ↑M) ∈ KS) :
    Subsingleton (RelHomologyInt (X := M) (KSᶜ) 3) := by
  haveI : Subsingleton (RelHomologyInt (X := Eucl 4) (CSᶜ) 3) :=
    ⟨fun a b => by
      rw [vanishMiddle_convexCompactInt hCconv hCcomp hOC 3 (by omega) (by omega) a,
          vanishMiddle_convexCompactInt hCconv hCcomp hOC 3 (by omega) (by omega) b]⟩
  exact ⟨fun a b =>
    (chartStageThreeEquivInt hU hV e hKcl hKU hCcomp.isClosed hCV hcompat).injective
      (Subsingleton.elim _ _)⟩

/-- **Chart-convex stage below-top freeness** `Module.Free ℤ (RelHomologyInt (Kᶜ) 3)` — the trivial module
is free. Discharges the B4c injectivity flip's stage freeness over ℤ. -/
theorem free_stage3_convexChartInt {M : TopCat} {U : Set ↑M} {V : Set ↑(Eucl 4)}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    {KS : Set ↑M} (hKcl : IsClosed KS) (hKU : KS ⊆ U)
    {CS : Set ↑(Eucl 4)} (hCconv : Convex ℝ CS) (hCcomp : IsCompact CS) (hCV : CS ⊆ V)
    {O : EuclideanSpace ℝ (Fin 4)} (hOC : O ∈ CS)
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl 4)) ∈ CS) ↔ (u : ↑M) ∈ KS) :
    Module.Free ℤ (RelHomologyInt (X := M) (KSᶜ) 3) :=
  haveI := stage3_convexChart_trivialInt hU hV e hKcl hKU hCconv hCcomp hCV hOC hcompat
  Module.Free.of_subsingleton ℤ _

end SKEFTHawking.SingularConvexStageIsoInt
