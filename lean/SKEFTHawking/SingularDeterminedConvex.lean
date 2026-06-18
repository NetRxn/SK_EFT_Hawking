import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularConvexRestrictionIso

/-!
# Phase 5q.F (w₂-foundation) — the `determinedByPoints` half of Hatcher 3.27 for a convex chart

The convex base case of Hatcher 3.27's *degree-`n`* statement: a compact convex chart set `K`
satisfies `determinedByPoints (m+2) K` — every class in `Hₘ₊₂(M | K)` whose restriction to
`Hₘ₊₂(M | x)` vanishes for all `x ∈ K` is itself `0`.

The proof is a transport-conjugation: `restrictToPoint hxK (m+2)` (the inclusion-of-pairs map
`Hₘ₊₂(M | K) → Hₘ₊₂(M | x₀)` for the chart-center `x₀`) is conjugate via the chart/excision transport
equivs (the first three steps of `manifoldConvexLocalHomologyIso`, without the final Euclidean local
model) to the Euclidean convex restriction `Hₘ₊₂(ℝⁿ | C) → Hₘ₊₂(ℝⁿ | 0)`, which is bijective by
`SingularConvexRestrictionIso.restrictToPoint_bijective`. Hence `restrictToPoint hxK (m+2)` is
injective, and the determined-by-points condition (which forces `restrictToPoint hxK (m+2) α = 0`)
gives `α = 0`. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularRelativeFunctoriality SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularManifoldFundamentalClass

namespace SKEFTHawking.SingularDeterminedConvex

theorem determinedByPoints_convexChart {M : TopCat} [T1Space ↑M] {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCconv : Convex ℝ C) (hCcomp : IsCompact C)
    (hC0 : C ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + 2)))) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K) :
    determinedByPoints (m + 2) K := by
  have h0C : (0 : EuclideanSpace ℝ (Fin (m + 2))) ∈ C := mem_of_mem_nhds hC0
  set q : ↥V := ⟨(0 : EuclideanSpace ℝ (Fin (m + 2))), hCV h0C⟩ with hq
  set x₀ : ↥U := e.symm q with hx₀
  set xpt : ↑M := (x₀ : ↑M) with hxpt
  have hex₀ : e x₀ = q := by rw [hx₀, e.apply_symm_apply]
  have hxK : xpt ∈ K := by
    refine (hcompat x₀).mp ?_
    rw [hex₀]
    exact h0C
  -- It suffices that the restriction to the single chart-center point `xpt` is injective.
  suffices hinj : Function.Injective (restrictToPoint (X := M) hxK (m + 2)) by
    intro α hα
    exact hinj (by rw [hα xpt hxK, map_zero])
  -- The Eucl-side center point is `0` (= `(q : Eucl)`); the M-side center point is `xpt = x₀`.
  -- The point-version chart compatibility: `e u = 0 ↔ u = x₀` (modulo coercions).
  have hcompat' : ∀ u : ↥U,
      ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
          ∈ ({(0 : EuclideanSpace ℝ (Fin (m + 2)))} : Set _)) ↔ (u : ↑M) ∈ ({xpt} : Set ↑M) := by
    intro u
    simp only [Set.mem_singleton_iff, hxpt]
    rw [show (0 : ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
          = (q : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) from rfl, ← hex₀,
      Subtype.coe_inj, e.injective.eq_iff, Subtype.coe_inj]
  -- The two transport equivs (first three steps of `manifoldConvexLocalHomologyIso`).
  set TK : RelativeHomology (X := M) Kᶜ (m + 2)
      ≃ₗ[ZMod 2] RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2)) Cᶜ (m + 2) :=
    (openSetExcisionEquiv hK hU hKU (m + 1)).symm.trans
      ((chartPairEquiv_set e hcompat (m + 2)).trans
        (openSetExcisionEquiv hCcomp.isClosed hV hCV (m + 1))) with hTK
  have hxptU : xpt ∈ U := x₀.2
  have h0V : (0 : EuclideanSpace ℝ (Fin (m + 2)))
      ∈ (V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) := q.2
  set Tx : RelativeHomology (X := M) ({xpt}ᶜ) (m + 2)
      ≃ₗ[ZMod 2] RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2))
          ({(0 : EuclideanSpace ℝ (Fin (m + 2)))}ᶜ) (m + 2) :=
    (openSetExcisionEquiv isClosed_singleton hU
        (Set.singleton_subset_iff.mpr hxptU) (m + 1)).symm.trans
      ((chartPairEquiv_set e hcompat' (m + 2)).trans
        (openSetExcisionEquiv isClosed_singleton hV
          (Set.singleton_subset_iff.mpr h0V) (m + 1))) with hTx
  -- The Euclidean convex restriction is bijective (Brick B), hence injective.
  have hEuclInj : Function.Injective
      (restrictToPoint (X := SingularEuclideanAcyclic.Eucl (m + 2)) h0C (m + 2)) :=
    (SingularConvexRestrictionIso.restrictToPoint_bijective m hCconv hCcomp hC0).injective
  -- The naturality square: `Tx ∘ restrictToPoint hxK = restrictToPoint h0C ∘ TK`.
  -- The four `relIncl` "vertical" maps in the square (on `M`, on `restr · U`, on `restr · V`, on `ℝⁿ`).
  have hKxpt : (Kᶜ : Set ↑M) ⊆ {xpt}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxK)
  have hC0' : (Cᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ⊆ {0}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr h0C)
  have hnat : ∀ α : RelativeHomology (X := M) Kᶜ (m + 2),
      Tx (restrictToPoint hxK (m + 2) α)
        = restrictToPoint (X := SingularEuclideanAcyclic.Eucl (m + 2)) h0C (m + 2) (TK α) := by
    intro α
    simp only [hTK, hTx, LinearEquiv.trans_apply]
    -- Step 1 (M-side excision, `.symm` direction): push `restrictToPoint hxK` past `excise⁻¹`.
    have hstep1 : (openSetExcisionEquiv isClosed_singleton hU
          (Set.singleton_subset_iff.mpr hxptU) (m + 1)).symm
            ((restrictToPoint hxK (m + 2)) α)
          = relIncl (Set.preimage_mono hKxpt) (m + 2)
              ((openSetExcisionEquiv hK hU hKU (m + 1)).symm α) := by
      apply (openSetExcisionEquiv isClosed_singleton hU (Set.singleton_subset_iff.mpr hxptU)
        (m + 1)).injective
      rw [LinearEquiv.apply_symm_apply]
      show (restrictToPoint hxK (m + 2)) α
        = excisionMap {xpt}ᶜ U (m + 2)
            (relIncl (Set.preimage_mono hKxpt) (m + 2)
              ((openSetExcisionEquiv hK hU hKU (m + 1)).symm α))
      rw [← relIncl_excisionMap hKxpt (m + 2)]
      show (restrictToPoint hxK (m + 2)) α
        = relIncl hKxpt (m + 2)
            ((openSetExcisionEquiv hK hU hKU (m + 1))
              ((openSetExcisionEquiv hK hU hKU (m + 1)).symm α))
      rw [LinearEquiv.apply_symm_apply]
      rfl
    -- Step 2 (chart-transport): `relIncl` commutes with the chart-pair map `RelativeHomology.map e`.
    have hstep2 : ∀ β, chartPairEquiv_set e hcompat' (m + 2)
          (relIncl (Set.preimage_mono hKxpt) (m + 2) β)
          = relIncl (Set.preimage_mono hC0') (m + 2) (chartPairEquiv_set e hcompat (m + 2) β) :=
      fun β => relIncl_map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (Set.preimage_mono hKxpt)
        (mapsTo_chart_set e hcompat) (mapsTo_chart_set e hcompat') (Set.preimage_mono hC0')
        (m + 2) β
    -- Step 3 (Eucl-side excision): `relIncl` commutes with `excisionMap` (`= restrictToPoint h0C`).
    have hstep3 : ∀ γ, openSetExcisionEquiv isClosed_singleton hV
          (Set.singleton_subset_iff.mpr h0V) (m + 1) (relIncl (Set.preimage_mono hC0') (m + 2) γ)
          = restrictToPoint h0C (m + 2)
              (openSetExcisionEquiv hCcomp.isClosed hV hCV (m + 1) γ) :=
      fun γ => (relIncl_excisionMap hC0' (m + 2) γ).symm
    rw [hstep1, hstep2, hstep3]
  -- Injectivity chase through the square.
  rw [injective_iff_map_eq_zero]
  intro α hα
  have h1 : restrictToPoint (X := SingularEuclideanAcyclic.Eucl (m + 2)) h0C (m + 2) (TK α) = 0 := by
    rw [← hnat, hα, map_zero]
  have h2 : TK α = 0 := hEuclInj (by rw [h1, map_zero])
  exact TK.injective (by rw [h2, map_zero])

end SKEFTHawking.SingularDeterminedConvex
