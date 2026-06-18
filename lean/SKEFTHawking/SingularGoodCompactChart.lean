import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularGoodCompact
import SKEFTHawking.SingularGoodCompactEuclidean

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4m) — `goodCompact` transported through a chart (Hatcher step 4)

The single-chart base case for the manifold-level fundamental-class assembly: a compact `K ⊆ M`
contained in a chart domain `U`, matched by the chart homeomorphism `e : U ≃ₜ V` to a compact
`C ⊆ ℝⁿ` (`hcompat`), is `goodCompact (m+2) K`. This transports the **arbitrary**-compact Euclidean
result `SingularGoodCompactEuclidean.goodCompact_eucl_compact` (Hatcher 3.27 step 3) through the chart,
mirroring `SingularManifoldFundamentalClass.manifoldConvexLocalHomology_high` /
`SingularDeterminedConvex.determinedByPoints_convexChart` but with the **convex** base swapped for the
general compact one — so the determined-by-points transport is now natural in **every** point of `K`,
not just the chart centre.

* `vanishAbove_chart` — the high-degree half, a verbatim re-run of `manifoldConvexLocalHomology_high`
  with `vanishAbove_eucl_compact` in place of `euclConvexLocalHomology_high`.
* `determinedByPoints_chart` — the degree-`n` half: the transport equiv `TK : Hₘ₊₂(M|K) ≅ Hₘ₊₂(ℝⁿ|C)`
  carries the per-point restrictions (`restrictToPoint_chart_nat`), so a class restricting to `0` at
  every point of `K` maps to one restricting to `0` at every point of `C`, hence `0` by
  `determinedByPoints_eucl_compact`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularRelativeFunctoriality SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularManifoldFundamentalClass

namespace SKEFTHawking.SingularGoodCompactChart

/-- **The high-degree vanishing half, transported through a chart**: `Hᵢ(M | K) = 0` for `i > m+2`,
for `K` a compact chart set matched to a compact `C ⊆ ℝⁿ`. Verbatim `manifoldConvexLocalHomology_high`
with `vanishAbove_eucl_compact` (the arbitrary-compact step-3 result) closing the Euclidean side. -/
theorem vanishAbove_chart {M : TopCat} {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCcomp : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K) :
    vanishAbove (m + 2) K := by
  intro i hi x
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 + 1 := ⟨i - 2, by omega⟩
  have e' := (openSetExcisionEquiv hK hU hKU (k + 1)).symm.trans
    ((chartPairEquiv_set e hcompat (k + 1 + 1)).trans
      (openSetExcisionEquiv hCcomp.isClosed hV hCV (k + 1)))
  exact e'.injective (by
    rw [map_zero]
    exact SingularGoodCompactEuclidean.vanishAbove_eucl_compact hCcomp (k + 1 + 1) (by omega) (e' x))

/-- **The degree-`n` half, transported through a chart**: a class in `Hₘ₊₂(M | K)` restricting to `0`
at every point of `K` is `0`, for `K` a compact chart set matched to a compact `C ⊆ ℝⁿ`. The bulk
transport equiv `TK : Hₘ₊₂(M|K) ≅ Hₘ₊₂(ℝⁿ|C)` carries the per-point restriction `restrictToPoint hxK`
to the Euclidean `restrictToPoint hc` (`hnat`, the naturality square parametrised over **every** point
`x ∈ K`, not just the chart centre as in `determinedByPoints_convexChart`), so `TK α` restricts to `0`
at every point of `C` and is `0` by `determinedByPoints_eucl_compact`. -/
theorem determinedByPoints_chart {M : TopCat} [T1Space ↑M] {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCcomp : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K) :
    determinedByPoints (m + 2) K := by
  intro α hα
  set TK : RelativeHomology (X := M) Kᶜ (m + 2)
      ≃ₗ[ZMod 2] RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2)) Cᶜ (m + 2) :=
    (openSetExcisionEquiv hK hU hKU (m + 1)).symm.trans
      ((chartPairEquiv_set e hcompat (m + 2)).trans
        (openSetExcisionEquiv hCcomp.isClosed hV hCV (m + 1))) with hTK
  apply TK.injective
  rw [map_zero]
  refine SingularGoodCompactEuclidean.determinedByPoints_eucl_compact hCcomp (TK α)
    (fun c hc => ?_)
  -- The chart preimage `x₀` of `c`, and its `M`-point `xpt ∈ K`.
  have hcV : c ∈ (V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) := hCV hc
  set x₀ : ↥U := e.symm ⟨c, hcV⟩ with hx₀
  set xpt : ↑M := (x₀ : ↑M) with hxpt
  have hex₀ : e x₀ = ⟨c, hcV⟩ := by rw [hx₀, e.apply_symm_apply]
  have hexc : (e x₀ : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) = c := by rw [hex₀]
  have hxK : xpt ∈ K := (hcompat x₀).mp (by rw [hexc]; exact hc)
  have hxptU : xpt ∈ U := x₀.2
  -- Point-version chart compatibility: `e u = c ↔ u = x₀` (modulo coercions).
  have hcompat' : ∀ u : ↥U,
      ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
          ∈ ({c} : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))))
        ↔ (u : ↑M) ∈ ({xpt} : Set ↑M) := by
    intro u
    simp only [Set.mem_singleton_iff, hxpt]
    rw [← hexc, Subtype.coe_inj, e.injective.eq_iff, Subtype.coe_inj]
  -- The point-transport equiv `Tx` (first three steps of the local model, point version).
  set Tx : RelativeHomology (X := M) ({xpt}ᶜ) (m + 2)
      ≃ₗ[ZMod 2] RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2)) ({c}ᶜ) (m + 2) :=
    (openSetExcisionEquiv isClosed_singleton hU
        (Set.singleton_subset_iff.mpr hxptU) (m + 1)).symm.trans
      ((chartPairEquiv_set e hcompat' (m + 2)).trans
        (openSetExcisionEquiv isClosed_singleton hV
          (Set.singleton_subset_iff.mpr hcV) (m + 1))) with hTx
  have hKxpt : (Kᶜ : Set ↑M) ⊆ {xpt}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxK)
  have hCc' : (Cᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ⊆ {c}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hc)
  -- Naturality: `Tx ∘ restrictToPoint hxK = restrictToPoint hc ∘ TK` (the three transport steps).
  have hnat : Tx (restrictToPoint hxK (m + 2) α) = restrictToPoint hc (m + 2) (TK α) := by
    simp only [hTK, hTx, LinearEquiv.trans_apply]
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
    have hstep2 : ∀ β, chartPairEquiv_set e hcompat' (m + 2)
          (relIncl (Set.preimage_mono hKxpt) (m + 2) β)
          = relIncl (Set.preimage_mono hCc') (m + 2) (chartPairEquiv_set e hcompat (m + 2) β) :=
      fun β => relIncl_map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (Set.preimage_mono hKxpt)
        (mapsTo_chart_set e hcompat) (mapsTo_chart_set e hcompat') (Set.preimage_mono hCc')
        (m + 2) β
    have hstep3 : ∀ γ, openSetExcisionEquiv isClosed_singleton hV
          (Set.singleton_subset_iff.mpr hcV) (m + 1) (relIncl (Set.preimage_mono hCc') (m + 2) γ)
          = restrictToPoint hc (m + 2)
              (openSetExcisionEquiv hCcomp.isClosed hV hCV (m + 1) γ) :=
      fun γ => (relIncl_excisionMap hCc' (m + 2) γ).symm
    rw [hstep1, hstep2, hstep3]
  rw [← hnat, hα xpt hxK, map_zero]

/-- **A compact chart set is `goodCompact`** (Hatcher step 4 base case): combine `vanishAbove_chart`
and `determinedByPoints_chart`. The single-chart piece the manifold-level finite-union compactness
induction stacks on toward the fundamental class `[M]`. -/
theorem goodCompact_chart {M : TopCat} [T1Space ↑M] {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCcomp : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K) :
    SKEFTHawking.SingularGoodCompact.goodCompact (X := M) (m + 2) K :=
  ⟨vanishAbove_chart hK hU hKU hCcomp hV hCV e hcompat,
   determinedByPoints_chart hK hU hKU hCcomp hV hCV e hcompat⟩

end SKEFTHawking.SingularGoodCompactChart
