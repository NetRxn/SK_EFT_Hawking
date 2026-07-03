import Mathlib
import SKEFTHawking.SingularConvexRadialMiddle
import SKEFTHawking.SingularCSCVanishAbove

/-!
# Phase 5q.G (G1 PD-induction, base-case B3) — CSC vanishing on chart-convex opens (part 1)

`exists_convex_compact_between`: a compact subset of an open convex set in a finite-dimensional
real normed space is sandwiched by a CONVEX compact inside the open set (containing any chosen
point). Mathlib lacks `IsCompact.convexHull`; this glues the per-point finset-hull neighborhoods
(`Convex.exists_subset_interior_convexHull_finset_of_isCompact` at singletons) by compactness and
takes the hull of the resulting finite union — `Set.Finite.isCompact_convexHull` finishes.

The cofinality tool for the chart-convex CSC-vanishing (`cscOpen_eq_zero_of_chartConvex`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

namespace SKEFTHawking.SingularCSCConvexChart

/-- **Convex-compact interpolation**: `KE ⊆ C' ⊆ C` with `C'` convex compact (and `p₀ ∈ C'`),
for `KE` compact and `C` open convex in a finite-dimensional real normed space. -/
theorem exists_convex_compact_between {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {KE C : Set E}
    (hK : IsCompact KE) (hC : Convex ℝ C) (hCo : IsOpen C) (hKC : KE ⊆ C)
    {p₀ : E} (hp₀ : p₀ ∈ C) :
    ∃ C' : Set E, Convex ℝ C' ∧ IsCompact C' ∧ KE ⊆ C' ∧ C' ⊆ C ∧ p₀ ∈ C' := by
  -- Per point: a finset-hull neighborhood inside `C`.
  have hpt : ∀ x ∈ KE, ∃ u : Finset E,
      x ∈ interior (convexHull ℝ (u : Set E)) ∧ convexHull ℝ (u : Set E) ⊆ C := by
    intro x hx
    obtain ⟨u, hsu, huC⟩ := (convex_singleton x).exists_subset_interior_convexHull_finset_of_isCompact
      isCompact_singleton (hCo.mem_nhdsSet.mpr (Set.singleton_subset_iff.mpr (hKC hx)))
    exact ⟨u, hsu rfl, huC⟩
  choose! u hu₁ hu₂ using hpt
  -- The interiors cover `KE`; extract a finite subcover.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : KE => interior (convexHull ℝ (u (↑x) : Set E)))
    (fun _ => isOpen_interior)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hu₁ x hx⟩)
  -- The hull of the finite union (plus `p₀`).
  refine ⟨convexHull ℝ (insert p₀ (⋃ x ∈ t, (u (↑x) : Set E))), convex_convexHull ℝ _,
    ?_, ?_, ?_, ?_⟩
  · refine Set.Finite.isCompact_convexHull ℝ ?_
    exact Set.Finite.insert p₀ (Set.Finite.biUnion t.finite_toSet fun x _ => (u ↑x).finite_toSet)
  · intro y hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    refine convexHull_mono ?_ (interior_subset hyx)
    intro z hz
    exact Set.mem_insert_of_mem _ (Set.mem_biUnion hxt hz)
  · refine convexHull_min (Set.insert_subset hp₀ (Set.iUnion₂_subset fun x _ => ?_)) hC
    exact (subset_convexHull ℝ _).trans (hu₂ (↑x) x.2)
  · exact subset_convexHull ℝ _ (Set.mem_insert _ _)

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularConvexRadialMiddle SKEFTHawking.SingularRelCohomVanishAbove

/-- **B3: the CSC cohomology of a chart-convex open vanishes in the middle band**
(`2 ≤ k < m+2`): every compact in `W` absorbs into a chart-convex compact stage (the
`exists_convex_compact_between` hull pulled back through the chart), where the stage object
`Hᵏ(M|K')` vanishes by the chart transport to `Hᵏ(ℝᵐ⁺²|C')`, universal coefficients, and
`vanishMiddle_convexCompact`. -/
theorem cscOpen_eq_zero_of_chartConvex {M : TopCat} [T2Space ↑M] {m : ℕ}
    {U : Set ↑M} (hU : IsOpen U)
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))} (hV : IsOpen V)
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    (hCne : C.Nonempty) (hCV : C ⊆ V)
    {W : Set ↑M} (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C))
    {k : ℕ} (h2 : 2 ≤ k) (hlt : k < m + 2)
    (α : CompactlySupportedCohomologyOpen W k) : α = 0 := by
  obtain ⟨p₀, hp₀⟩ := hCne
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  refine SKEFTHawking.SingularCSCVanishAbove.cscOpen_eq_zero_of_cofinal_vanish (fun K => ?_) α
  have hKU : (↑K.1 : Set ↑M) ⊆ U := K.2.trans hWU
  -- The Euclidean image of `K` and the interpolated convex compact `C'`.
  have hKUc : IsCompact (Subtype.val ⁻¹' (↑K.1 : Set ↑M) : Set ↥U) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      Set.inter_eq_self_of_subset_right hKU]
    exact K.1.isCompact'
  set KE : Set (EuclideanSpace ℝ (Fin (m + 2))) :=
    (fun x : ↥U => (e x : ↑(SingularEuclideanAcyclic.Eucl (m + 2))))
      '' (Subtype.val ⁻¹' (↑K.1 : Set ↑M)) with hKEdef
  have hKEc : IsCompact KE :=
    hKUc.image (continuous_subtype_val.comp e.continuous)
  have hKEC : KE ⊆ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hWe x).mp (K.2 hx)
  obtain ⟨C', hC'conv, hC'comp, hKEC', hC'C, hp₀C'⟩ :=
    exists_convex_compact_between hKEc hCconv hCopen hKEC hp₀
  -- The pulled-back stage `K'`.
  set K'pre : Set ↥U := ⇑e ⁻¹' (Subtype.val ⁻¹' C') with hK'predef
  set K'set : Set ↑M := Subtype.val '' K'pre with hK'setdef
  have hK'pre_eq : K'pre = ⇑e.symm '' (Subtype.val ⁻¹' C' : Set ↥V) := by
    ext x
    constructor
    · intro hx; exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hK'predef]
      simp only [Set.mem_preimage, e.apply_symm_apply]
      exact hy
  have hC'V : C' ⊆ (V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) := hC'C.trans hCV
  have hK'c : IsCompact K'set := by
    refine IsCompact.image ?_ continuous_subtype_val
    rw [hK'pre_eq]
    refine IsCompact.image ?_ e.symm.continuous
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    rwa [Set.inter_eq_self_of_subset_right hC'V]
  have hK'W : K'set ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hWe x).mpr (hC'C hx)
  have hKK' : (↑K.1 : Set ↑M) ⊆ K'set := by
    intro z hz
    exact ⟨⟨z, hKU hz⟩, hKEC' ⟨⟨z, hKU hz⟩, hz, rfl⟩, rfl⟩
  have hcompat' : ∀ u : ↥U,
      ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C') ↔ (u : ↑M) ∈ K'set := by
    intro u
    constructor
    · intro h; exact ⟨u, h, rfl⟩
    · rintro ⟨x, hx, hxu⟩
      rwa [Subtype.val_injective hxu] at hx
  refine ⟨⟨⟨K'set, hK'c⟩, hK'W⟩, hKK', ?_⟩
  -- The stage vanishing: `Hⁿ⁺¹(M|K') = 0` by the chart transport + UC + `vanishMiddle`.
  intro x
  have hK'closed : IsClosed K'set := hK'c.isClosed
  have hK'U : K'set ⊆ U := by rintro _ ⟨u, _, rfl⟩; exact u.2
  have hHvan : ∀ β : RelativeHomology (X := M) K'setᶜ (n + 1), β = 0 := by
    intro β
    set TK := (openSetExcisionEquiv hK'closed hU hK'U n).symm.trans
      ((chartPairEquiv_set e hcompat' (n + 1)).trans
        (openSetExcisionEquiv hC'comp.isClosed hV hC'V n)) with hTKdef
    have hβT : TK β = 0 :=
      vanishMiddle_convexCompact hC'conv hC'comp hp₀C' (n + 1) h2 hlt (TK β)
    exact (LinearEquiv.map_eq_zero_iff TK).mp hβT
  exact relCohomology_eq_zero_of_relHomology_eq_zero K'setᶜ hHvan x

/-- **The chart-convex stage-absorption** (factored from `cscOpen_eq_zero_of_chartConvex`):
every compact stage `K` of a chart-convex `W` absorbs into a stage `K'` whose Euclidean image is
a convex compact `C' ∋ p₀` inside `C`, with the chart compatibility for `(K', C')` — the input
shape of the chart-pair transport and the convex stage-isos. -/
theorem exists_chartConvex_stage_above {M : TopCat} [T2Space ↑M] {m : ℕ}
    {U : Set ↑M} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    {p₀ : EuclideanSpace ℝ (Fin (m + 2))} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑M} (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C))
    (K : SKEFTHawking.SingularCompactsInOpen.CompactsIn W) :
    ∃ (K' : SKEFTHawking.SingularCompactsInOpen.CompactsIn W)
      (C' : Set (EuclideanSpace ℝ (Fin (m + 2)))),
      K ≤ K' ∧ Convex ℝ C' ∧ IsCompact C' ∧ C' ⊆ C ∧ p₀ ∈ C' ∧
      (∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C')
        ↔ (u : ↑M) ∈ (↑K'.1 : Set ↑M)) := by
  have hKU : (↑K.1 : Set ↑M) ⊆ U := K.2.trans hWU
  have hKUc : IsCompact (Subtype.val ⁻¹' (↑K.1 : Set ↑M) : Set ↥U) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      Set.inter_eq_self_of_subset_right hKU]
    exact K.1.isCompact'
  set KE : Set (EuclideanSpace ℝ (Fin (m + 2))) :=
    (fun x : ↥U => (e x : ↑(SingularEuclideanAcyclic.Eucl (m + 2))))
      '' (Subtype.val ⁻¹' (↑K.1 : Set ↑M)) with hKEdef
  have hKEc : IsCompact KE :=
    hKUc.image (continuous_subtype_val.comp e.continuous)
  have hKEC : KE ⊆ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hWe x).mp (K.2 hx)
  obtain ⟨C', hC'conv, hC'comp, hKEC', hC'C, hp₀C'⟩ :=
    exists_convex_compact_between hKEc hCconv hCopen hKEC hp₀
  set K'pre : Set ↥U := ⇑e ⁻¹' (Subtype.val ⁻¹' C') with hK'predef
  set K'set : Set ↑M := Subtype.val '' K'pre with hK'setdef
  have hK'pre_eq : K'pre = ⇑e.symm '' (Subtype.val ⁻¹' C' : Set ↥V) := by
    ext x
    constructor
    · intro hx; exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hK'predef]
      simp only [Set.mem_preimage, e.apply_symm_apply]
      exact hy
  have hC'V : C' ⊆ (V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) := hC'C.trans hCV
  have hK'c : IsCompact K'set := by
    refine IsCompact.image ?_ continuous_subtype_val
    rw [hK'pre_eq]
    refine IsCompact.image ?_ e.symm.continuous
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      Set.inter_eq_self_of_subset_right hC'V]
    exact hC'comp
  have hK'W : K'set ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hWe x).mpr (hC'C hx)
  have hKK' : (↑K.1 : Set ↑M) ⊆ K'set := by
    intro z hz
    exact ⟨⟨z, hKU hz⟩, hKEC' ⟨⟨z, hKU hz⟩, hz, rfl⟩, rfl⟩
  refine ⟨⟨⟨K'set, hK'c⟩, hK'W⟩, C', hKK', hC'conv, hC'comp, hC'C, hp₀C', ?_⟩
  intro u
  constructor
  · intro h; exact ⟨u, h, rfl⟩
  · rintro ⟨x, hx, hxu⟩
    rwa [Subtype.val_injective hxu] at hx

end SKEFTHawking.SingularCSCConvexChart
