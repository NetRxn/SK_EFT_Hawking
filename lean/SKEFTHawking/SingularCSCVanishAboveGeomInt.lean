/-
# Phase 5q.H (E1 CSC-PD tower) — W-relative geometric cofinality of `vanishAboveInt` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCVanishAboveGeom.vanishAbove_cofinal`: every compact `K ⊆ W`
(`W` open in a charted `(m+2)`-manifold) sits inside a compact `K' ⊆ W` that is a finite union of closed
chart-ball pieces and hence satisfies `vanishAboveInt (m+2) K'`. The construction (chart balls, finite
subcover, biUnion) is pure topology — reused verbatim from the mod-2 development (`exists_chartBall_subset_open`
is coefficient-agnostic); only the good-compact glue is the integral `goodCompactInt_biUnion` /
`goodCompactInt_compact_in_chart_source` / `goodCompactInt_empty`.

The top-degree HOMOLOGY-vanishing cofinality — the geometric prerequisite of the integral top-degree CSC
cohomology vanishing (`cscOpen_eq_zero_of_isOpenInt`, whose cohomology bridge additionally needs the
boundary-degree Ext-freeness `[Free H_{m+2}(M|K)]`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCVanishAboveInt
import SKEFTHawking.SingularCSCVanishAboveGeom
import SKEFTHawking.SingularGoodCompactManifoldInt
import SKEFTHawking.SingularGoodCompactUnionInt
import SKEFTHawking.SingularGoodCompactEuclideanInt
import SKEFTHawking.SingularTopHomologyFreeUnionInt

open SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularGoodCompactInt (vanishAboveInt goodCompactInt)
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularTopHomologyFreeUnionInt (HballFreeInt free_relHom_biUnion)
open SKEFTHawking.SingularCSCVanishAboveGeom (exists_chartBall_subset_open)

namespace SKEFTHawking.SingularCSCVanishAboveGeomInt

/-- **W-relative geometric cofinality of the `vanishAboveInt` stages** (integral): every compact `K ⊆ W`
(`W` open) is contained in a compact `K' ⊆ W` with `vanishAboveInt (m+2) ↑K'` — `K'` = a finite union of
closed chart-ball pieces inside `W` covering `K`. -/
theorem vanishAbove_cofinalInt {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (hballFree : HballFreeInt m M)
    {W : Set M} (hW : IsOpen W) (K : CompactsIn W) :
    ∃ K' : CompactsIn W, K ≤ K' ∧
      vanishAboveInt (X := TopCat.of M) (m + 2) (↑K'.1 : Set M) ∧
      Module.Free ℤ (RelHomologyInt (X := TopCat.of M) (↑K'.1 : Set M)ᶜ (m + 2)) := by
  classical
  rcases Set.eq_empty_or_nonempty (↑K.1 : Set M) with hKe | hKne
  · refine ⟨K, le_refl K, ?_, ?_⟩
    · rw [hKe]
      exact (SKEFTHawking.SingularGoodCompactEuclideanInt.goodCompactInt_empty
        (X := TopCat.of M) (m + 2)).1
    · rw [hKe]
      haveI : Subsingleton (RelHomologyInt (X := TopCat.of M) (∅ᶜ : Set ↑(TopCat.of M)) (m + 2)) :=
        ⟨fun a b => by
          rw [SKEFTHawking.SingularGoodCompactEuclideanInt.relHomologyInt_compl_empty_eq_zero _ a,
            SKEFTHawking.SingularGoodCompactEuclideanInt.relHomologyInt_compl_empty_eq_zero _ b]⟩
      exact Module.Free.of_subsingleton ℤ _
  · have hKW : (↑K.1 : Set M) ⊆ W := K.2
    set c : M → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m + 2))) :=
      fun x => chartAt (EuclideanSpace ℝ (Fin (m + 2))) x with hc
    have hball : ∀ i : (↑K.1 : Set M), ∃ r : ℝ, 0 < r ∧
        Metric.closedBall ((c i) i) r ⊆ (c i).target ∧
        (c i).symm '' Metric.closedBall ((c i) i) r ⊆ W :=
      fun i => exists_chartBall_subset_open hW (hKW i.2)
    choose r hrpos hrsub hrW using hball
    set B : (↑K.1 : Set M) → Set M :=
      fun i => (c i).symm '' Metric.closedBall ((c i) i) (r i) with hB
    set O : (↑K.1 : Set M) → Set M :=
      fun i => (c i).symm '' Metric.ball ((c i) i) (r i) with hO
    have hO_open : ∀ i, IsOpen (O i) := fun i =>
      (c i).isOpen_image_symm_of_subset_target Metric.isOpen_ball
        (Metric.ball_subset_closedBall.trans (hrsub i))
    have hO_mem : ∀ i : (↑K.1 : Set M), (i : M) ∈ O i := fun i =>
      ⟨(c i) i, Metric.mem_ball_self (hrpos i), (c i).left_inv (mem_chart_source _ _)⟩
    have hOB : ∀ i, O i ⊆ B i := fun i => Set.image_mono Metric.ball_subset_closedBall
    have hcover : (↑K.1 : Set M) ⊆ ⋃ i, O i := fun x hx =>
      Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hO_mem ⟨x, hx⟩⟩
    obtain ⟨t, ht⟩ := K.1.isCompact'.elim_finite_subcover O hO_open hcover
    have hB_compact : ∀ i, IsCompact (B i) := fun i =>
      (ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
        ((c i).continuousOn_symm.mono (hrsub i))
    have hB_source : ∀ i, B i ⊆ (c i).source := fun i => by
      rintro p ⟨z, hz, rfl⟩
      exact (c i).symm_mapsTo (hrsub i hz)
    have hKK' : (↑K.1 : Set M) ⊆ ⋃ i ∈ t, B i :=
      ht.trans (Set.iUnion₂_mono fun i _ => hOB i)
    have ht_ne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hKne
      obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (ht hx)
      exact ⟨i, hi⟩
    have hK'_compact : IsCompact (⋃ i ∈ t, B i) :=
      t.finite_toSet.isCompact_biUnion (fun i _ => hB_compact i)
    have hK'_W : (⋃ i ∈ t, B i) ⊆ W := Set.iUnion₂_subset (fun i _ => hrW i)
    -- Each nonempty sub-intersection of the chart-ball cover is closed and good-compact.
    have hgood : ∀ t' : Finset (↑K.1 : Set M), t' ⊆ t → t'.Nonempty →
        IsClosed (⋂ i ∈ t', B i) ∧ goodCompactInt (X := TopCat.of M) (m + 2) (⋂ i ∈ t', B i) := by
      intro t' _ht' ht'ne
      obtain ⟨j, hj⟩ := ht'ne
      have hsubBj : (⋂ i ∈ t', B i) ⊆ B j := Set.biInter_subset_of_mem hj
      have hclosed : IsClosed (⋂ i ∈ t', B i) :=
        isClosed_biInter (fun i _ => (hB_compact i).isClosed)
      have hcompInter : IsCompact (⋂ i ∈ t', B i) :=
        (hB_compact j).of_isClosed_subset hclosed hsubBj
      exact ⟨hclosed, SKEFTHawking.SingularGoodCompactManifoldInt.goodCompactInt_compact_in_chart_source
        hcompInter (hsubBj.trans (hB_source j))⟩
    -- Freeness of `H_{m+2}(M | ⋃ i∈t, B i)`: the biUnion of chart-balls, each free by `hballFree`.
    -- Stated on the plain union (not the `CompactsIn` coercion) so `free_relHom_biUnion` matches directly.
    have hfreeK' : Module.Free ℤ
        (RelHomologyInt (X := TopCat.of M) (⋃ i ∈ t, B i)ᶜ (m + 2)) := by
      refine free_relHom_biUnion (X := TopCat.of M) (n := m + 2) ht_ne B hgood (fun i _ => ?_)
      exact hballFree (i : M) (r i) (hrpos i).le (hrsub i)
    exact ⟨⟨⟨⋃ i ∈ t, B i, hK'_compact⟩, hK'_W⟩, hKK',
      (SKEFTHawking.SingularGoodCompactUnionInt.goodCompactInt_biUnion (X := TopCat.of M)
        ht_ne B hgood).1, hfreeK'⟩

end SKEFTHawking.SingularCSCVanishAboveGeomInt
