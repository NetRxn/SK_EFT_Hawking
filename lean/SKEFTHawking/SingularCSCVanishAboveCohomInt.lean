/-
# Phase 5q.H (E1 CSC-PD tower) — top-degree CSC cohomology vanishing `Hᵏ_c(W;ℤ)=0`, `k>m+2` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCVanishAboveGeom.cscOpen_eq_zero_of_isOpen`. Per compact stage,
`vanishAbove_cofinalInt` produces a good-compact `K'` with `H_i(M|K';ℤ)=0` for `i>m+2` (HOMOLOGY). The
cohomology bridge is the integral relative UCT with a **case split on the boundary degree** `k=m+3`:
* `k>m+3` — both `H_k` and `H_{k-1}` vanish (both `>m+2`) ⟹ `relCohomology_eq_zero_of_relHomology_two_
  vanishInt` (Hom-term + Ext-term both die); needs only `hproj`.
* `k=m+3` (the pdWindow `hvan` degree) — `H_{m+3}=0` (Hom-term) but `H_{m+2}` is the top and generally
  nonzero, so the Ext-term needs `H_{m+2}` FREE ⟹ `relKroneckerHInt_injective_of_free`; needs the boundary
  Ext-freeness `[Free H_{m+2}(M|K')]`.

`hproj` (Kaplansky) and `hfree` (top-degree relative-homology freeness of a good-compact — a `fg`+
torsion-free⟹free build, the shared boundary crux with the `k=1` bottom) are threaded as hypotheses — NO
project axiom. The top-degree CSC vanishing feeds `pdWindowPInt_union_charted`'s `csc⁵`-vanishing args.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCVanishAboveGeomInt
import SKEFTHawking.SingularRelativeUCVanishInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularGoodCompactInt (vanishAboveInt)
open SKEFTHawking.SingularCSCVanishAboveInt (cscOpen_eq_zero_of_cofinal_vanishInt)
open SKEFTHawking.SingularCSCVanishAboveGeomInt (vanishAbove_cofinalInt)
open SKEFTHawking.SingularTopHomologyFreeUnionInt (HballFreeInt)
open SKEFTHawking.SingularRelativeUCVanishInt (relCohomology_eq_zero_of_relHomology_two_vanishInt)

namespace SKEFTHawking.SingularCSCVanishAboveCohomInt

/-- **Top-degree vanishing of `Hᵏ_c(W;ℤ)` for an open `W` in a charted `(m+2)`-manifold**, `k>m+2`
(integral). Threads `hproj` (relative-boundaries projectivity, = Kaplansky) and `hfree` (top-degree
relative-homology freeness of a compact set, the boundary Ext-freeness crux) as hypotheses. -/
theorem cscOpen_eq_zero_of_isOpenInt {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (hproj : ∀ (S : Set ↑(TopCat.of M)) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    (hballFree : HballFreeInt m M)
    {W : Set M} (hW : IsOpen W) {k : ℕ} (hk : m + 2 < k)
    (α : CompactlySupportedCohomologyOpenInt (M := TopCat.of M) W k) : α = 0 := by
  refine cscOpen_eq_zero_of_cofinal_vanishInt (fun K => ?_) α
  obtain ⟨K', hKK', hvanish, hfreeK'⟩ := vanishAbove_cofinalInt (m := m) (M := M) hballFree hW K
  refine ⟨K', hKK', fun x => ?_⟩
  rcases Nat.lt_or_ge k (m + 3 + 1) with hk2 | hk2
  · -- Boundary degree `k = m+3`: Ext-term needs `[Free H_{m+2}(M|K')]` — from the cofinal freeness.
    obtain rfl : k = m + 3 := by omega
    haveI := hfreeK'
    haveI := hproj ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (m + 1)
    exact SingularRelativeUCInt.relKroneckerHInt_injective_of_free
      ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) x
      (fun β => by rw [hvanish (m + 3) (by omega) β, map_zero])
  · -- Above the boundary `k > m+3`: both `H_k` and `H_{k-1}` vanish.
    obtain ⟨M', rfl⟩ : ∃ M', k = M' + 2 := ⟨k - 2, by omega⟩
    haveI := hproj ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) M'
    exact relCohomology_eq_zero_of_relHomology_two_vanishInt ((↑K'.1 : Set ↑(TopCat.of M))ᶜ)
      (fun β => hvanish (M' + 1) (by omega) β) (fun β => hvanish (M' + 2) (by omega) β) x

end SKEFTHawking.SingularCSCVanishAboveCohomInt
