/-
# Phase 5q.H close-out — THE SEAM RESIDUAL NARROWING: hasClass's last atoms.

Building on the #194 seam-split engine (`PinPlusTraceCapstoneSeamSplit`,
`PinPlusTraceDiskSeamSplit`), this module narrows the last residuals of the capstone `hasClass`.

* **§1 (item a) — the `W`-refined cover split.** `exists_iterate_cover_split_amb_inf` strengthens
  `SingularConnSquareCloseNC.exists_iterate_cover_split_amb`: when the split chain `f` is ADDITIONALLY
  supported in a set `W`, the two cover-split pieces land in `U ∩ W` and `V ∩ W` (not just `U`/`V`).
  Proof reuses the per-simplex re-partition `repartition_subspaceChains` — the partition internals
  already carry the `W`-support. Then `exists_subtype_boundary_split_of_relCycle_inf` propagates this
  to the disk's direct dependency: the free remainder of `∂(Sdᵘ c)` lands in `V ∩ W` (`W` = the
  boundary-support set), the attached part a pushforward from `↥(U ∩ W)`.

* **§2 (item b) — the exact free-sphere support.** `diskDetectChain_subtype_boundary_split_inf`
  instantiates §1 at `diskDetectChain` over the boundary sphere `W = {‖v‖ = 1}`, so the free part
  lands in `V ∩ sphere` exactly. `diskDetectChain_subtype_boundary_split_freeSphere` takes the cover
  choice `V = Sᶜ` (open, `S` closed): then `V ∩ sphere = sphere ∖ S` on the nose (set-level, no closure
  fuzz), discharging the free-sphere side `hvOut` of `CapstoneSeamTransferSeam` EXACTLY.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project
axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceDiskSeamSplit

namespace SKEFTHawking.PinPlusTraceSeamResidualNarrow

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularConnSquareCloseNC
open SKEFTHawking.PinPlusTraceCapstoneSeamSplit
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.DiskChartGeneric (D5)

noncomputable section

/-! ## §1. The `W`-refined cover split (item a) — the partition internals carry the `W`-support. -/

variable {X : TopCat} [T2Space ↑X]

/-- **The `W`-refined cover-fine split (item a).** Strengthens
`SingularConnSquareCloseNC.exists_iterate_cover_split_amb`: for a chain `f` supported in both the
union `U ∪ V` of a two-set open cover AND in a set `W`, the cover-fine split
`Sdᵘ f = fA + fB` has its pieces refined to `fA ∈ subspaceChains (U ∩ W)`, `fB ∈ subspaceChains (V ∩ W)`.
The proof reuses the base split, then the per-simplex re-partition `repartition_subspaceChains` (each
cover-fine support simplex of `Sdᵘ f`, being `W`-supported, lands in `U ∩ W` or `V ∩ W`). This is the
"partition internals already carry the `W`-support" strengthening the exact-support residual needs. -/
theorem exists_iterate_cover_split_amb_inf {U V W : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    {n : ℕ} (f : SingularChain X n) (hfUV : f ∈ subspaceChains (U ∪ V) n)
    (hfW : f ∈ subspaceChains W n) :
    ∃ (μ : ℕ) (fA fB : SingularChain X n),
      fA ∈ subspaceChains (U ∩ W) n ∧ fB ∈ subspaceChains (V ∩ W) n
      ∧ (⇑(singularSd X n))^[μ] f = fA + fB := by
  obtain ⟨μ, fA, fB, hfA, hfB, hsplit⟩ := exists_iterate_cover_split_amb hU hV f hfUV
  obtain ⟨cA, hcA⟩ := hfA
  obtain ⟨cB, hcB⟩ := hfB
  have hSdW : (⇑(singularSd X n))^[μ] f ∈ subspaceChains W n :=
    SingularExcision.singularSd_iterate_mem_subspaceChains hfW μ
  have hsum : chainIncl U n cA + chainIncl V n cB ∈ subspaceChains W n := by
    rw [hcA, hcB, ← hsplit]; exact hSdW
  obtain ⟨a, b, hab⟩ := repartition_subspaceChains cA cB hsum
  refine ⟨μ, chainIncl (U ∩ W) n a, chainIncl (V ∩ W) n b, ⟨a, rfl⟩, ⟨b, rfl⟩, ?_⟩
  rw [hsplit, ← hcA, ← hcB]; exact hab

/-- **The disk-side split producer, `W`-refined (item a, propagated).** As
`exists_subtype_boundary_split_of_relCycle` (#194) but the free remainder is refined to
`vOut ∈ subspaceChains (V ∩ W)` and the attached part a pushforward from `↥(U ∩ W)`. Because
`∂(Sdᵘ c) = Sdᵘ(∂c)` (chain map) and `∂c` is `W`-supported, `exists_iterate_cover_split_amb_inf`
carves the boundary split so the free part is supported in `V ∩ W` (`W` = the boundary-support set)
on the nose. The exact-support form the free-sphere residual consumes. -/
theorem exists_subtype_boundary_split_of_relCycle_inf {U V W : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V) (hWUV : W ⊆ U ∪ V) {m : ℕ} (c : SingularChain X (m + 2))
    (hbd : chainBoundary X (m + 1) c ∈ subspaceChains W (m + 1)) :
    ∃ (μ : ℕ) (cU : SingularChain (sub (U ∩ W)) (m + 1)) (vOut : SingularChain X (m + 1)),
      vOut ∈ subspaceChains (V ∩ W) (m + 1)
      ∧ chainBoundary X (m + 1) ((⇑(singularSd X (m + 2)))^[μ] c)
          = mapChain (ambIncl (U ∩ W)) (m + 1) cU + vOut
      ∧ chainBoundary X (m + 1) ((⇑(singularSd X (m + 2)))^[μ] c) ∈ subspaceChains W (m + 1) := by
  have hfUV : chainBoundary X (m + 1) c ∈ subspaceChains (U ∪ V) (m + 1) :=
    subspaceChains_mono hWUV (m + 1) hbd
  obtain ⟨μ, fA, fB, hfA, hfB, hsplit⟩ :=
    exists_iterate_cover_split_amb_inf hU hV (chainBoundary X (m + 1) c) hfUV hbd
  obtain ⟨cU, hcU⟩ :=
    (mem_subspaceChains_iff_exists_mapChain_ambIncl (U ∩ W) (m + 1) fA).mp hfA
  refine ⟨μ, cU, fB, hfB, ?_, chainBoundary_singularSd_iterate_mem m c hbd μ⟩
  rw [singularSd_iterate_chainBoundary, hsplit, hcU]

/-! ## §2. The exact free-sphere support (item b) — `hvOut` discharged on the nose. -/

/-- **The disk-side seam split of `diskDetectChain`, free part refined to `V ∩ sphere` (item b).**
As `PinPlusTraceDiskSeamSplit.diskDetectChain_subtype_boundary_split` but with the free remainder
supported in `V ∩ {‖v‖ = 1}` exactly (via §1 at `W = ` the boundary sphere), and the attached part a
pushforward from `↥(U ∩ sphere)`. Detection is inherited unchanged. -/
theorem diskDetectChain_subtype_boundary_split_inf {U V : Set D5} (hU : IsOpen U) (hV : IsOpen V)
    (hcover : {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} ⊆ U ∪ V) :
    ∃ (μ : ℕ)
        (cU : SingularChain (sub (X := TopCat.of D5)
          (U ∩ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1})) (3 + 1))
        (vOut : SingularChain (TopCat.of D5) (3 + 1)),
      vOut ∈ subspaceChains (X := TopCat.of D5)
          (V ∩ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}) (3 + 1)
      ∧ chainBoundary (TopCat.of D5) (3 + 1)
            ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
          = mapChain (ambIncl (X := TopCat.of D5)
              (U ∩ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1})) (3 + 1) cU + vOut
      ∧ chainBoundary (TopCat.of D5) (3 + 1)
            ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
          ∈ subspaceChains {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1)
      ∧ ∀ (y : D5) (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}),
          relClassOf (X := TopCat.of D5) ({y}ᶜ) 3
              ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
              (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1)
                (chainBoundary_singularSd_iterate_mem 3 diskDetectChain diskDetectChain_hc μ)) ≠ 0 := by
  obtain ⟨μ, cU, vOut, hvOut, hsplit, hmem⟩ :=
    exists_subtype_boundary_split_of_relCycle_inf (X := TopCat.of D5) hU hV hcover
      diskDetectChain diskDetectChain_hc
  refine ⟨μ, cU, vOut, hvOut, hsplit, hmem, fun y hy => ?_⟩
  rw [relClassOf_singularSd_iterate_eq 3 diskDetectChain diskDetectChain_hc μ y hy]
  exact diskDetectChain_hdet y hy

/-- **The exact free-sphere seam split (item b, discharged) — `hvOut` on the nose.** With the cover
choice `V = Sᶜ` (open, since `S` is closed), the free remainder lands in `sphere ∖ S` EXACTLY:
`Sᶜ ∩ {‖v‖ = 1} = {‖v‖ = 1} ∖ S` set-level, no closure fuzz. This is precisely the support demanded
by the `hvOut` field of `CapstoneSeamTransferSeam` — the free-sphere side discharged exactly. -/
theorem diskDetectChain_subtype_boundary_split_freeSphere {U : Set D5} (S : Set D5)
    (hS : IsClosed S) (hU : IsOpen U)
    (hcover : {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} ⊆ U ∪ Sᶜ) :
    ∃ (μ : ℕ)
        (cU : SingularChain (sub (X := TopCat.of D5)
          (U ∩ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1})) (3 + 1))
        (vOut : SingularChain (TopCat.of D5) (3 + 1)),
      vOut ∈ subspaceChains (X := TopCat.of D5)
          ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)
      ∧ chainBoundary (TopCat.of D5) (3 + 1)
            ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
          = mapChain (ambIncl (X := TopCat.of D5)
              (U ∩ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1})) (3 + 1) cU + vOut
      ∧ chainBoundary (TopCat.of D5) (3 + 1)
            ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
          ∈ subspaceChains {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} (3 + 1) := by
  obtain ⟨μ, cU, vOut, hvOut, hsplit, hmem, _⟩ :=
    diskDetectChain_subtype_boundary_split_inf hU hS.isOpen_compl hcover
  have hset : Sᶜ ∩ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}
      = {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S := by
    rw [Set.inter_comm, Set.diff_eq]
  exact ⟨μ, cU, vOut, hset ▸ hvOut, hsplit, hmem⟩

end

end SKEFTHawking.PinPlusTraceSeamResidualNarrow
