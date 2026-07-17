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
import SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply

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

/-- **The controlled rep's transported detection (item c helper).** The subdivided disk rep
`Sdᵘ diskDetectChain` detects the local generator at every disk-interior point, in the EXACT shape
`hasClass_ofTransfer`'s `hdetHa` argument demands with `cHa := Sdᵘ diskDetectChain` and
`hcHa := chainBoundary_singularSd_iterate_mem 3 diskDetectChain diskDetectChain_hc μ`. This is the
detection of `diskDetectChain` (`diskDetectChain_hdet`) transported across subdivision by
`relClassOf_singularSd_iterate_eq` (#194) — the free-standing supply of `hdetHa` for the controlled
rep. -/
theorem diskDetectChain_iterate_hdet (μ : ℕ) (y : D5)
    (hy : y ∉ {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}) :
    relClassOf (X := TopCat.of D5) ({y}ᶜ) 3
        ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (3 + 1)
          (chainBoundary_singularSd_iterate_mem 3 diskDetectChain diskDetectChain_hc μ)) ≠ 0 := by
  rw [relClassOf_singularSd_iterate_eq 3 diskDetectChain diskDetectChain_hc μ y hy]
  exact diskDetectChain_hdet y hy

/-! ## §3. The closed-S attached side (item d) — the collar bridge, honest-reduced.

The exact free-sphere remainder is discharged (item b). The complementary ATTACHED part of item b's
split is `mapChain (ambIncl (U ∩ sphere)) cU` — a pushforward from the OPEN nbhd `U ∩ sphere` of the
CLOSED attaching region `S`, not from `↥S` itself. The `hsplitHa`/`hvOut` fields of
`CapstoneSeamTransferSeam` demand the attached part be a pushforward from `↥S` (via `seamLegHa`,
defeq `ambIncl S` since `sub S = TopCat.of ↥S`). Bridging the open-nbhd attached part down to the
closed `S` is the **collar deformation-retraction** of the sphere-collar of `S` onto `S`, carrying
chain support to an EQUAL chain modulo a free-sphere correction.

This is NOT reachable by the open-cover subdivision engine: open covers cannot reach exact closed
supports directly (the #194 isolation — prose-level, NOT kernel-false; `{S, sphere ∖ S}` is not an
open cover, `S` being closed). The banked retraction machinery (`SingularConvexRadialRetract`,
`SingularPuncturedRetract`) delivers homology/homotopy equivalences — `relClassOf`-invariance — not
the chain-level EQUALITY `hsplitHa` needs; `SeamCollarChainDatum.ofCorrector` builds the straddle
`hdetAB`, not the boundary's `S`-exact decomposition. So the collar bridge WALLS, and is honest-reduced
to the named atom `ClosedSeamAttachedCollarBridge` below.

**Gate-pending, UNCONSUMED.** `ClosedSeamAttachedCollarBridge` is a completeness-adjacent Prop: it is
NOT proven here, and nothing unconditional is built from it — only the conditional wiring
`exact_seam_split_of_attachedBridge`, which takes it as a hypothesis. -/

/-- **The closed-seam attached-collar bridge (item d, the named atom — gate-pending, unconsumed).**
For the closed attaching region `S ⊆ D⁵` and an attached chain `a` (item b's attached part, supported
in an open nbhd `U ∩ sphere` of `S`), the bridge asserts `a` decomposes as a pushforward from `↥S`
plus a free-sphere correction: `a = mapChain (ambIncl S) cSeam + corr` with `corr` supported in
`sphere ∖ S`. This is exactly the collar deformation-retraction content — retract the open-nbhd
attached simplices onto `S`, the retraction homotopy's mismatch landing in the free sphere. Its
provision is the sole remaining geometric atom of the disk-side seam decomposition; it is NOT provable
by open-cover subdivision (the closed-`S` support barrier). Left UNCONSUMED: no proof, no unconditional
inhabitant. -/
def ClosedSeamAttachedCollarBridge (S : Set D5) (a : SingularChain (TopCat.of D5) (3 + 1)) : Prop :=
  ∃ (cSeam : SingularChain (sub (X := TopCat.of D5) S) (3 + 1))
      (corr : SingularChain (TopCat.of D5) (3 + 1)),
    a = mapChain (ambIncl (X := TopCat.of D5) S) (3 + 1) cSeam + corr
      ∧ corr ∈ subspaceChains (X := TopCat.of D5)
          ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)

/-- **The exact closed-S seam split, CONDITIONAL on the collar bridge (item d wiring).** Given item b's
open-nbhd split `w = a + vOut` (`vOut` free-sphere-supported) and the collar bridge on the attached
part `a`, the boundary `w` splits EXACTLY as a pushforward from `↥S` plus a free-sphere remainder:
`w = mapChain (ambIncl S) cSeam + vOut'` with `vOut' = corr + vOut ∈ subspaceChains (sphere ∖ S)`. This
is the exact `hsplitHa`/`hvOut` shape of `CapstoneSeamTransferSeam` (via `seamLegHa` defeq `ambIncl S`).
The whole disk-side seam decomposition thus reduces to the single atom `ClosedSeamAttachedCollarBridge`,
which is left unproven (gate-pending). Substantive char-2 rearrangement + submodule closure; consumes
the bridge only as a hypothesis. -/
theorem exact_seam_split_of_attachedBridge {S : Set D5}
    {w a vOut : SingularChain (TopCat.of D5) (3 + 1)}
    (hsplit : w = a + vOut)
    (hvOut : vOut ∈ subspaceChains (X := TopCat.of D5)
        ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1))
    (hbridge : ClosedSeamAttachedCollarBridge S a) :
    ∃ (cSeam : SingularChain (sub (X := TopCat.of D5) S) (3 + 1))
        (vOut' : SingularChain (TopCat.of D5) (3 + 1)),
      w = mapChain (ambIncl (X := TopCat.of D5) S) (3 + 1) cSeam + vOut'
        ∧ vOut' ∈ subspaceChains (X := TopCat.of D5)
            ({v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1) := by
  obtain ⟨cSeam, corr, ha, hcorr⟩ := hbridge
  refine ⟨cSeam, corr + vOut, ?_, Submodule.add_mem _ hcorr hvOut⟩
  rw [hsplit, ha, add_assoc]

end

/-! ## §4. The controlled-rep Supply wiring (item c) — `hasClass_ofTransfer` consumes `Sdᵘ`. -/

section CtrlSupply

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlue
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The controlled-rep narrowed capstone residual (item c).** The variant of
`CapstoneSeamTransferResidual` whose seam-transfer core and straddle detection ride on the CONTROLLED
representative `Sdᵘ diskDetectChain` (`μ` the subdivision count), not the unsubdivided `diskDetectChain`.
This is the shape the exact seam split (`diskDetectChain_subtype_boundary_split_inf`, item b) actually
lands on: the free-sphere remainder splits off `∂(Sdᵘ diskDetectChain)`, so the residual's `seam` field
is over `Sdᵘ diskDetectChain`. The row consumers see an equivalent supply (the seam core + straddle
detection over the controlled rep), NOT a restructured row — a pure variant constructor. -/
structure CapstoneSeamTransferResidualCtrl (μ : ℕ) where
  /-- a fundamental cycle of the closed source 4-manifold `M`. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents the fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- the `htransfer`-free seam-transfer core over the CONTROLLED rep `Sdᵘ diskDetectChain`. -/
  seam : CapstoneSeamTransferSeam s S hS φ hφ hφinj z
      ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
  /-- the overlap-zone straddle detection, over the controlled rep. -/
  hdetAB : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
      (hx : x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)),
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
      (closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isEmbedding
          (3 + 2) (capstoneCylChainT s S hS φ hφ hφinj z)
        + closedEmbeddingChain
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isEmbedding
          (3 + 2) ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain))
      (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (3 + 1)
        (hbd_ofTransfer s t S hS φ hφ hφinj cd hseam d
          (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj seam))) ≠ 0

/-- **The controlled-rep residual supplies the capstone `hasClass` field (item c).** Fires
`hasClass_ofTransfer` with `cHa := Sdᵘ diskDetectChain`, its transported boundary-support
(`chainBoundary_singularSd_iterate_mem`) and detection (`diskDetectChain_iterate_hdet`), the transfer
datum `seam.toTransfer` (its `htransfer` discharged in the Supply module), and the straddle detection.
Same output type as `CapstoneSeamTransferResidual.toHasClass`, so the two residual variants are
interchangeable suppliers of the capstone `hasClass` — the controlled-rep one matching the exact seam
split's landing chain. -/
def CapstoneSeamTransferResidualCtrl.toHasClass {μ : ℕ}
    (R : CapstoneSeamTransferResidualCtrl s t S hS φ hφ hφinj cd hseam d μ) :
    letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace) :=
  hasClass_ofTransfer s t S hS φ hφ hφinj cd hseam d R.z R.hz
    ((⇑(singularSd (TopCat.of D5) (3 + 2)))^[μ] diskDetectChain)
    (chainBoundary_singularSd_iterate_mem 3 diskDetectChain diskDetectChain_hc μ)
    (fun y hy => diskDetectChain_iterate_hdet μ y hy)
    (CapstoneSeamTransferSeam.toTransfer s S hS φ hφ hφinj R.seam)
    R.hdetAB

end

end CtrlSupply

end SKEFTHawking.PinPlusTraceSeamResidualNarrow
