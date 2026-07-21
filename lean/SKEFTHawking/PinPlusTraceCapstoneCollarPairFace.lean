/-
# Phase 5q.H (#212) — `houtPair` AT THE COARSE (CLOSED-COMPLEMENT) GRANULARITY

`PinPlusTraceCapstoneCollarPairCore` cut the collar-pair row to five geometric obligations
(`hctrlC`, `hctrlH`, `houtPair`, `hcoreHit`, `hq0det`) and factored `houtPair` into "a collar-annulus
refinement + three `∂W`-supports", then fenced the *open-complement* instantiation of that
refinement as settled-dead (§6 of that module: `collarAnnulusOpen_toSeamTransferSeam` builds the
refuted `CapstoneSeamTransferSeam`). Its scope note left the **strictly coarser closed-complement**
granularity — the `#210` shrunk-core picture `topface ∖ φ '' K` — open, and named it the live route.

This module takes that route to the bottom. Three things happen.

* **§1 — the granularity question is settled, and it is not a choice.**
  `closedEmbeddingChain_mem_iff_preimage` is an `↔`: a pushed chain lies in `C(A)` **iff** the
  chain itself lies in `C(j ⁻¹' A)`. So for the piecewise discharge of `houtPair` there is exactly
  ONE maximal support granularity, `fromCyl ⁻¹' ∂W` / `fromHandle ⁻¹' ∂W`, and every candidate
  support set is squeezed into the band
  `topface ∖ range φ` (the fenced, dead end) `⊆ topface ∖ φ '' K` `⊆ fromCyl ⁻¹' ∂W` (maximal).
  `houtPair_of_preimageSupport` discharges `houtPair` from the three maximal-granularity supports
  with `ann := 0` — no annulus chain is needed at all.

* **§2–§3 — `houtPair` collapses to ONE set-level containment.** The row already carries its
  remainders at the shrunk-core granularity (`houtC`, `houtH`), and the bottom face is the source
  end. Of the three faces the surgered-end datum covers two outright (`d.topFaceCovered`,
  `d.sphereFaceCovered`) and `ktSourceEnd` covers the third. What is left over is *exactly* the
  seam annulus between the shrunk core `K` and the edge of the attaching region: the single
  hypothesis
  `hseamAnn : ∀ a : ↥S, a ∉ K → fromHandle (a : D5) ∈ ∂W`.
  `houtPair_of_seamAnnulusCovered` / `CollarPairGeomFace.toCollarPairGeomCore` turn it into the
  five-obligation row's `houtPair` + `bdOut`. Because `fromCyl ∘ φ = fromHandle ∘ (↑·)` (the glue),
  the cylinder-side and handle-side annulus residuals are literally the SAME points of the trace
  carrier — hence one hypothesis, not two.

* **§4 — WHAT `eM'` ACTUALLY COVERS (the geometric crux).** `∂W = range ktSourceEnd ∪ range eM'`
  (`capstone_boundary_eq`), and on the seam the source end is *excluded*: with the attaching map
  landing in the top face (`hφtop`), `seamPoint_notMem_range_ktSourceEnd` shows
  `fromHandle (a : D5) ∉ range ktSourceEnd`. Hence `seamPoint_mem_bd_iff` — on the seam,
  `∈ ∂W` **iff** `∈ range eM'` — and `seamAnnulusCovered_iff_eM'`: the residual `hseamAnn` is
  *equivalent* to "the surgered end swallows the seam annulus". `topFace_inter_fromCyl_preimage_bd`
  computes the whole top-face part of the maximal granularity:
  `topface ∩ fromCyl ⁻¹' ∂W = (topface ∖ range φ) ∪ φ '' {a | fromHandle ↑a ∈ range eM'}`.
  So the answer to "what of the collar does `eM'` cover?" is, in tree, **exactly the two open
  complements and nothing of the seam**: every point of `range φ` that `∂W` contains is contained
  *because* `eM'` was chosen to contain it, and `SurgeredEndDatum` says nothing about those points.
  That containment is the sharply-named residual of `houtPair`, and it is a statement about the
  datum, not about chains.

## Fences

The fence `collar-pair-open-complement-annulus-is-refuted-shape` bans the OPEN-complement
instantiation (`outCbd ∈ C(topface ∖ range φ)`, `outHbd ∈ C(sphere ∖ S)`). Nothing here uses it:
every support in this module is at the strictly coarser shrunk-core / preimage granularity, and
`hseamAnn` at `K = univ` is vacuous (recovering exactly the fenced open-complement supports and
nothing more), which is the same boundary the `hcoreHit` fence
`collar-pair-maximal-core-reenters-refuted-support` marks. The live band is `K ⊊ S`.
Nothing here routes through `CapstoneSeamTransfer` / `hbd_ofTransfer`.

⚠ **`CollarPairGeomFace` is a SUFFICIENT producer, NOT an equivalent row** — see its docstring.
`hseamAnn` is not recoverable from `CollarPairGeomCore.houtPair`, so the honest count is still FIVE
obligations; what changed is that the deepest one is now a single **set-level** containment about
the surgered end rather than a chain equation with an existential witness.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCollarPairCore

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceDiskCorePair
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCoverGlueDisk
open SKEFTHawking.PinPlusTraceCapstoneCollarPair
open SKEFTHawking.PinPlusTraceCapstoneCollarPairGeom
open SKEFTHawking.PinPlusTraceCapstoneCollarPairCore

namespace SKEFTHawking.PinPlusTraceCapstoneCollarPairFace

/-! ## §0. The support granularity is forced: an `↔`, not a choice -/

/-- **THE MAXIMAL GRANULARITY, AS AN `↔`.** A chain pushed along a topological embedding `j` is
supported in `A` **iff** the chain itself is supported in `j ⁻¹' A`. Forward is the support-pullback
`mem_subspaceChains_of_mapChain_mem` (injectivity of `j`); backward is
`closedEmbeddingChain_mem_of_mem` plus `image_preimage_subset`.

Consequence for the collar-pair row: any *piecewise* discharge of `houtPair` — i.e. any route that
puts each of the three weld residuals into `C(∂W)` separately — must place that residual's support
inside `j ⁻¹' ∂W`, and may place it anywhere inside. So `fromCyl ⁻¹' ∂W` / `fromHandle ⁻¹' ∂W` are
not a convenient choice of granularity, they are *the* granularity; the fenced open complements are
its minimal end and the shrunk-core sets sit strictly between. -/
theorem closedEmbeddingChain_mem_iff_preimage {P : Type} [TopologicalSpace P] {Wc : Type}
    [TopologicalSpace Wc] {j : P → Wc} (hj : Topology.IsEmbedding j) {A : Set Wc} (n : ℕ)
    (c : SingularChain (TopCat.of P) n) :
    closedEmbeddingChain hj n c ∈ subspaceChains (X := TopCat.of Wc) A n
      ↔ c ∈ subspaceChains (X := TopCat.of P) (j ⁻¹' A) n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : mapChain (X := TopCat.of P) (Y := TopCat.of Wc) ⟨j, hj.continuous⟩ n c
        ∈ subspaceChains (X := TopCat.of Wc) A n := by
      rwa [← PinPlusTraceSeamTransferNoGo.closedEmbeddingChain_eq_mapChain hj n c]
    exact PinPlusTraceSeamTransferNoGo.mem_subspaceChains_of_mapChain_mem
      (X := TopCat.of P) (Y := TopCat.of Wc) ⟨j, hj.continuous⟩ hj.injective h'
  · exact subspaceChains_mono (X := TopCat.of Wc) (Set.image_preimage_subset j A) n
      (closedEmbeddingChain_mem_of_mem hj (Bd := j ⁻¹' A) n c h)

section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

variable {s t S hS φ hφ hφinj cd hseam d}

/-! ## §1. What `∂W` contains for free: the two open complements and the source end -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The bottom face is the source end.** `M × {⊥}`, pushed by `fromCyl`, is `range ktSourceEnd`,
the first half of `capstone_boundary_eq`. Free — no datum field needed. -/
theorem bottomFace_subset_fromCyl_preimage_bd :
    (Set.univ ×ˢ ({⊥} : Set (Set.Icc (0 : ℝ) 1)))
      ⊆ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) := by
  intro y hy
  have hbot : y.2 = ⊥ := hy.2
  have hyeq : cylBot s.M y.1 = y := Prod.ext rfl (by rw [hbot]; rfl)
  show (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl y
      ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
  rw [capstone_boundary_eq]
  exact Set.mem_union_left _ ⟨y.1, by rw [ktSourceEnd, hyeq]⟩

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The un-attached top face is covered by the surgered end** — `d.topFaceCovered` restated at the
maximal granularity. This is the set the open-complement fence bans as a *support*; here it appears
only as a sub-piece of the coarse set. -/
theorem topFaceOpen_subset_fromCyl_preimage_bd :
    ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ)
      ⊆ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) := by
  intro y hy
  show (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl y
      ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
  rw [capstone_boundary_eq]
  exact Set.mem_union_right _ (d.topFaceCovered (Set.mem_image_of_mem _ hy))

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The free boundary sphere is covered by the surgered end** — `d.sphereFaceCovered` restated at
the maximal granularity. -/
theorem sphereOpen_subset_fromHandle_preimage_bd :
    ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S)
      ⊆ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) := by
  intro q hq
  show (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle q
      ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
  rw [capstone_boundary_eq]
  exact Set.mem_union_right _ (d.sphereFaceCovered (Set.mem_image_of_mem _ hq))

/-! ## §2. The seam-annulus residual, and the coarse faces it buys -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE COARSE TOP FACE, from the seam-annulus residual.** The `#210` shrunk-core top face
`topface ∖ φ '' K` splits into the un-attached part (free from `d.topFaceCovered`) and the seam
annulus `φ '' Kᶜ` (the residual `hseamAnn`, transported across the glue
`fromCyl ∘ φ = fromHandle ∘ (↑·)`). -/
theorem topFaceShrunk_subset_fromCyl_preimage_bd {K : Set ↥S}
    (hseamAnn : ∀ a : ↥S, a ∉ K →
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
        ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) :
    ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ φ '' K)
      ⊆ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) := by
  rintro y ⟨hytop, hyK⟩
  by_cases hyφ : y ∈ Set.range φ
  · obtain ⟨a, rfl⟩ := hyφ
    have haK : a ∉ K := fun h => hyK (Set.mem_image_of_mem _ h)
    have hglue : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl (φ a)
        = (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5) :=
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a
    show (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl (φ a)
        ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
    rw [hglue]
    exact hseamAnn a haK
  · exact topFaceOpen_subset_fromCyl_preimage_bd (d := d) ⟨hytop, hyφ⟩

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE COARSE BOUNDARY SPHERE, from the same residual.** The handle-side mirror: the shrunk-core
sphere `S⁴ ∖ (↑·) '' K` splits into the free part (free from `d.sphereFaceCovered`) and the seam
annulus, which is the SAME set of trace-carrier points as the cylinder-side annulus. -/
theorem sphereShrunk_subset_fromHandle_preimage_bd {K : Set ↥S}
    (hseamAnn : ∀ a : ↥S, a ∉ K →
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
        ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) :
    ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ Subtype.val '' K)
      ⊆ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) := by
  rintro q ⟨hqs, hqK⟩
  by_cases hqS : q ∈ S
  · have haK : (⟨q, hqS⟩ : ↥S) ∉ K := fun h => hqK (Set.mem_image_of_mem _ h)
    exact hseamAnn ⟨q, hqS⟩ haK
  · exact sphereOpen_subset_fromHandle_preimage_bd (d := d) ⟨hqs, hqS⟩

/-! ## §3. `houtPair`, discharged at the maximal granularity -/

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`houtPair` FROM THE THREE MAXIMAL-GRANULARITY SUPPORTS.** With every residual supported in the
preimage of `∂W`, the weld holds — with the TRIVIAL annulus `ann := 0`, so no collar-annulus chain
enters at all. By `closedEmbeddingChain_mem_iff_preimage` each hypothesis is *equivalent* to the
corresponding pushed residual lying in `C(∂W)`, which is what `houtPair_of_bdMem` asks for; so this
is the weakest possible per-piece hypothesis set. -/
theorem houtPair_of_preimageSupport (z : cycles (TopCat.of s.M) (2 + 2)) (μ : ℕ)
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (hC : outC ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1))
    (hH : outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle ⁻¹'
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1))
    (hBot : ctrlBottom s S hS φ hφ hφinj z μ
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        ((ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1)) :
    ∃ bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1),
      weldSum z μ outC outH
        = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
            (3 + 1) bdOut :=
  houtPair_of_bdMem (d := d) z μ 0 outC outH (by rw [map_zero, zero_add]) (by rw [map_zero, zero_add])
    ((closedEmbeddingChain_mem_iff_preimage _ _ _).mpr hC)
    ((closedEmbeddingChain_mem_iff_preimage _ _ _).mpr hH)
    ((closedEmbeddingChain_mem_iff_preimage _ _ _).mpr hBot)

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The bottom face of a fundamental cycle is supported in `M × {⊥}` — the slice `z@⊥` maps every
point into the bottom endpoint slice. -/
theorem ctrlBottom_zero_mem_bottomFace (z : cycles (TopCat.of s.M) (2 + 2)) :
    ctrlBottom s S hS φ hφ hφinj z 0
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        (Set.univ ×ˢ ({⊥} : Set (Set.Icc (0 : ℝ) 1))) (3 + 1) := by
  rw [ctrlBottom_zero]
  exact mapChain_mem_subspaceChains (slice (graphHom (TopCat.of s.M)) 0)
    (fun x _ => by rw [slice_graphHom]; exact ⟨Set.mem_univ x, rfl⟩) (3 + 1) _
    (mem_subspaceChains_univ _ _)

omit [PreconnectedSpace s.M] [Nonempty s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **`houtPair` FROM ONE SET-LEVEL CONTAINMENT.** Given the row's own shrunk-core remainder
supports (`houtC`, `houtH`) and the seam-annulus residual `hseamAnn`, the weld holds. Every other
input is free: the two open complements come from `d.topFaceCovered` / `d.sphereFaceCovered` and the
bottom face is the source end. So at `μ = 0` the whole of `houtPair` — a chain equation with an
existential `∂W`-subtype witness — reduces to the single containment `hseamAnn`. -/
theorem houtPair_of_seamAnnulusCovered (z : cycles (TopCat.of s.M) (2 + 2)) {K : Set ↥S}
    {outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)}
    {outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)}
    (houtC : outC ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ φ '' K) (3 + 1))
    (houtH : outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ Subtype.val '' K) (3 + 1))
    (hseamAnn : ∀ a : ↥S, a ∉ K →
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
        ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) :
    ∃ bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1),
      weldSum z 0 outC outH
        = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
            (3 + 1) bdOut :=
  houtPair_of_preimageSupport (d := d) z 0
    (subspaceChains_mono (topFaceShrunk_subset_fromCyl_preimage_bd (d := d) hseamAnn) (3 + 1) houtC)
    (subspaceChains_mono (sphereShrunk_subset_fromHandle_preimage_bd (d := d) hseamAnn) (3 + 1)
      houtH)
    (subspaceChains_mono (bottomFace_subset_fromCyl_preimage_bd (d := d)) (3 + 1)
      (ctrlBottom_zero_mem_bottomFace z))

/-! ## §4. WHAT `eM'` ACTUALLY COVERS — the seam is `eM'`-only -/

omit [T2Space s.M] [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- The in-tree top-face fact `hφtop` (stated in `ℝ`-coordinates by `SingularSurgeryBoundaryFloor`)
in the `Set.Icc`-lattice form the top-face SET uses. -/
theorem phi_snd_eq_top (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) (a : ↥S) : (φ a).2 = ⊤ :=
  Subtype.ext (hφtop a)

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The source end never meets the seam.** With the attaching map landing in the TOP face
(`hφtop`), a seam point `fromHandle (a : D5) = fromCyl (φ a)` lies in the handle end, and the source
end (the BOTTOM face) is disjoint from the whole handle end — the in-tree
`ktSourceEnd_disjoint_range_fromHandle`, which is exactly the separation this needs. -/
theorem seamPoint_notMem_range_ktSourceEnd (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) (a : ↥S) :
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
      ∉ Set.range (ktSourceEnd s.M D5 S hS φ hφ hφinj) := fun h =>
  Set.disjoint_left.mp
    (ktSourceEnd_disjoint_range_fromHandle s.M D5 S hS φ hφ hφinj hφtop) h ⟨(a : D5), rfl⟩

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **ON THE SEAM, `∂W` IS EXACTLY `range eM'`.** `∂W = range ktSourceEnd ∪ range eM'` and the first
half misses the seam entirely, so a seam point is a boundary point **iff** the surgered end was
chosen to contain it. An `↔`. -/
theorem seamPoint_mem_bd_iff (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) (a : ↥S) :
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
        ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W
      ↔ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5) ∈ Set.range d.eM' := by
  rw [capstone_boundary_eq]
  exact ⟨fun h => h.resolve_left (seamPoint_notMem_range_ktSourceEnd hφtop a),
    fun h => Set.mem_union_right _ h⟩

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE RESIDUAL, RESTATED AS A FACT ABOUT `eM'`.** The seam-annulus containment that `houtPair`
needs is *equivalent* to: the surgered end `M′` swallows the whole seam annulus between the shrunk
core `K` and the edge of the attaching region. `SurgeredEndDatum` carries no such field — its
`topFaceCovered` / `sphereFaceCovered` stop at the OPEN complements — so this is exactly the
geometry the coarse route still owes, stated on the datum rather than on chains. -/
theorem seamAnnulusCovered_iff_eM' (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) (K : Set ↥S) :
    (∀ a : ↥S, a ∉ K →
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
          ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      ↔ (∀ a : ↥S, a ∉ K →
        (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5) ∈ Set.range d.eM') :=
  forall_congr' fun a => forall_congr' fun _ => seamPoint_mem_bd_iff (d := d) hφtop a

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE TOP-FACE PART OF THE MAXIMAL GRANULARITY, COMPUTED.** Intersected with the top face, the
preimage `fromCyl ⁻¹' ∂W` is *exactly* the un-attached complement (which `d.topFaceCovered` gives
outright) together with the seam points the surgered end happens to contain — nothing else. This is
the precise answer to "what of the collar does `eM'` cover": in tree, the two open complements, plus
whatever of `range φ` the chosen `eM'` swallows, about which the datum is silent. -/
theorem topFace_inter_fromCyl_preimage_bd (hφtop : ∀ a : ↥S, ((φ a).2 : ℝ) = 1) :
    (Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1)))
        ∩ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl ⁻¹'
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      = ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ)
        ∪ φ '' {a : ↥S | (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
              ∈ Set.range d.eM'} := by
  ext y
  constructor
  · rintro ⟨hytop, hybd⟩
    by_cases hyφ : y ∈ Set.range φ
    · obtain ⟨a, rfl⟩ := hyφ
      refine Set.mem_union_right _ ⟨a, ?_, rfl⟩
      have : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
          ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W := by
        rw [← (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a]; exact hybd
      exact (seamPoint_mem_bd_iff (d := d) hφtop a).mp this
    · exact Set.mem_union_left _ ⟨hytop, hyφ⟩
  · rintro (⟨hytop, hyφ⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨hytop, topFaceOpen_subset_fromCyl_preimage_bd (d := d) ⟨hytop, hyφ⟩⟩
    · refine ⟨⟨Set.mem_univ _, phi_snd_eq_top hφtop a⟩, ?_⟩
      have hglue : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl (φ a)
          = (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5) :=
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).glue a
      show (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl (φ a)
          ∈ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      rw [hglue]
      exact (seamPoint_mem_bd_iff (d := d) hφtop a).mpr ha

/-! ## §5. The row, produced from the set-level residual -/

variable (s t S hS φ hφ hφinj cd hseam d)

/-- **A SUFFICIENT PRODUCER FOR THE FIVE-OBLIGATION ROW — NOT an equivalent row.**
`CollarPairGeomCore` with the two weld fields (`bdOut`, `houtPair`) replaced by the single
**set-level** field `hseamAnn`; every other field is verbatim its `CollarPairGeomCore` counterpart.

⚠ **Scope.** `CollarPairGeomFace → CollarPairGeomCore` is constructive
(`toCollarPairGeomCore`), but the converse is NOT available: `houtPair` is a statement about two
particular chains and does not recover a containment about *all* seam points off `K`. So this is a
**strengthening**, and the honest obligation count of the collar-pair row is still FIVE. What the
trade buys is qualitative: the deepest field is no longer a chain equation carrying an existential
`∂W`-subtype witness but one containment about the surgered end, equivalent (by
`seamAnnulusCovered_iff_eM'`) to "`range eM'` contains the seam annulus". -/
structure CollarPairGeomFace where
  /-- a fundamental cycle of the closed source 4-manifold `M`. -/
  z : cycles (TopCat.of s.M) (2 + 2)
  /-- `z` represents THE fundamental class. -/
  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
    = Homology.mk (TopCat.of s.M) (2 + 2) z
  /-- **the shrunk closed core** `K ⊂ int A` of the attaching region (#210 repair shape). -/
  K : Set ↥S
  /-- the core is chosen away from the boundary of the finished trace. -/
  hKoffBd : K ⊆ (seamPoint s S hS φ hφ hφinj ⁻¹'
    (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W))ᶜ
  /-- **the shared 4-dimensional seam core** on the attaching region. -/
  cCore : SingularChain (TopCat.of ↥S) (3 + 1)
  /-- the cylinder-side remainder (the un-attached top face, off `K`). -/
  outC : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B) (3 + 1)
  /-- the handle-side remainder (the free boundary sphere, off `K`). -/
  outH : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
  /-- **GEOMETRIC 1 — the top-face split** `z@⊤ = φ_# cCore + outC`. -/
  hctrlC : topSliceB s S hS φ hφ hφinj z
    = mapChain (seamLegB s S hS φ hφ hφinj) (3 + 1) cCore + outC
  /-- **GEOMETRIC 2 — the disk-side split** on the canonical detecting chain. -/
  hctrlH : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1)
      diskDetectChain
    = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cCore + outH
  /-- the cylinder remainder is supported in the top face off the shrunk core. -/
  houtC : outC ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ φ '' K) (3 + 1)
  /-- the handle remainder is supported in the boundary sphere off the shrunk core. -/
  houtH : outH ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
      ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ Subtype.val '' K) (3 + 1)
  /-- **GEOMETRIC 3′ — THE SEAM-ANNULUS RESIDUAL**, replacing `bdOut` + `houtPair`: every seam point
  off the shrunk core is a boundary point of the finished trace. Equivalently (`hφtop`,
  `seamAnnulusCovered_iff_eM'`): the surgered end `M′` swallows the seam annulus. -/
  hseamAnn : ∀ a : ↥S, a ∉ K →
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle (a : D5)
      ∈ ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W
  /-- **GEOMETRIC 4 — the anti-fake tether**. -/
  hcoreHit :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) →
    cCore ∉ subspaceChains (X := TopCat.of ↥S) (K ᶜ) (3 + 1)
  /-- **GEOMETRIC 5 — the seam straddle-detection atom**. -/
  hq0det : ∀ (x : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier),
      x ∉ (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl →
      x ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle →
      ∀ (hq : chainBoundary
          (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) (3 + 1)
          (qZero s S hS φ hφ hφinj z)
        ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            ({x}ᶜ) (3 + 1)),
    relClassOf (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier) ({x}ᶜ) 3
      (qZero s S hS φ hφ hφinj z) hq ≠ 0

namespace CollarPairGeomFace

variable {s t S hS φ hφ hφinj cd hseam d}
variable (F : CollarPairGeomFace s t S hS φ hφ hφinj cd hseam d)

omit [PreconnectedSpace s.M] in
/-- **THE WELD, PRODUCED.** `houtPair_of_seamAnnulusCovered` applied to the face row's own data. -/
theorem houtPair_exists :
    ∃ bdOut : SingularChain
      (sub (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) (3 + 1),
      weldSum F.z 0 F.outC F.outH
        = chainIncl (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
            (3 + 1) bdOut :=
  houtPair_of_seamAnnulusCovered (d := d) F.z F.houtC F.houtH F.hseamAnn

omit [PreconnectedSpace s.M] in
/-- **THE FACE ROW PRODUCES THE FIVE-OBLIGATION ROW.** The weld field and its `∂W`-subtype witness
are both constructed from `hseamAnn`; every other field transfers verbatim. -/
noncomputable def toCollarPairGeomCore :
    CollarPairGeomCore s t S hS φ hφ hφinj cd hseam d where
  z := F.z
  hz := F.hz
  K := F.K
  hKoffBd := F.hKoffBd
  cCore := F.cCore
  outC := F.outC
  outH := F.outH
  hctrlC := F.hctrlC
  hctrlH := F.hctrlH
  houtC := F.houtC
  houtH := F.houtH
  bdOut := (houtPair_exists F).choose
  houtPair := (houtPair_exists F).choose_spec
  hcoreHit := F.hcoreHit
  hq0det := F.hq0det

end CollarPairGeomFace

variable {s t S hS φ hφ hφinj cd hseam d}

omit [PreconnectedSpace s.M] in
/-- **THE PRODUCTION STATEMENT (one direction — see `CollarPairGeomFace`'s scope note).** Inhabiting
the face row inhabits the five-obligation row, hence (through `CollarPairGeomCore.toHasClass`) the
capstone's relative fundamental class. The converse is not claimed. -/
theorem nonempty_collarPairGeomCore_of_face
    (h : Nonempty (CollarPairGeomFace s t S hS φ hφ hφinj cd hseam d)) :
    Nonempty (CollarPairGeomCore s t S hS φ hφ hφinj cd hseam d) :=
  ⟨h.some.toCollarPairGeomCore⟩

end

end SKEFTHawking.PinPlusTraceCapstoneCollarPairFace
