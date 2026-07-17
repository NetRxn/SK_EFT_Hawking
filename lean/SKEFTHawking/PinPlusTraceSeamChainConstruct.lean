/-
# Phase 5q.H close-out — THE GENUINE cSeam: the shared seam chain BY DATA (route c, honest reduction)

The consumption structure `CapstoneSeamTransferSeam` (#184, Supply) carries the SINGLE shared seam
chain `cSeam : SingularChain ↥S (3+1)` serving BOTH splits — the cylinder-side `z@⊤ = (φ-leg)_# cSeam
+ wOut` and the disk-side `∂cHa = (incl-leg)_# cSeam + vOut`. Gate round 13 (#202 §2) located the
disk-side collar Prop `ClosedSeamAttachedCollarBridge` as PURE SUPPORT (fakeable in isolation with
`cSeam := 0`), with the anti-laundering guard living in the SHARED-`cSeam` tie. This module addresses
the production of that genuine `cSeam`.

## Routing verdict (BLOCK #204) — routes (a) and (b) both WALL; deliver route (c)

* **Route (a) — chain-level construction from the disk chain's explicit S-face — WALLS.** The disk
  chain `diskDetectChain` (#166/#168) is `(exists_detecting_chain_of_hasRelFundClass …).choose`: an
  OPAQUE `.choose` artifact carrying NO explicit `S`-face subchain. There is no named face to pull
  back along `φ`. (Confirmed by direct inspection of `PinPlusTraceDiskCorePair.diskDetectChain`.)
* **Route (b) — the collar-retraction route — WALLS.** `SeamCollarDatum` (#136) supplies only a
  HOMEOMORPHISM `hHomeo : ↥seamNbhd ≃ₜ WeldedCollarModel A` — a topological equivalence delivering
  `relClassOf`-invariance, NOT the chain-level EQUALITY the split demands (exactly as
  `PinPlusTraceSeamResidualNarrow` §3 predicted: the banked retraction machinery gives
  homology/homotopy equivalence, and the open-cover subdivision engine cannot reach the CLOSED-`S`
  support barrier — `{S, sphere ∖ S}` is not an open cover, `S` being closed).
* **Route (c) — honest reduction — DELIVERED here.** The single shared-`cSeam` data-atom is exactly
  `CapstoneSeamTransferSeam` (already in tree); this module proves the CONNECTING lemmas that make its
  role precise and confirm the round-13 specs from the PRODUCING side:

  1. **§1 `capstoneSeamTransferSeam_disk_bridge`** — the disk side of any consumption inhabitant IS a
     genuine `ClosedSeamAttachedCollarBridge S (∂cHa)` instance (via `seamLegHa ≡ ambIncl S`,
     `.Ha ≡ D⁵`). The gate-located support Prop is precisely the disk half; the shared `cSeam` field
     is what ties it to the cylinder half, which the bare bridge lacks.
  2. **§2 `capstoneSeamTransferSeam_ofSharedSeam`** — the named shared-`cSeam` constructor: a single
     `cSeam` on `↥S` plus the two co-adapted splits assembles the structure (the `with cSeam in hand →
     consume` step; keeps the ONE shared field, spec-2 compliant). Its output feeds
     `CapstoneSeamTransferSeam.toTransfer` and hence the `seam` field of `CapstoneSeamTransferResidual`
     / `CapstoneSeamTransferResidualCtrl`, firing `hasClass_ofTransfer` (the Supply wiring, unchanged).
  3. **§3** — the shared-`cSeam` tie from the PRODUCING side:
     `capstoneSeamTransferSeam_cSeam_ne_zero_of_topFace_meets_attach` (a genuine attachment — top face
     meeting `range φ` — forces `cSeam ≠ 0`), the positive form of the round-13 anti-fake.
  4. **§4 `capstoneSeamTransferSeam_zero`** — the degenerate floor (`z = 0`, `cHa = 0`, `cSeam = 0`):
     the shape is non-vacuous but certifies nothing (NOT a discharge — `z = 0` is not a fundamental
     cycle), the producing-side analogue of the gate's `closedSeamAttachedCollarBridge_zero`.

## What remains of the hasClass row

After this module the deepest capstone atom, for connected `s.M`, is exactly: inhabit
`CapstoneSeamTransferResidual` = {a fundamental cycle `z` of `M`, a SHARED `cSeam` on `↥S` with the two
co-adapted splits (`§2`'s inputs over `diskDetectChain`), the straddle detection `hdetAB`}. The sole
remaining GEOMETRIC residual is the shared `cSeam` satisfying BOTH splits simultaneously — the
co-adaptation of `z` and `cHa` to the attaching map. It is NOT kernel-false (it holds for the actual
collar of a genuine surgery); it walls only at the CLOSED-`S` support barrier of the current
open-cover/homeomorphism machinery (a machinery gap, prose-level, consistent with
`PinPlusTraceSeamResidualNarrow` §3). No new kernel no-go.

**Fences.** No collar theorem proved; no completeness Prop minted (the atom is the DATA structure
`CapstoneSeamTransferSeam`, not a Prop); the single shared `cSeam` field is never split into
independent cylinder/disk bridges (round-13 spec 2). Additive module. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no `native_decide`,
no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceSeamResidualNarrow

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.PinPlusTraceCapstoneSeamTransfer
open SKEFTHawking.PinPlusTraceCapstoneSeamTransferSupply
open SKEFTHawking.PinPlusTraceSeamResidualNarrow
open SKEFTHawking.PinPlusTraceDiskCorePair

namespace SKEFTHawking.PinPlusTraceSeamChainConstruct

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  [CompactSpace s.M] [Nonempty s.M] [PreconnectedSpace s.M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)

/-! ## §1. The disk side of the consumption structure IS the collar bridge. -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The disk side of `CapstoneSeamTransferSeam` is a genuine collar-bridge instance.** Any
inhabitant `R` supplies, through its shared seam chain `R.cSeam` and free-sphere remainder `R.vOut`,
exactly a decomposition of the disk boundary `∂cHa = (ambIncl S)_# cSeam + vOut` with `vOut` in the
free sphere — the defining shape of `ClosedSeamAttachedCollarBridge S (∂cHa)`. (Uses the defeq
`seamLegHa ≡ ambIncl S` and `.Ha ≡ D⁵`.) So the gate-located support Prop (#202 §2) is precisely the
disk half of the consumption structure; the shared-`cSeam` field is what ties it to the cylinder
half, which the bare bridge lacks. -/
theorem capstoneSeamTransferSeam_disk_bridge {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (R : CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa) :
    ClosedSeamAttachedCollarBridge S
      (chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa) :=
  ⟨R.cSeam, R.vOut, R.hsplitHa, R.hvOut⟩

/-! ## §2. The shared-seam constructor — wiring a bridge-shaped seam chain into consumption. -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The shared-`cSeam` constructor.** Given the SINGLE seam chain `cSeam` on `↥S` and the two
co-adapted splits — the cylinder-side split `z@⊤ = (φ-leg)_# cSeam + wOut` (`wOut` off the attaching
region) and the disk-side split `∂cHa = (ambIncl S)_# cSeam + vOut` (`vOut` free-sphere), the latter
stated in the collar-bridge output shape — this assembles a `CapstoneSeamTransferSeam`. The disk
split is accepted into the `hsplitHa` field by the `ambIncl S ≡ seamLegHa` defeq: a bridge-derived
`cSeam` (shape `(ambIncl S)_#`) plugs straight in, keeping the one shared field. This is the
`with cSeam in hand → consume` step: its output feeds `CapstoneSeamTransferSeam.toTransfer` and hence
`CapstoneSeamTransferResidual.seam`. -/
def capstoneSeamTransferSeam_ofSharedSeam {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (cSeam : SingularChain (TopCat.of ↥S) (3 + 1))
    (wOut : SingularChain (cyl (TopCat.of s.M)) (3 + 1))
    (hsplit : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      = mapChain (seamLegCyl s S φ hφ) (3 + 1) cSeam + wOut)
    (hwOut : wOut ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
        ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1))
    (vOut : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1))
    (hsplitHa : chainBoundary (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 1) cHa
      = mapChain (seamLegHa s S hS φ hφ hφinj) (3 + 1) cSeam + vOut)
    (hvOut : vOut ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
        ({q : D5 | ‖(q : EuclideanSpace ℝ (Fin 5))‖ = 1} \ S) (3 + 1)) :
    CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa where
  cSeam := cSeam
  wOut := wOut
  hsplit := hsplit
  hwOut := hwOut
  vOut := vOut
  hsplitHa := hsplitHa
  hvOut := hvOut

/-! ## §3. The shared-`cSeam` tie, producing side — genuine attachment forces a nonzero seam. -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **A degenerate (zero) seam forces the top face off the attaching region** (the gate tie, re-proved
here self-contained for the producing side). If `R.cSeam = 0` the cylinder split collapses to
`z@⊤ = wOut` with `wOut` supported off `range φ`. -/
theorem capstoneSeamTransferSeam_topFace_off_of_cSeam_zero {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (R : CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa) (h0 : R.cSeam = 0) :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∈ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1) := by
  have h := R.hsplit
  rw [h0, map_zero, zero_add] at h
  rw [h]
  exact R.hwOut

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **THE PRODUCING-SIDE ANTI-FAKE (contrapositive)** — a genuine attachment forces a NONZERO seam.
If the cylinder's top face `z@⊤` is NOT supported off the attaching region (i.e. it genuinely meets
`range φ`), then any `CapstoneSeamTransferSeam` inhabitant has `R.cSeam ≠ 0`. So the shared seam chain
is load-bearing exactly when the surgery genuinely attaches: a fake with `cSeam := 0` (spec-2
anti-laundering) is impossible whenever the fundamental top face touches the seam. The positive form
of the round-13 shared-`cSeam` tie, established from the producing side. -/
theorem capstoneSeamTransferSeam_cSeam_ne_zero_of_topFace_meets_attach
    {z : cycles (TopCat.of s.M) (2 + 2)}
    {cHa : SingularChain (TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha) (3 + 2)}
    (R : CapstoneSeamTransferSeam s S hS φ hφ hφinj z cHa)
    (hmeet : mapChain (slice (graphHom (TopCat.of s.M)) 1) (3 + 1)
        (z : SingularChain (TopCat.of s.M) (3 + 1))
      ∉ subspaceChains (X := TopCat.of (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
          ((Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))) \ Set.range φ) (3 + 1)) :
    R.cSeam ≠ 0 :=
  fun h0 => hmeet (capstoneSeamTransferSeam_topFace_off_of_cSeam_zero s S hS φ hφ hφinj R h0)

/-! ## §4. The degenerate floor — the shape alone certifies nothing (producing-side non-vacuity). -/

omit [Nonempty s.M] [PreconnectedSpace s.M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M] in
/-- **The zero inhabitant — the degenerate floor.** `CapstoneSeamTransferSeam` is inhabited at the
degenerate data `z = 0`, `cHa = 0`, `cSeam = 0` for EVERY attaching region `S` and map `φ`: all four
faces vanish and the two splits collapse to `0 = 0`. So the structure per se is non-vacuous but
certifies nothing — a genuine seam requires nonzero data (§3). The producing-side analogue of the
gate's `closedSeamAttachedCollarBridge_zero` (#202 §2). NOT a discharge: `z = 0` is not a fundamental
cycle and `cHa = 0` is not a detecting chain, so this floor does NOT feed
`CapstoneSeamTransferResidual` (whose `hz` demands `z` represent the nonzero fundamental class). -/
def capstoneSeamTransferSeam_zero :
    CapstoneSeamTransferSeam s S hS φ hφ hφinj (0 : cycles (TopCat.of s.M) (2 + 2)) 0 where
  cSeam := 0
  wOut := 0
  hsplit := by simp
  hwOut := Submodule.zero_mem _
  vOut := 0
  hsplitHa := by simp
  hvOut := Submodule.zero_mem _

end

end SKEFTHawking.PinPlusTraceSeamChainConstruct
