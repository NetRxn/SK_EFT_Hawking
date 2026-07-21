/-
# Phase 5q.H — the per-piece collar, made CONCRETE: `collarᵢ = {fiberNorm ≥ 1/2}`

`KummerPairTransportInt.pairH2TwoTorsionFree_iff_pieces` reduced the `b₂` residual
`PairH2TwoTorsionFree` to sixteen per-piece statements about `H₂(ResE, pieceSub CollarInE i; ℤ)`.
Those sixteen subspaces were still *opaque*: `pieceSub CollarInE i` is defined by pulling the K3-level
thickened `Q`-piece `qThick` back through the weld, so nothing about it could be used geometrically.

This module removes that opacity. `KummerK7MVAssembly.qThick_inter_eImage : qThick ∩ eImage = eOuter`
identifies the collar inside the exceptional set with the image of the **outer half-collar carrier**
`{p | 1/2 ≤ fiberNorm p.2}`, and `KummerWeld.weldMk_inr_injective` says the sixteen `E`-copies embed
disjointly. Together:

`pieceSub_collarInE_eq : pieceSub CollarInE i = outerE`  with  `outerE = {y : ResE | 1/2 ≤ fiberNorm y}`

— **the same set for every `i`** (the 16-fold indexing really is bookkeeping), and a completely
explicit sublevel set of the chart-independent fiber norm on the two-chart `𝒪(−2)` model.

Consequently (`pairH2TwoTorsionFree_iff_outerE`, a genuine `↔`) the whole `b₂` residual is

> `H₂(ResE, {fiberNorm ≥ 1/2}; ℤ)` has no 2-torsion

— one statement about ONE explicit space, with no reference to K3, to the weld, to `EIndex`, or to
the sixteen-fold indexing. `pairH2TwoTorsionFree_of_outerE` is the one-directional consumer feeding
`KummerPairHalving.kummerK3_b2_target_of_exceptional_halvable`.

§3 records the geometric orientation of the target: the collar is disjoint from the zero section
(`outerE_subset_compl_zeroLocus`), so `(ResE, outerE)` is a pair whose relative `H₂` sees the
zero-section class — the Euler-number−2 content — and `outerE` carries the whole boundary
(`boundaryE_subset_outerE`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KummerPairTransportInt

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.KummerResolutionPiece (ResE zeroLocus boundaryE)
open SKEFTHawking.KummerWeld (EIndex weldMk weldMk_inr_injective)
open SKEFTHawking.KummerWeldFiberFlow (fiberNorm)
open SKEFTHawking.KummerK7MVAssembly (qThick eOuter eOuterCarrier qThick_inter_eImage eImageHomeo)
open SKEFTHawking.KummerPairTubeSeparation (ESub CollarInE PairH2 PairH2TwoTorsionFree)
open SKEFTHawking.KummerPairTransportInt (ResEtop pieceSub pairH2TwoTorsionFree_iff_pieces)

namespace SKEFTHawking.KummerPieceCollarInt

noncomputable section

/-! ## §1. The concrete collar `outerE = {fiberNorm ≥ 1/2}` -/

/-- **The outer half-collar of a single resolution piece** — the fiber-radius `≥ 1/2` locus of the
two-chart `𝒪(−2)` disk bundle `E`. This is the intrinsic model of the collar the `b₂` pair
`(eImage, collar)` is taken relative to. -/
def outerE : Set ↑ResEtop := {y | 1 / 2 ≤ fiberNorm y}

/-- The underlying `K3` point of the `i`-th copy of `y`. -/
theorem coe_eImageHomeo (i : EIndex) (y : ResE) :
    ((eImageHomeo (i, y) : ↥SKEFTHawking.KummerWeld.eImage) : SKEFTHawking.KummerWeld.KummerK3)
      = weldMk (Sum.inr (i, y)) := rfl

/-- **The per-piece collar is `outerE`, for every `i`.** The K3-level collar `qThick ∩ eImage` is the
outer half-collar image (`qThick_inter_eImage`), and the sixteen `E`-copies are disjointly embedded
(`weldMk_inr_injective`), so the `i`-th piece's induced subspace is exactly the fiber-radius `≥ 1/2`
locus — independent of `i`. -/
theorem pieceSub_collarInE_eq (i : EIndex) : pieceSub CollarInE i = outerE := by
  ext y
  show (weldMk (Sum.inr (i, y)) : SKEFTHawking.KummerWeld.KummerK3) ∈ qThick ↔ 1 / 2 ≤ fiberNorm y
  constructor
  · intro hq
    have hmem : weldMk (Sum.inr (i, y)) ∈ eOuter := by
      rw [← qThick_inter_eImage]
      exact ⟨hq, ⟨(i, y), rfl⟩⟩
    obtain ⟨p, hp, hpe⟩ := hmem
    have : p = (i, y) := weldMk_inr_injective hpe
    rw [this] at hp
    exact hp
  · intro hy
    have : weldMk (Sum.inr (i, y)) ∈ eOuter := ⟨(i, y), hy, rfl⟩
    rw [← qThick_inter_eImage] at this
    exact this.1

/-! ## §2. The `b₂` residual as one statement about one explicit space -/

/-- **The whole `b₂` residual, concretely.** `PairH2TwoTorsionFree` — the last open input to
`kummerK3_b2_target` — holds **iff** the relative `H₂` of the single explicit pair
`(E, {fiberNorm ≥ 1/2})` has no 2-torsion. A genuine biconditional: `pairH2TwoTorsionFree_iff_pieces`
supplies the 16-fold reduction and `pieceSub_collarInE_eq` identifies every piece with `outerE`, so
no strength is lost in either direction. -/
theorem pairH2TwoTorsionFree_iff_outerE :
    PairH2TwoTorsionFree
      ↔ ∀ m : RelHomologyInt (X := ResEtop) outerE 2, (2 : ℤ) • m = 0 → m = 0 := by
  have hne : Nonempty EIndex :=
    Fintype.card_pos_iff.mp (by rw [SKEFTHawking.KummerWeld.eIndex_card]; norm_num)
  obtain ⟨c⟩ := hne
  rw [pairH2TwoTorsionFree_iff_pieces]
  constructor
  · intro h
    have h0 := h c
    rw [pieceSub_collarInE_eq] at h0
    exact h0
  · intro h i
    rw [pieceSub_collarInE_eq i]
    exact h

/-- **The consumer form** — the concrete per-piece statement supplies the residual, hence (through
`KummerPairHalving.pairH2TwoTorsionFree_iff_exceptional_halvable` →
`kummerK3_b2_target_of_exceptional_halvable`) the `H₂(K3;ℤ) ≅ ℤ²²` headline. -/
theorem pairH2TwoTorsionFree_of_outerE
    (h : ∀ m : RelHomologyInt (X := ResEtop) outerE 2, (2 : ℤ) • m = 0 → m = 0) :
    PairH2TwoTorsionFree :=
  pairH2TwoTorsionFree_iff_outerE.mpr h

/-- Transport of a relative integral homology group along an equality of subspaces. -/
def relHomologyCongrSet {S T : Set ↑ResEtop} (h : S = T) (n : ℕ) :
    RelHomologyInt S n ≃ₗ[ℤ] RelHomologyInt T n := by
  subst h; exact LinearEquiv.refl _ _

/-- **The `b₂` group is sixteen copies of ONE concrete group**:
`PairH2 ≅ (EIndex → H₂(E, {fiberNorm ≥ 1/2}; ℤ))`. The `ℤ`-linear form of
`pieceSub_collarInE_eq` composed with `KummerPairTransportInt.pairH2SplitInt`; unlike the latter its
target no longer mentions `pieceSub`, `CollarInE`, or the weld. -/
def pairH2SplitOuter : PairH2 ≃ₗ[ℤ] (EIndex → RelHomologyInt (X := ResEtop) outerE 2) :=
  SKEFTHawking.KummerPairTransportInt.pairH2SplitInt.trans
    (LinearEquiv.piCongrRight fun i => relHomologyCongrSet (pieceSub_collarInE_eq i) 2)

/-! ## §3. Where the collar sits: off the zero section, around the whole boundary -/

/-- `outerE` misses the zero section — so the pair `(E, outerE)` is exactly the pair whose relative
`H₂` records the zero-section class, i.e. the Euler-number `−2` content. -/
theorem outerE_subset_compl_zeroLocus : outerE ⊆ (zeroLocus : Set ResE)ᶜ := by
  intro y hy hz
  have h0 : fiberNorm y = 0 := by
    obtain ⟨z, hzy | hzy⟩ := hz
    · rw [hzy]
      simp [SKEFTHawking.KummerResolutionPiece.zeroPt,
        SKEFTHawking.KummerResolutionPiece.zeroFiber]
    · rw [hzy]
      simp [SKEFTHawking.KummerResolutionPiece.zeroPt,
        SKEFTHawking.KummerResolutionPiece.zeroFiber]
  have hy' : (1 : ℝ) / 2 ≤ fiberNorm y := hy
  rw [h0] at hy'
  norm_num at hy'

/-- `outerE` contains the whole boundary `∂E` (the `fiberNorm = 1` locus). -/
theorem boundaryE_subset_outerE : (boundaryE : Set ResE) ⊆ outerE := by
  intro y hy
  have : fiberNorm y = 1 := SKEFTHawking.KummerWeldFiberFlow.fiberNorm_eq_one_iff.mpr hy
  show (1 : ℝ) / 2 ≤ fiberNorm y
  rw [this]; norm_num

/-- **`outerE` is a proper, nonempty piece of `E`** — a falsifiable pin: it is not all of `E` (the
zero section is outside) and not empty (the boundary is inside). -/
theorem outerE_ne_univ_and_ne_empty :
    outerE ≠ (Set.univ : Set ↑ResEtop) ∧ outerE ≠ (∅ : Set ↑ResEtop) := by
  constructor
  · intro h
    have hz : SKEFTHawking.KummerResolutionPiece.chart0 (⟨0, by simp⟩, ⟨0, by simp⟩) ∈ outerE := by
      rw [h]; trivial
    have hz' : (1 : ℝ) / 2 ≤ ‖((0 : ℂ))‖ := hz
    simp at hz'
    norm_num at hz'
  · intro h
    have hb : SKEFTHawking.KummerResolutionPiece.chart0 (⟨0, by simp⟩, ⟨1, by simp⟩) ∈ outerE := by
      show (1 : ℝ) / 2 ≤ ‖((1 : ℂ))‖
      simp
      norm_num
    rw [h] at hb
    exact hb

end

end SKEFTHawking.KummerPieceCollarInt
