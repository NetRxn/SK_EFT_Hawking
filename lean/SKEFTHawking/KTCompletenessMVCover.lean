/-
# Phase 5q.H close-out — THE MV COLLAR-THICKENED COVER: the interior cover, the overlap
# identification, and the collar-derived overlap homeomorphism, for ARBITRARY attachment data.

`CapstoneCohomologyMVDatum`/`CapstoneMVTransferRow` (`PinPlusTraceCapstoneCohomologyMV.lean`,
`PinPlusTraceCapstoneMVPieces.lean`) reduce the four capstone cohomology finite-dimensionality atoms
to a two-piece Mayer–Vietoris cover `W = A ∪ B` whose INTERIORS cover, plus per-piece homeomorphisms
`eA`/`eB`/`eAB`. The pieces' `hcov` field is the load-bearing residual: `HandleAttachment` banks only
the CLOSED range union `range fromCyl ∪ range fromHandle = univ` (`range_fromCyl_union_range_fromHandle`),
while Mayer–Vietoris needs the two INTERIORS to cover. This module supplies the missing cover, its
interior-covering proof, the overlap identification, and the overlap homeomorphism — for ARBITRARY
attachment data `(s, t, S, φ, cd, hseam, d)`, consuming nothing instance-specific.

## THE COLLAR FORK — respected (route correction, lead 2026-07-20).

No general collar-neighbourhood theorem (Mathlib-absent, off-critical-path). The capstone attachment
carries an EXPLICIT per-instance collar: the `SeamCollarDatum` field `cd` (whose `cd.hHomeo` presents
the open seam neighbourhood `cd.seamNbhd` as a welded-collar product `WeldedCollarModel cd.A =
cd.A × (welded interval)`), together with `hseam : seamRegion ⊆ cd.seamNbhd`. We THICKEN EACH CLOSED
PIECE INTO THAT GIVEN OPEN COLLAR:

* `coverA := range fromCyl ∪ cd.seamNbhd`  (the cyl side, thickened by the whole open collar);
* `coverB := range fromHandle ∪ cd.seamNbhd`  (the handle side, thickened by the whole open collar).

## §-map
* **§1 — the collar as a carrier subset** `seamSet` (`= cd.seamNbhd`, open) and the cover
  `coverA`/`coverB`: the two closed pieces each thickened by the open seam collar.
* **§2 — the overlap identification** `coverA_inter_coverB`: `coverA ∩ coverB = cd.seamNbhd` exactly
  (the seam `range fromCyl ∩ range fromHandle = seamRegion` sits inside the open collar by `hseam`, so
  the Boolean overlap `(P ∪ N) ∩ (Q ∪ N) = (P ∩ Q) ∪ N` collapses to `N = cd.seamNbhd`).
* **§3 — the interior cover** `coverInteriors_cover`/`hcov`: the two INTERIORS cover `W`. Pure-cyl
  points sit in `interior coverA` via the open complement `(range fromHandle)ᶜ ⊆ range fromCyl ⊆
  coverA`; pure-handle points in `interior coverB` symmetrically; seam points in `cd.seamNbhd ⊆
  interior` of both (the collar is open). NO general collar theorem — only `hseam`, the closed ranges,
  and the closed range union.
* **§4 — the overlap homeomorphism** `eAB`: `↥(coverA ∩ coverB) ≃ₜ WeldedCollarModel cd.A`, transported
  from `cd.hHomeo` across the overlap identity by `Homeomorph.setCongr`. The overlap comparison homeo
  the transfer row asks for, for FREE from the collar datum.
* **§5 — the transfer-row assembly** `coverTransferRow`: plug `coverA`/`coverB`/`hcov`/`eAB` into
  `CapstoneMVTransferRow.ofPieces`, reducing the whole transfer row to exactly the two piece
  homeomorphisms `eA`/`eB` (the collar-absorption / deformation-retraction residual — genuinely a
  homotopy-equivalence obligation, not a homeomorphism the closed→open thickening can supply), the
  overlap finiteness `hYAB` (a genuine geometric input until the concrete attaching region is pinned),
  and the boundary two-closed-ends split (a separate banked lane). Everything else falls.

**Fences.** THE COLLAR FORK is respected: `coverA`/`coverB` are the constructed handle-attachment's own
`range fromCyl`/`range fromHandle` structure, thickened by the GIVEN `cd.seamNbhd` collar — never a
general collar theorem. The sealed heavy carrier term appears only in field/binder TYPES (via
`TopCat.of (capstoneB …).W`, which reduces definitionally to `(ktHandleAttachment …).carrier`), never
re-elaborated inside a constructed term.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneMVPieces

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCohomologyMV
open SKEFTHawking.PinPlusTraceCapstoneMVPieces

namespace SKEFTHawking.KTCompletenessMVCover

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §1. The collar as a carrier subset, and the collar-thickened cover. -/

/-- **The open seam collar as a subset of the capstone carrier** — `cd.seamNbhd`, viewed at the
`TopCat.of (capstoneB …).W` carrier type (which reduces definitionally to `(ktHandleAttachment …).carrier`,
where `cd.seamNbhd` lives). The canonical carrier-typed spelling of the given open collar. -/
def seamSet : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) :=
  {x | x ∈ cd.seamNbhd}

/-- **The seam collar is open** — it is the given open seam neighbourhood `cd.seamNbhd`. -/
theorem isOpen_seamSet : IsOpen (seamSet s t S hS φ hφ hφinj cd hseam d) :=
  cd.seamNbhd.isOpen

/-- **The cyl-side piece of the MV cover** — the closed range `range fromCyl` (`≃ M × I`) thickened by
the whole open seam collar `cd.seamNbhd`. Open enough (with `coverB`) for the two INTERIORS to cover. -/
def coverA : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) :=
  Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
    ∪ seamSet s t S hS φ hφ hφinj cd hseam d

/-- **The handle-side piece of the MV cover** — the closed range `range fromHandle` (`≃ D⁵`) thickened
by the whole open seam collar `cd.seamNbhd`. -/
def coverB : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) :=
  Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle
    ∪ seamSet s t S hS φ hφ hφinj cd hseam d

/-! ## §2. The overlap identification — the two thickened pieces meet exactly on the open collar. -/

/-- **The seam sits inside the open collar** — `range fromCyl ∩ range fromHandle = seamRegion ⊆
cd.seamNbhd` (`hseam`). The seam is the glued attaching region, contained in the collar neighbourhood. -/
theorem seam_subset_seamSet :
    Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
        ∩ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle
      ⊆ seamSet s t S hS φ hφ hφinj cd hseam d := by
  rw [(ktHandleAttachment s.M D5 S hS φ hφ hφinj).range_fromCyl_inter_range_fromHandle]
  have hseamRegion :
      Set.range (fun a : ↥(ktHandleAttachment s.M D5 S hS φ hφ hφinj).S =>
          (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle
            (a : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha))
        = (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion :=
    (Set.image_eq_range _ _).symm
  rw [hseamRegion]
  exact hseam

/-- **The overlap identification** — the two thickened pieces meet exactly on the open seam collar:
`coverA ∩ coverB = cd.seamNbhd`. The Boolean overlap `(P ∪ N) ∩ (Q ∪ N) = (P ∩ Q) ∪ N` collapses to
`N` because the seam `P ∩ Q ⊆ N` (`seam_subset_seamSet`). -/
theorem coverA_inter_coverB :
    coverA s t S hS φ hφ hφinj cd hseam d ∩ coverB s t S hS φ hφ hφinj cd hseam d
      = seamSet s t S hS φ hφ hφinj cd hseam d := by
  have hseam' := seam_subset_seamSet s t S hS φ hφ hφinj cd hseam d
  simp only [coverA, coverB]
  ext w
  constructor
  · rintro ⟨hwA, hwB⟩
    rcases hwA with hwA | hwA
    · rcases hwB with hwB | hwB
      · exact hseam' ⟨hwA, hwB⟩
      · exact hwB
    · exact hwA
  · intro hw
    exact ⟨Or.inr hw, Or.inr hw⟩

/-! ## §3. The interior cover — the two INTERIORS cover `W` (the Mayer–Vietoris cover hypothesis). -/

/-- **The two interiors cover `W`** — the load-bearing collar upgrade. `HandleAttachment` banks only
the CLOSED range union; here the thickening by the open collar makes the two INTERIORS cover: a
pure-cyl point sits in `interior coverA` via the open complement `(range fromHandle)ᶜ ⊆ range fromCyl
⊆ coverA`; a pure-handle point in `interior coverB` symmetrically; a seam point in `cd.seamNbhd`, open
and inside both. Uses only `hseam`, the two closed ranges, and their closed union — no general collar
theorem. -/
theorem coverInteriors_cover :
    interior (coverA s t S hS φ hφ hφinj cd hseam d)
        ∪ interior (coverB s t S hS φ hφ hφinj cd hseam d)
      = Set.univ := by
  classical
  have hHandleClosed :
      IsClosed (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle) :=
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromHandle.isClosed_range
  have hCylClosed :
      IsClosed (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl) :=
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).isClosedEmbedding_fromCyl.isClosed_range
  have hcover :
      Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
          ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle = Set.univ :=
    (ktHandleAttachment s.M D5 S hS φ hφ hφinj).range_fromCyl_union_range_fromHandle
  have hseam' := seam_subset_seamSet s t S hS φ hφ hφinj cd hseam d
  have hNopen := isOpen_seamSet s t S hS φ hφ hφinj cd hseam d
  simp only [coverA, coverB]
  -- seam collar ⊆ interior of each piece (open subset of the piece).
  have hNiA : seamSet s t S hS φ hφ hφinj cd hseam d
      ⊆ interior (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
          ∪ seamSet s t S hS φ hφ hφinj cd hseam d) :=
    interior_maximal Set.subset_union_right hNopen
  have hNiB : seamSet s t S hS φ hφ hφinj cd hseam d
      ⊆ interior (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle
          ∪ seamSet s t S hS φ hφ hφinj cd hseam d) :=
    interior_maximal Set.subset_union_right hNopen
  -- pure-cyl region open ⊆ interior coverA.
  have hDA : (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle)ᶜ
      ⊆ interior (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
          ∪ seamSet s t S hS φ hφ hφinj cd hseam d) := by
    apply interior_maximal _ hHandleClosed.isOpen_compl
    intro w hw
    have hwC : w ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl := by
      have hmem : w ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
          ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle := by
        rw [hcover]; trivial
      rcases hmem with h | h
      · exact h
      · exact absurd h hw
    exact Or.inl hwC
  -- pure-handle region open ⊆ interior coverB.
  have hDB : (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl)ᶜ
      ⊆ interior (Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle
          ∪ seamSet s t S hS φ hφ hφinj cd hseam d) := by
    apply interior_maximal _ hCylClosed.isOpen_compl
    intro w hw
    have hwH : w ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle := by
      have hmem : w ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
          ∪ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle := by
        rw [hcover]; trivial
      rcases hmem with h | h
      · exact absurd h hw
      · exact h
    exact Or.inl hwH
  rw [Set.eq_univ_iff_forall]
  intro w
  by_cases hwC : w ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromCyl
  · by_cases hwH : w ∈ Set.range (ktHandleAttachment s.M D5 S hS φ hφ hφinj).fromHandle
    · exact Set.mem_union_left _ (hNiA (hseam' ⟨hwC, hwH⟩))
    · exact Set.mem_union_left _ (hDA hwH)
  · exact Set.mem_union_right _ (hDB hwC)

/-- **The Mayer–Vietoris cover hypothesis in the datum shape** — the `hcov` field of
`CapstoneCohomologyMVDatum`/`CapstoneMVTransferRow`, the `⋃ U ∈ {coverA, coverB}, interior U = univ`
form of `coverInteriors_cover`. -/
theorem hcov :
    (⋃ U ∈ ({coverA s t S hS φ hφ hφinj cd hseam d, coverB s t S hS φ hφ hφinj cd hseam d} :
        Set (Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))), interior U)
      = Set.univ := by
  rw [Set.biUnion_insert, Set.biUnion_singleton]
  exact coverInteriors_cover s t S hS φ hφ hφinj cd hseam d

/-! ## §4. The overlap homeomorphism — the collar datum's homeo, transported across the overlap. -/

/-- **The overlap comparison homeomorphism** — `↥(coverA ∩ coverB) ≃ₜ WeldedCollarModel cd.A`,
transported from the collar datum's `cd.hHomeo` across the overlap identification
`coverA ∩ coverB = cd.seamNbhd` (`Homeomorph.setCongr`). The overlap comparison homeo the transfer row
asks for, for FREE from the given collar. -/
def eAB :
    ↑(sub (coverA s t S hS φ hφ hφinj cd hseam d ∩ coverB s t S hS φ hφ hφinj cd hseam d))
      ≃ₜ WeldedCollarModel cd.A :=
  (Homeomorph.setCongr (coverA_inter_coverB s t S hS φ hφ hφinj cd hseam d)).trans cd.hHomeo

/-! ## §5. The transfer-row assembly — cover + hcov + eAB plugged in; residual = `eA`/`eB`. -/

/-- **The transfer-row assembly** — plug the collar-thickened cover `coverA`/`coverB`, its
interior-cover `hcov`, and the collar-derived overlap homeo `eAB` into `CapstoneMVTransferRow.ofPieces`.
The whole transfer row now reduces to exactly: the two piece homeomorphisms `eA`/`eB` (the
collar-absorption residual — a genuine homotopy-equivalence obligation, NOT a homeomorphism the
closed→open thickening supplies), the overlap finiteness `hYAB` (genuine geometric input), and the
boundary two-closed-ends split (`YBd`/`eBd`/`U`/`hU`/`e₁`/`e₂` — a separate banked lane). -/
def coverTransferRow
    (eA : ↑(sub (coverA s t S hS φ hφ hφinj cd hseam d))
      ≃ₜ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
    (eB : ↑(sub (coverB s t S hS φ hφ hφinj cd hseam d))
      ≃ₜ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
    (hYAB : ∀ n, FiniteDimensional (ZMod 2)
      (Homology (TopCat.of (WeldedCollarModel cd.A)) n))
    (YBd : TopCat)
    (eBd : ↑(sub (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) ≃ₜ ↑YBd)
    (U : Set ↑YBd) (hU : IsClopen U)
    {M₁ : Type} [TopologicalSpace M₁] [T2Space M₁] [CompactSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M₁]
    {M₂ : Type} [TopologicalSpace M₂] [T2Space M₂] [CompactSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M₂]
    (e₁ : ↑(sub U) ≃ₜ M₁) (e₂ : ↑(sub Uᶜ) ≃ₜ M₂) :
    CapstoneMVTransferRow s t S hS φ hφ hφinj cd hseam d :=
  CapstoneMVTransferRow.ofPieces s t S hS φ hφ hφinj cd hseam d
    (coverA s t S hS φ hφ hφinj cd hseam d) (coverB s t S hS φ hφ hφinj cd hseam d)
    (hcov s t S hS φ hφ hφinj cd hseam d) eA eB
    (TopCat.of (WeldedCollarModel cd.A)) (eAB s t S hS φ hφ hφinj cd hseam d) hYAB
    YBd eBd U hU e₁ e₂

end

end SKEFTHawking.KTCompletenessMVCover
