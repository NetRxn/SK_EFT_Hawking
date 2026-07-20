/-
# Phase 5q.H completeness geometric leg — LANE H-3: the W-admissibility transfer across the handle.

**What this file is (the RISK-1 audit's constructive residue).** Lane H-3's mandate is to move the
plain-cylinder admissibility atoms across the KT 2-handle attachment onto the eleven W-admissibility
fields of `CapstoneAmbientSupply` (`PinPlusTraceCapstoneInhabit.lean`). The audit (reported to the
lead) found that the eleven fields are ALREADY reduced by banked machinery — `CapstoneCohomologyMVDatum`
(findim ← MV cover), `capstone_dimeq14/23_of_flip` (dimeq ← two-sided nondeg + MV),
`capstone_hwu_of_steenrodKronecker` (hwu ← Steenrod–Kronecker vanishings), `hasClass_ofTransfer`
(hasClass; the seam T-input is the settled-dead `seam-transfer-open-support-uninhabitable` shape) — to
CARRIER-geometric residuals that the provider's cylinder `WAdmPinned` (a Poincaré–Lefschetz datum of the
CYLINDER `M×I`, not of `W`) does not feed. The genuinely-open, genuinely-transferable atom this file
closes is the **boundary two-ends comparison** feeding the relative-cohomology finiteness fields
`findimRel14`/`findimRel23`: the trace boundary `∂W = M ⊔ M′` is exactly the disjoint union of the two
closed-embedded ends supplied by the `SurgeredEndDatum` (the source end `ktSourceEnd` and the surgered
end `eM'`), so its all-degree homology finiteness — the `hBd` obligation of `CapstoneCohomologyMVDatum`
— transfers from the two ends' closed-4-manifold finiteness with NO new geometric input.

**§1** the general topology core `finiteDimensional_homology_sub_two_ends`: a subspace that is the
disjoint union of the ranges of two continuous injections of closed 4-manifolds into a Hausdorff space
has all-degree finite mod-2 homology. Reusable, carrier-agnostic.

**§2** the capstone instantiation `capstone_boundary_hBd`: the `hBd` field of the capstone MV datum,
discharged from a `SurgeredEndDatum` for arbitrary attaching data, consuming the attachment data
abstractly (no Lane-H-1 disk dependency).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneMVPieces

open scoped Manifold
open Topology
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.PinPlusTraceCapstoneMVPieces
open SKEFTHawking.PinPlusTraceCapstoneCohomologyMV
open SKEFTHawking.PinPlusTraceCapstoneInhabit

namespace SKEFTHawking.KTCompletenessTransfer

noncomputable section

/-! ## §1. The general boundary-two-ends finiteness core. -/

/-- **A subspace that is the disjoint union of the ranges of two closed-4-manifold injections has
all-degree finite mod-2 homology.** The two ranges are closed (compact image in a Hausdorff space),
disjoint, and cover `bd`, so within `bd` each is clopen; each is homeomorphic to its closed-4-manifold
source (a continuous bijection from a compact space to a Hausdorff space), so the two-closed-ends brick
`finiteDimensional_homology_of_two_closed_ends` applies. Carrier-agnostic; the `∂W = M ⊔ M′` transfer. -/
theorem finiteDimensional_homology_sub_two_ends
    {X : TopCat} [T2Space ↑X]
    {M₁ M₂ : Type}
    [TopologicalSpace M₁] [T2Space M₁] [CompactSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M₁]
    [TopologicalSpace M₂] [T2Space M₂] [CompactSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M₂]
    (bd : Set ↑X)
    (f : M₁ → ↑X) (hf : Continuous f) (hfinj : Function.Injective f)
    (g : M₂ → ↑X) (hg : Continuous g) (hginj : Function.Injective g)
    (hdisj : Disjoint (Set.range f) (Set.range g))
    (hbd : bd = Set.range f ∪ Set.range g) (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology (sub bd) n) := by
  -- the two ends are closed embeddings into `X`
  have hfce : IsClosedEmbedding f := hf.isClosedEmbedding hfinj
  have hgce : IsClosedEmbedding g := hg.isClosedEmbedding hginj
  -- the inclusion `↥bd ↪ X` is continuous
  have hval : Continuous (fun y : ↑(sub bd) => (y : ↑X)) := continuous_subtype_val
  -- `U` = the source end inside `↥bd`
  set U : Set ↑(sub bd) := (fun y : ↑(sub bd) => (y : ↑X)) ⁻¹' Set.range f with hUdef
  -- `Uᶜ` is the surgered end inside `↥bd`
  have hUc : Uᶜ = (fun y : ↑(sub bd) => (y : ↑X)) ⁻¹' Set.range g := by
    ext y
    simp only [hUdef, Set.mem_compl_iff, Set.mem_preimage]
    constructor
    · intro hy
      rcases hbd.subset y.2 with h | h
      · exact absurd h hy
      · exact h
    · intro hy hy'
      exact (Set.disjoint_left.mp hdisj hy' hy)
  have hUclosed : IsClosed U := hfce.isClosed_range.preimage hval
  have hUcclosed : IsClosed Uᶜ := by
    rw [hUc]; exact hgce.isClosed_range.preimage hval
  have hU : IsClopen U := ⟨hUclosed, isClosed_compl_iff.mp hUcclosed⟩
  -- the source end is homeomorphic to `M₁`
  have e₁ : ↑(sub U) ≃ₜ M₁ := by
    let fwd : M₁ → ↥U := fun m =>
      ⟨⟨f m, by rw [hbd]; exact Or.inl ⟨m, rfl⟩⟩, ⟨m, rfl⟩⟩
    have hbij : Function.Bijective fwd := by
      refine ⟨fun a b h => hfinj (Subtype.ext_iff.mp (Subtype.ext_iff.mp h)), fun y => ?_⟩
      obtain ⟨⟨w, hwbd⟩, hwU⟩ := y
      obtain ⟨m, hm⟩ := hwU
      exact ⟨m, Subtype.ext (Subtype.ext hm)⟩
    have hcont : Continuous fwd :=
      Continuous.subtype_mk (Continuous.subtype_mk hf (fun m => by rw [hbd]; exact Or.inl ⟨m, rfl⟩))
        (fun m => ⟨m, rfl⟩)
    exact (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective fwd hbij) hcont).symm
  -- the surgered end is homeomorphic to `M₂`
  have e₂ : ↑(sub Uᶜ) ≃ₜ M₂ := by
    let fwd : M₂ → ↥Uᶜ := fun m =>
      ⟨⟨g m, by rw [hbd]; exact Or.inr ⟨m, rfl⟩⟩, by
        show (⟨g m, by rw [hbd]; exact Or.inr ⟨m, rfl⟩⟩ : ↑(sub bd)) ∈ Uᶜ
        rw [hUc]; exact ⟨m, rfl⟩⟩
    have hbij : Function.Bijective fwd := by
      refine ⟨fun a b h => hginj (Subtype.ext_iff.mp (Subtype.ext_iff.mp h)), fun y => ?_⟩
      obtain ⟨⟨w, hwbd⟩, hwU⟩ := y
      rw [hUc] at hwU
      obtain ⟨m, hm⟩ := hwU
      exact ⟨m, Subtype.ext (Subtype.ext hm)⟩
    have hcont : Continuous fwd :=
      Continuous.subtype_mk
        (Continuous.subtype_mk hg (fun m => by rw [hbd]; exact Or.inr ⟨m, rfl⟩))
        (fun m => by
          show (⟨g m, by rw [hbd]; exact Or.inr ⟨m, rfl⟩⟩ : ↑(sub bd)) ∈ Uᶜ
          rw [hUc]; exact ⟨m, rfl⟩)
    exact (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective fwd hbij) hcont).symm
  exact finiteDimensional_homology_of_two_closed_ends (X := sub bd) hU e₁ e₂ n

/-! ## §2. The capstone instantiation: `hBd` from a `SurgeredEndDatum`, for arbitrary attaching data. -/

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M] [T2Space t.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The capstone boundary finiteness `hBd`, transferred from the `SurgeredEndDatum`.** The trace
boundary `∂W = range (ktSourceEnd) ∪ range eM′` (`d.bdry`) is the disjoint union (`d.disj`) of the two
closed-embedded ends — the source end `M = s.M` (`ktSourceEnd`, a closed embedding) and the surgered end
`M′ = t.M` (`eM′`, continuous injective from the compact `t.M` into the Hausdorff carrier). Both are
closed charted 4-manifolds, so `∂W` has all-degree finite mod-2 homology by
`finiteDimensional_homology_sub_two_ends`. This is the `hBd` field of `CapstoneCohomologyMVDatum`
(feeding `findimRel14`/`findimRel23`), discharged generically over the attaching data — no Lane-H-1
disk dependency, the attachment data consumed abstractly through the `SurgeredEndDatum`. -/
theorem capstone_boundary_hBd (n : ℕ) :
    letI := capstone_t2Space s t S hS φ hφ hφinj cd hseam d
    FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) n) := by
  haveI := capstone_t2Space s t S hS φ hφ hφinj cd hseam d
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) s.M :=
    inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M)
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) t.M :=
    inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 4)) t.M)
  exact finiteDimensional_homology_sub_two_ends
    (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
    (bd := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
    (M₁ := s.M) (M₂ := t.M)
    (ktSourceEnd s.M D5 S hS φ hφ hφinj)
    (continuous_ktSourceEnd s.M D5 S hS φ hφ hφinj)
    (injective_ktSourceEnd s.M D5 S hS φ hφ hφinj)
    d.eM' d.cont d.inj d.disj d.bdry n

end

end SKEFTHawking.KTCompletenessTransfer
