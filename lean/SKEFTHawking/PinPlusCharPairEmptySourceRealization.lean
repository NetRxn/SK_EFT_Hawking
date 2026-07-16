/-
# Phase 5q.H close-out (#165) — THE EMPTY-SOURCE MEMBRANE REALIZATION (the terminal KRS step).

The KRS lane's per-`p` membrane residual (`CapstoneAmbientSupplyWelded.real`) demands a
`GeoRealizationTied (TopCat.of p'.2.surf.M) (TopCat.of p.2.surf.M) p'.2.basis p.2.basis` — the
Σ-trace membrane between the surgered source's characteristic surface `Σ' = p'.2.surf` and the
target's `Σ = p.2.surf`. **The degenerate-case verdict (checked before formalizing):** the target
side can NEVER be empty — `0 < p.2.n` plus the carried basis `H¹(Σ) ≃ (Fin p.2.n → ℤ/2)` forces
`Σ ≠ ∅` (the empty surface has trivial `H¹`). The empty case lives on the SOURCE side only: the
TERMINAL surgery step (`p.2.n = 2`, `p'.2.n = 0`) may take the spin source's characteristic surface
`Σ' = ∅`. There the Σ-trace membrane degenerates to a compact 3-manifold `Q` with `∂Q = Σ` alone
(the classical "the characteristic surface bounds") — the σ-side of every joint condition dissolves.

This module formalizes exactly that dissolve:

* **§2 `emptySourceRealizationTied`** — for ANY empty σ-end `Sσ` and closed τ-end surface `Sτ`
  closed-embedded in a compact T2 space `Q`, the datum `∂Q := Sσ ⊔ Sτ`, `U := range inl` is a
  genuine `GeoRealizationTied Sσ Sτ bσ bτ`: every certificate is honest per-object topology
  (`Sσ` empty is compact + T2; the boundary inclusion `Sum.elim isEmptyElim ιY` is a continuous
  injection from a compact space into a T2 space, hence a closed embedding).
* **§3 the kernel identity** — `transportedBInc = boundingBInc ∘ (x ↦ x ∘ inr)`: the transported
  boundary-inclusion factors through the τ-block alone (the σ-block dies: `Fin nσ` is empty, so the
  σ-coordinates are `0` and every σ-term is killed by `map_zero`). `boundingBInc` is the single-
  surface bounding map `H₁(Σ) → H₁(Q)` read through the DERIVED (UCT-dual) basis — the classical
  bounding kernel, never a free field.
* **§4 the joint-condition dissolve** — `TaylorLegVanishes`/`JointLagrangian` for the pair
  `(qσ, qτ)` on the computed membrane kernel collapse to SINGLE-SURFACE conditions on the bounding
  kernel `ker (boundingBInc)`: `qτ` vanishes on it, and it is `B`-maximal — the classical
  "enhancement vanishes on the bounding Lagrangian" pin condition. The σ-side contributes `q 0 = 0`
  and `B 0 · = 0` only.
* **§5 the capstone cascade** — `TraceMembraneLeaves.ofCapstoneWeldedEmptySource`: the welded
  membrane row on the constructed capstone with an empty-Σ source, where `glueσ` is discharged
  VACUOUSLY (the σ-boundary component is empty) and the τ-glue is taken in its clean single-surface
  form (over points of `Σ` directly, not of `sub Uᶜ`). The membrane residual for the terminal KRS
  step is thereby: `Q` (compact, T2, `MembraneModel`-charted), the closed embedding `Σ ↪ Q`, its
  `H₁` basis, the two single-surface kernel conditions, and the weld/`hQ`/τ-glue row — the σ-side
  atoms are GONE.

Dimension discipline: `W` 5-dim, `Q` 3-dim (`MembraneModel`-charted), the ends' characteristic
surfaces 2-dim; the source Σ' is EMPTY here (the terminal step); the handle is `D⁵` upstairs.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneMembraneWeld

open scoped Manifold
open Topology
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied

namespace SKEFTHawking.PinPlusCharPairEmptySourceRealization

/-! ## §1. Empty-space topology helpers. -/

/-- Any map out of an empty space is continuous (every preimage is the empty set). -/
theorem continuous_of_isEmpty {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [IsEmpty X]
    (f : X → Y) : Continuous f :=
  continuous_def.mpr fun s _ => by
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' s)]
    exact isOpen_empty

/-- An empty space is Hausdorff. -/
theorem t2Space_of_isEmpty {X : Type} [TopologicalSpace X] [IsEmpty X] : T2Space X :=
  ⟨fun x => isEmptyElim x⟩

/-- An empty space is compact (`univ = ∅`). -/
theorem compactSpace_of_isEmpty {X : Type} [TopologicalSpace X] [IsEmpty X] : CompactSpace X :=
  ⟨by rw [Set.univ_eq_empty_iff.mpr ‹IsEmpty X›]; exact isCompact_empty⟩

/-- The left component `sub (range inl)` of a sum with empty left summand is empty. -/
theorem isEmpty_sub_range_inl {A B : TopCat} [IsEmpty (A : Type)] :
    IsEmpty ↑(sub (X := TopCat.of (↑A ⊕ ↑B)) (Set.range (Sum.inl : ↑A → ↑A ⊕ ↑B))) :=
  ⟨fun x => by obtain ⟨a, _⟩ := x.2; exact isEmptyElim a⟩

/-! ## §2. The empty-source realization. -/

variable {nσ nτ : ℕ} (Sσ Sτ : TopCat) [IsEmpty (Sσ : Type)]
  [T2Space (Sτ : Type)] [CompactSpace (Sτ : Type)]
  (bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
  (bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
  (QC : TopCat) [T2Space (QC : Type)] [CompactSpace (QC : Type)]
  (ιY : C((Sτ : Type), (QC : Type)))
  (hιY : IsClosedEmbedding ιY)
  (mid : ℕ) (eQ : Homology QC 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2))

/-- The empty-source boundary inclusion `Sσ ⊔ Sτ → Q`: the σ-summand is empty, the τ-summand goes
through the given closed embedding `ιY : Sτ ↪ Q`. -/
noncomputable def emptySourceBdryIncl : C(↑Sσ ⊕ ↑Sτ, ↑QC) :=
  ⟨Sum.elim (fun a => isEmptyElim a) ιY,
    (continuous_of_isEmpty _).sumElim ιY.continuous⟩

omit [T2Space (Sτ : Type)] [CompactSpace (Sτ : Type)]
  [T2Space (QC : Type)] [CompactSpace (QC : Type)] in
theorem emptySourceBdryIncl_injective (hinj : Function.Injective ιY) :
    Function.Injective (emptySourceBdryIncl Sσ Sτ QC ιY) := by
  rintro (a | y) (b | z) h
  · exact isEmptyElim a
  · exact isEmptyElim a
  · exact isEmptyElim b
  · exact congrArg Sum.inr (hinj h)

/-- **THE EMPTY-SOURCE REALIZATION** — the degenerate Σ-trace membrane of the terminal KRS surgery
step: the σ-end (the surgered spin source's characteristic surface) is EMPTY, and the membrane is
any compact T2 space `Q` in which the τ-end surface `Sτ` closed-embeds (`∂Q = ∅ ⊔ Sτ`). Every field
is honest per-object topology; the boundary homology bases are DERIVED from the carried cohomology
bases (the F2 pin), and the interior basis is the given `eQ`. -/
noncomputable def emptySourceRealizationTied : GeoRealizationTied Sσ Sτ bσ bτ where
  bdry := TopCat.of (↑Sσ ⊕ ↑Sτ)
  Q := QC
  U := Set.range (Sum.inl : ↑Sσ → ↑Sσ ⊕ ↑Sτ)
  hU := ⟨isClosed_range_inl, isOpen_range_inl⟩
  bdryT2 :=
    letI : T2Space (Sσ : Type) := t2Space_of_isEmpty
    inferInstanceAs (T2Space (↑Sσ ⊕ ↑Sτ))
  bdryCompact :=
    letI : CompactSpace (Sσ : Type) := compactSpace_of_isEmpty
    inferInstanceAs (CompactSpace (↑Sσ ⊕ ↑Sτ))
  QT2 := inferInstanceAs (T2Space (QC : Type))
  QCompact := inferInstanceAs (CompactSpace (QC : Type))
  ι := emptySourceBdryIncl Sσ Sτ QC ιY
  hιce :=
    letI : CompactSpace (Sσ : Type) := compactSpace_of_isEmpty
    (emptySourceBdryIncl Sσ Sτ QC ιY).continuous.isClosedEmbedding
      (emptySourceBdryIncl_injective Sσ Sτ QC ιY hιY.injective)
  homσ :=
    letI : IsEmpty
        ↑(sub (X := TopCat.of (↑Sσ ⊕ ↑Sτ)) (Set.range (Sum.inl : ↑Sσ → ↑Sσ ⊕ ↑Sτ))) :=
      isEmpty_sub_range_inl
    Homeomorph.empty
  homτ := (Homeomorph.setCongr Set.compl_range_inl).trans
    IsClosedEmbedding.inr.isEmbedding.toHomeomorph.symm
  mid := mid
  eQ := eQ

/-! ## §3. The kernel identity — the transported boundary-inclusion factors through the τ-block. -/

omit [IsEmpty (Sσ : Type)] [T2Space (Sτ : Type)] [CompactSpace (Sτ : Type)]
  [T2Space (QC : Type)] [CompactSpace (QC : Type)] in
/-- **The single-surface bounding map** `(Fin nτ → ℤ/2) →ₗ (Fin mid → ℤ/2)` — the geometric
`H₁(Σ) → H₁(Q)` of the embedding `ιY`, read through the DERIVED (UCT-dual) basis of the carried
cohomology basis `bτ` and the interior basis `eQ`. Its kernel is the classical bounding kernel of
the surface in the membrane. -/
noncomputable def boundingBInc : (Fin nτ → ZMod 2) →ₗ[ZMod 2] (Fin mid → ZMod 2) :=
  eQ.toLinearMap ∘ₗ Homology.map ιY 1 ∘ₗ
    (homologyBasisOfCohomologyBasis bτ).symm.toLinearMap

/-- The boundary inclusion restricted to the τ-end and read through `homτ.symm` IS the given
embedding `ιY`. -/
theorem emptySourceRealizationTied_ι_comp_right :
    ((emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).ι.comp
        (subInclCM ((emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).U)ᶜ)).comp
      ⟨(emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).homτ.symm,
        (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).homτ.symm.continuous⟩
      = ιY :=
  ContinuousMap.ext fun _ => rfl

/-- **THE KERNEL IDENTITY** — the empty-source realization's transported boundary-inclusion is the
single-surface bounding map precomposed with the τ-block projection `x ↦ x ∘ inr`: the σ-block dies
(`Fin nσ` empty ⟹ the σ-coordinates are `0`). -/
theorem emptySourceRealizationTied_transportedBInc [IsEmpty (Fin nσ)] :
    transportedBInc (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData
      = (boundingBInc Sτ bτ QC ιY mid eQ).comp
          (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inr : Fin nτ → Fin nσ ⊕ Fin nτ)) := by
  refine LinearMap.ext fun x => ?_
  show eQ (Homology.map (emptySourceBdryIncl Sσ Sτ QC ιY) 1
      ((srcEquiv (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData).symm x))
    = eQ (Homology.map ιY 1
        ((homologyBasisOfCohomologyBasis bτ).symm (fun i => x (Sum.inr i))))
  refine congrArg eQ ?_
  rw [srcEquiv_symm_apply]
  have hσ0 : homIncl (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData.U 1
      ((emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData.eσ.symm
        (fun i => x (Sum.inl i))) = 0 := by
    haveI : IsEmpty ↑(sub (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData.U) :=
      isEmpty_sub_range_inl
    rw [Subsingleton.elim ((emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData.eσ.symm
      (fun i => x (Sum.inl i))) 0, map_zero]
  rw [map_add, hσ0, map_zero, zero_add]
  -- The τ-end derived-basis inverse is (all `rfl`-lemmas collapsed): the UCT-dual basis inverse
  -- transported by `H₁(homτ.symm)`.
  have he : (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData.eτ.symm
        (fun i => x (Sum.inr i))
      = Homology.map ⟨(emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).homτ.symm,
          (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).homτ.symm.continuous⟩ 1
          ((homologyBasisOfCohomologyBasis bτ).symm (fun i => x (Sum.inr i))) := rfl
  rw [he, homIncl_eq_map, ← LinearMap.comp_apply, ← Homology.map_comp]
  have hmap : (Homology.map ((emptySourceBdryIncl Sσ Sτ QC ιY).comp
        (subInclCM (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData.Uᶜ)) 1) ∘ₗ
      Homology.map ⟨(emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).homτ.symm,
        (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).homτ.symm.continuous⟩ 1
      = Homology.map ιY 1 :=
    (Homology.map_comp _ _ 1).symm.trans
      (congrArg (Homology.map · 1)
        (emptySourceRealizationTied_ι_comp_right Sσ Sτ bσ bτ QC ιY hιY mid eQ))
  exact LinearMap.congr_fun hmap _

/-- **The membrane kernel is the τ-block preimage of the bounding kernel** — the computed
Taylor-leg submodule of the empty-source membrane is exactly the classical bounding kernel of the
τ-surface, pulled back along the τ-block projection. -/
theorem emptySourceRealizationTied_toMembrane_L [IsEmpty (Fin nσ)]
    (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ)) :
    ((emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toMembrane qσ qτ).L
      = Submodule.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inr : Fin nτ → Fin nσ ⊕ Fin nτ))
          (LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ)) := by
  show LinearMap.ker (transportedBInc (emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toData)
    = _
  rw [emptySourceRealizationTied_transportedBInc]
  exact LinearMap.ker_comp _ _

/-! ## §4. The joint-condition dissolve — single-surface conditions suffice. -/

/-- **The Taylor leg dissolves to the single-surface condition**: if `qτ` vanishes on the bounding
kernel of the τ-surface in the membrane, the τ-end-negated joint enhancement vanishes on the whole
computed membrane kernel (the σ-side contributes `q 0 = 0` only). -/
theorem taylorLegVanishes_emptySource [IsEmpty (Fin nσ)]
    (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (hq : ∀ v ∈ LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ), qτ.q v = 0) :
    TaylorLegVanishes qσ qτ
      ((emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toMembrane qσ qτ).L := by
  intro l hl
  rw [emptySourceRealizationTied_toMembrane_L, Submodule.mem_comap] at hl
  have hτ : qτ.q (fun i => l (Sum.inr i)) = 0 := hq _ hl
  show qσ.q (fun i => l (Sum.inl i)) + -(qτ.q (fun i => l (Sum.inr i))) = 0
  rw [Subsingleton.elim (fun i => l (Sum.inl i)) 0, qσ.q_zero, hτ, neg_zero, add_zero]

/-- **The Lagrangian condition dissolves to the single-surface condition**: if the bounding kernel
is `B`-maximal for `qτ` (`K^⊥ ⊆ K`), the computed membrane kernel is jointly Lagrangian (the
σ-side polar contributions vanish: the σ-coordinates of every vector are `0`). -/
theorem jointLagrangian_emptySource [IsEmpty (Fin nσ)]
    (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (hlag : ∀ v, (∀ l ∈ LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ), qτ.B v l = 0)
      → v ∈ LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ)) :
    JointLagrangian qσ qτ
      ((emptySourceRealizationTied Sσ Sτ bσ bτ QC ιY hιY mid eQ).toMembrane qσ qτ).L := by
  intro v hv
  rw [emptySourceRealizationTied_toMembrane_L] at hv ⊢
  rw [Submodule.mem_comap]
  apply hlag
  intro w hw
  have hmem : Sum.elim (0 : Fin nσ → ZMod 2) w ∈
      Submodule.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inr : Fin nτ → Fin nσ ⊕ Fin nτ))
        (LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ)) :=
    Submodule.mem_comap.mpr hw
  have key : qσ.B (fun i => v (Sum.inl i)) 0 + qτ.B (fun i => v (Sum.inr i)) w = 0 :=
    hv (Sum.elim 0 w) hmem
  rw [qσ.B_symm (fun i => v (Sum.inl i)) 0, qσ.B_zero_left, zero_add] at key
  exact key

/-! ## §5. The capstone cascade — the welded membrane row with an empty-Σ source.

The terminal KRS surgery step realised on the CONSTRUCTED capstone: the σ-end (the surgered spin
source's characteristic surface) is EMPTY, so the whole σ-side of the welded membrane row dissolves.
`TraceMembraneLeaves.ofCapstoneWeldedEmptySource` is the empty-source specialisation of
`TraceMembraneLeaves.ofCapstoneWelded`: `real` is the empty-source realization, `htaylor`/`hlag` are
the §4 single-surface dissolves, and `glueσ` is discharged VACUOUSLY (`sub real.U = ∅`). The honest
open residual is purely SINGLE-SURFACE: the membrane space `QC` (the trace's own dim-3 3-manifold),
the closed embedding `ιY : Σ ↪ QC`, its interior basis `eQ`, the two single-surface kernel conditions
`hq`/`hlagK` on the classical bounding kernel `ker (boundingBInc …)`, and the presentation atoms
`HAQ`/`weld`/`hQ`/`glueτ`/`chartQ` — the σ-side atoms (`glueσ`, the σ-half of `real`) are GONE.

Homed here (not in `PinPlusTraceCapstoneMembraneWeld.lean`) because this module already imports it:
`ofCapstoneWeldedEmptySource` consumes `ofCapstoneWelded` UNCHANGED (the untethered-membrane fence —
the weld still supplies the presentation).

**τ-side adjudication (the KRS consumption site).** In `kernelReducesToSpin_of_capstoneWeldedSupply`
the target end is `p` with the binder guard `0 < p.2.n`; per §2, `0 < p.2.n` plus the carried basis
`H¹(Σ) ≃ (Fin p.2.n → ℤ/2)` forces `Σ = p.2.surf ≠ ∅` (the empty surface has trivial `H¹`). So the
τ-end is ALWAYS genuinely non-empty in the KRS lane: the doubly-empty degenerate world never occurs
there, and this SINGLE-surface residual is the correct membrane shape for the terminal step. -/

open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.PinPlusTraceMembranePresented
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneMembraneWeld

/-- **The empty-source membrane realization on a capstone's ends** (σ empty). Encapsulates the
`τ.surfT2` `letI` so the wrapper's `glueτ` residual type and its body share ONE realization term. -/
noncomputable def capstoneEmptySourceReal
    {s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M]
    (QC : TopCat) [T2Space (QC : Type)] [CompactSpace (QC : Type)]
    (ιY : C((τ.surf.M : Type), (QC : Type))) (hιY : IsClosedEmbedding ιY)
    (mid : ℕ) (eQ : Homology QC 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2)) :
    GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis :=
  letI := τ.surfT2
  emptySourceRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis QC ιY hιY mid eQ

/-- **THE EMPTY-SOURCE WELDED MEMBRANE ROW on the constructed capstone** (`#165` §5, the terminal KRS
step). The empty-source specialisation of `TraceMembraneLeaves.ofCapstoneWelded`: with the σ-end
characteristic surface EMPTY (`[IsEmpty σ.surf.M]`, `[IsEmpty (Fin σ.n)]`), the membrane realization
is `capstoneEmptySourceReal` (its σ-block dead), `htaylor`/`hlag` are the §4 single-surface dissolves
from the bounding-kernel conditions `hq`/`hlagK`, and `glueσ` is VACUOUS (`sub real.U` is empty). The
honest residual is single-surface: `QC`/`ιY`/`hιY`/`mid`/`eQ` + `hq`/`hlagK` + `HAQ`/`weld`/`hQ`/
`glueτ`/`chartQ`. Consumes `ofCapstoneWelded` unchanged (untethered-membrane fence). -/
noncomputable def TraceMembraneLeaves.ofCapstoneWeldedEmptySource
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)]
    (QC : TopCat) [T2Space (QC : Type)] [CompactSpace (QC : Type)]
    (ιY : C((τ.surf.M : Type), (QC : Type))) (hιY : IsClosedEmbedding ιY)
    (mid : ℕ) (eQ : Homology QC 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2))
    (hq : ∀ v ∈ LinearMap.ker (boundingBInc (TopCat.of τ.surf.M) τ.basis QC ιY mid eQ), τ.q.q v = 0)
    (hlagK : ∀ v,
      (∀ l ∈ LinearMap.ker (boundingBInc (TopCat.of τ.surf.M) τ.basis QC ιY mid eQ), τ.q.B v l = 0)
        → v ∈ LinearMap.ker (boundingBInc (TopCat.of τ.surf.M) τ.basis QC ιY mid eQ))
    (HAQ : HandleAttachment.{0, 0})
    (weld : HandleAttachment.Weld HAQ (ktHandleAttachment s.M D5 S hS φ hφ hφinj))
    (hQ : ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Q : Type) ≃ₜ HAQ.carrier)
    (glueτ : ∀ x : ↑(sub (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Uᶜ),
        weld.carrierMap (hQ ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).ι
            (subInclCM (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Uᶜ x)))
          = (capstoneB s t S hS φ hφ hφinj cd hseam d).e
              (Sum.inr (τ.emb ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).homτ x))))
    (chartQ : ChartedSpace MembraneModel ↑(capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Q) :
    TraceMembraneLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ :=
  letI := τ.surfT2
  TraceMembraneLeaves.ofCapstoneWelded s t S hS φ hφ hφinj cd hseam d σ τ
    (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ)
    (taylorLegVanishes_emptySource (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis QC ιY hιY
      mid eQ σ.q τ.q hq)
    (jointLagrangian_emptySource (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis QC ιY hιY
      mid eQ σ.q τ.q hlagK)
    HAQ weld hQ
    (fun x => (isEmpty_sub_range_inl.false x).elim)
    glueτ chartQ

end SKEFTHawking.PinPlusCharPairEmptySourceRealization
