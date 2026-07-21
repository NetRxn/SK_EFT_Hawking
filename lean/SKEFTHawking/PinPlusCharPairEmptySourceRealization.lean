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

/-! ## §6. The single-surface bounding-kernel metabolic bridge and the packaged τ-side membrane row
(`#183`, the τ-side single-surface membrane front — the KRS supply's last non-Fable-gated row).

The wrapper `TraceMembraneLeaves.ofCapstoneWeldedEmptySource` (§5) exposes the honest τ-side residual
AS its parameter list: the membrane space `QC`, the closed embedding `ιY : Σ ↪ QC`, the interior
basis `mid`/`eQ`, the two single-surface bounding-kernel conditions `hq`/`hlagK`, and the welded
plumbing `HAQ`/`weld`/`hQ`/`glueτ`/`chartQ`. For an ARBITRARY nonempty target surface `Σ = τ.surf.M`
(the terminal KRS step's target carries `0 < τ.n`, so `Σ` has nontrivial `H¹` and is NEVER a sphere:
the concrete bounding 3-manifold `Q` is the twice-deferred `real`-membrane's territory — no Mathlib
smooth bordism theory), so the honest form is the per-`p` PACKAGED membrane datum (§6.2), constructed
data the capstone's builder supplies, mirroring the `SurgeredEndDatum`/`SeamCollarDatum` pattern.

Dimension discipline: `QC` is 3-dim (`MembraneModel`-charted, `Σ×[0,½]∪handle∪∅` degenerating to a
single-surface bounding membrane); `τ.surf.M = Σ` is 2-dim; the capstone `W` is 5-dim; `HAQ` is the
dim-3 attachment `Q = B ⊔_φ Ha` one dimension down from the dim-5 `W`. -/

/-- **THE SINGLE-SURFACE BOUNDING-KERNEL METABOLIC BRIDGE** (`#183` §6.1). The two single-surface
conditions the empty-source wrapper consumes — `qτ` vanishes on the bounding kernel
`ker (boundingBInc …)` (`hq`), and that kernel is `B`-maximal (`hlagK`) — say exactly that the
classical bounding kernel is a metabolic Lagrangian for the SINGLE form `qτ`, hence `qτ.brown = 0`.
The honest "the characteristic surface bounds in `Q` ⟹ its Brown invariant vanishes" content (Taylor
`0802.0111` Lem 1.3, the algebra half), read off the terminal KRS step's membrane. This is what makes
the `hq`/`hlagK` fields of the packaged datum GENUINE (anti-vacuity): they cost the builder a
falsifiable grade-zero certificate — the `ℝP²` form (`brown = ±1`) admits no such bounding kernel. -/
theorem boundingBInc_metabolic_brown_zero {nτ mid : ℕ} (Sτ : TopCat)
    (bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (QC : TopCat) (ιY : C((Sτ : Type), (QC : Type)))
    (eQ : Homology QC 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2))
    (qτ : Z4Quadratic (Fin nτ))
    (hq : ∀ v ∈ LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ), qτ.q v = 0)
    (hlagK : ∀ v, (∀ l ∈ LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ), qτ.B v l = 0)
      → v ∈ LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ)) :
    qτ.brown = 0 := by
  haveI : Fintype (LinearMap.ker (boundingBInc Sτ bτ QC ιY mid eQ)) := Fintype.ofFinite _
  exact qτ.brown_eq_zero_of_metabolic _ hq hlagK

/-- **The empty-index enhancement has vanishing Brown invariant** (`#183` §6.1b). When the σ-index
`Fin σ.n` is empty (the terminal KRS step: the surgered spin source has no characteristic classes),
the whole space `Fin n → ℤ/2` is a subsingleton, hence a metabolic Lagrangian (`⊤`), so
`q.brown = 0`. The algebraic shadow of "the empty source is null-bordant". -/
theorem brown_zero_of_isEmpty {n : ℕ} [IsEmpty (Fin n)] (q : Z4Quadratic (Fin n)) :
    q.brown = 0 := by
  haveI : Fintype (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) := Fintype.ofFinite _
  refine q.brown_eq_zero_of_metabolic ⊤ (fun l _ => ?_) (fun v _ => Submodule.mem_top)
  rw [Subsingleton.elim l 0, q.q_zero]

/-- **THE PACKAGED τ-SIDE SINGLE-SURFACE MEMBRANE DATUM** (`#183` §6.2). The per-`p` constructed-data
package the terminal-step capstone's builder supplies for the τ-end of the empty-source membrane row —
mirroring the `SurgeredEndDatum`/`SeamCollarDatum` packaging pattern (constructed data, not a proof
obligation). It bundles EXACTLY the honest τ-side residual the wrapper `ofCapstoneWeldedEmptySource`
consumes: the membrane space `QC` (with its own T2/compact certificates), the closed embedding
`ιY : Σ ↪ QC`, the interior basis `mid`/`eQ`, the two single-surface bounding-kernel conditions
`hq`/`hlagK` (the geometric heart — §6.1 shows they cost a genuine grade-zero certificate), and the
welded dim-3 plumbing `HAQ`/`weld`/`hQ`/`glueτ`/`chartQ`. Every field is a genuine geometric atom;
none self-discharges. The σ-side atoms are GONE (the source Σ is empty). -/
structure TauMembraneWeldDatum
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)] where
  /-- **the concrete membrane space** `Q` (dim-3, `MembraneModel`-charted): the 3-manifold the target
  characteristic surface `Σ = τ.surf.M` bounds through the trace. -/
  QC : TopCat
  /-- **per-object certificate**: `Q` is Hausdorff. -/
  QT2 : T2Space QC
  /-- **per-object certificate**: `Q` is compact. -/
  QCompact : CompactSpace QC
  /-- **the closed embedding** `Σ ↪ Q` of the target surface into the membrane. -/
  ιY : C((τ.surf.M : Type), (QC : Type))
  /-- `ιY` is a closed embedding (`open Topology`). -/
  hιY : IsClosedEmbedding ιY
  /-- `mid = dim H₁(Q;ℤ/2)`. -/
  mid : ℕ
  /-- `H₁(Q)` interior basis (the free interior gauge — kernel-invariant). -/
  eQ : Homology QC 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2)
  /-- **(bounding kernel — the geometric heart)** `qτ` vanishes on the classical bounding kernel
  `ker (boundingBInc …)` — "Σ bounds a Lagrangian in Q". Costs a genuine grade-zero certificate
  (§6.1 `boundingBInc_metabolic_brown_zero`). -/
  hq : ∀ v ∈ LinearMap.ker (boundingBInc (TopCat.of τ.surf.M) τ.basis QC ιY mid eQ), τ.q.q v = 0
  /-- **(bounding kernel — the geometric heart)** the bounding kernel is `B`-maximal (`K^⊥ ⊆ K`). -/
  hlagK : ∀ v,
    (∀ l ∈ LinearMap.ker (boundingBInc (TopCat.of τ.surf.M) τ.basis QC ιY mid eQ), τ.q.B v l = 0)
      → v ∈ LinearMap.ker (boundingBInc (TopCat.of τ.surf.M) τ.basis QC ιY mid eQ)
  /-- **the membrane's dim-3 handle attachment** `Q = B ⊔_φ Ha` (one dimension down from the dim-5
  capstone carrier `W`). -/
  HAQ : HandleAttachment.{0, 0}
  /-- **the membrane weld** `Q ↪ W` into the FIXED capstone carrier `ktHandleAttachment …`. -/
  weld : HandleAttachment.Weld HAQ (ktHandleAttachment s.M D5 S hS φ hφ hφinj)
  /-- `Q` presented as `HAQ.carrier`. -/
  hQ : letI := QT2; letI := QCompact
    ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Q : Type) ≃ₜ HAQ.carrier
  /-- **glue (τ-end)**: the welded membrane boundary factors through `(capstoneB …).e ∘ Sum.inr ∘
  τ.emb` (in the `hW`-collapsed welded form). -/
  glueτ : letI := QT2; letI := QCompact
    ∀ x : ↑(sub (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Uᶜ),
      weld.carrierMap (hQ ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).ι
          (subInclCM (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Uᶜ x)))
        = (capstoneB s t S hS φ hφ hφinj cd hseam d).e
            (Sum.inr (τ.emb ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).homτ x)))
  /-- **manifold discipline**: `Q` charts over the dim-3 membrane model. -/
  chartQ : letI := QT2; letI := QCompact
    ChartedSpace MembraneModel ↑(capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Q

/-- **THE PACKAGED-DATUM BUILDER** (`#183` §6.3). The τ-side membrane datum discharges the empty-source
welded membrane row: its bundled fields feed `TraceMembraneLeaves.ofCapstoneWeldedEmptySource` verbatim.
With this, the membrane atoms of the KRS supply are COMPLETE modulo the per-`p` datum `D` — every
wrapper parameter is read off `D`, and the σ-side atoms are already gone (empty source). -/
noncomputable def TraceMembraneLeaves.ofTauMembraneWeldDatum
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)]
    (D : TauMembraneWeldDatum s t S hS φ hφ hφinj cd hseam d σ τ) :
    TraceMembraneLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ :=
  letI := D.QT2
  letI := D.QCompact
  TraceMembraneLeaves.ofCapstoneWeldedEmptySource s t S hS φ hφ hφinj cd hseam d σ τ
    D.QC D.ιY D.hιY D.mid D.eQ D.hq D.hlagK D.HAQ D.weld D.hQ D.glueτ D.chartQ

/-- **The packaged datum forces the terminal-step target grade to vanish** (`#183` §6.4). The datum's
bounding-kernel fields `hq`/`hlagK` force `τ.q.brown = 0` (§6.1) — the falsifiable physics payload of
the terminal KRS step: the empty (null) source forces the target's Brown/ABK grade to zero. Confirms
the datum's geometric-heart fields are genuinely load-bearing (anti-vacuity discipline). -/
theorem TauMembraneWeldDatum.brown_zero
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)]
    (D : TauMembraneWeldDatum s t S hS φ hφ hφinj cd hseam d σ τ) :
    τ.q.brown = 0 :=
  boundingBInc_metabolic_brown_zero (TopCat.of τ.surf.M) τ.basis D.QC D.ιY D.eQ τ.q D.hq D.hlagK

/-- **The packaged datum witnesses Brown-preservation across the terminal KRS step** (`#183` §6.5).
Both ends have vanishing Brown grade: the empty source `σ` by §6.1b (empty index), the target `τ` by
§6.4 (the bounding-kernel fields). So `σ.q.brown = τ.q.brown` — the KT surgery's mod-8 Brown/ABK
invariance, delivered by the SINGLE-surface membrane datum directly, independent of the full tethered
assembly and of the `Quot.sound` class-equality route. -/
theorem TauMembraneWeldDatum.brown_preserved
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)]
    (D : TauMembraneWeldDatum s t S hS φ hφ hφinj cd hseam d σ τ) :
    σ.q.brown = τ.q.brown :=
  (brown_zero_of_isEmpty σ.q).trans
    (TauMembraneWeldDatum.brown_zero s t S hS φ hφ hφinj cd hseam d σ τ D).symm

/-! ### The rank-zero specialization (hcolD brick B4)

For a **rank-zero** target `τ` (`Fin τ.n` empty — the hcolD collapse sector, where the carried
surface has trivial enhancement `H¹`), the two "geometric heart" bounding-kernel fields `hq`/`hlagK`
of `TauMembraneWeldDatum` discharge for free: the enhancement space `Fin τ.n → ℤ/2` is a
subsingleton, so every vector is `0`, `q(0) = 0`, and `0` lies in every kernel. The HONEST residual
of the rank-zero membrane row is therefore exactly the GEOMETRIC field list — the membrane `Q`
genuinely bounding `Σ_τ` with its weld into the capstone carrier — which is what hcolD brick B1
(`RankZeroSurfaceBoundingDatum`) must construct. This constructor makes that split precise. -/

/-- **The rank-zero τ-side membrane datum — geometric fields only (hcolD B4).** When the target's
enhancement is rank-zero, `TauMembraneWeldDatum`'s bounding-kernel fields are subsingleton-trivial,
so the datum is determined by its geometric content: the compact membrane `Q`, the closed embedding
`Σ_τ ↪ Q`, the interior `H₁` basis, and the dim-3 weld plumbing into the fixed capstone carrier.
The algebraic self-discharge here is honest (rank-zero means there is literally no enhancement to
obstruct); the geometric fields remain genuinely load-bearing and are the B1 construction target. -/
noncomputable def TauMembraneWeldDatum.ofRankZero
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)]
    (QC : TopCat) (QT2 : T2Space QC) (QCompact : CompactSpace QC)
    (ιY : C((τ.surf.M : Type), (QC : Type))) (hιY : IsClosedEmbedding ιY)
    (mid : ℕ) (eQ : Homology QC 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2))
    (HAQ : HandleAttachment.{0, 0})
    (weld : HandleAttachment.Weld HAQ (ktHandleAttachment s.M D5 S hS φ hφ hφinj))
    (hQ : letI := QT2; letI := QCompact
      ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Q : Type) ≃ₜ HAQ.carrier)
    (glueτ : letI := QT2; letI := QCompact
      ∀ x : ↑(sub (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Uᶜ),
        weld.carrierMap (hQ ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).ι
            (subInclCM (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Uᶜ x)))
          = (capstoneB s t S hS φ hφ hφinj cd hseam d).e
              (Sum.inr (τ.emb ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).homτ x))))
    (chartQ : letI := QT2; letI := QCompact
      ChartedSpace MembraneModel ↑(capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Q) :
    TauMembraneWeldDatum s t S hS φ hφ hφinj cd hseam d σ τ where
  QC := QC
  QT2 := QT2
  QCompact := QCompact
  ιY := ιY
  hιY := hιY
  mid := mid
  eQ := eQ
  hq := fun v _ => by rw [Subsingleton.elim v 0, τ.q.q_zero]
  hlagK := fun v _ => by
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  HAQ := HAQ
  weld := weld
  hQ := hQ
  glueτ := glueτ
  chartQ := chartQ

/-- **The rank-zero membrane row, end to end (hcolD B4 consumer form)**: geometric fields in,
`TraceMembraneLeaves` out — the composite `ofTauMembraneWeldDatum ∘ ofRankZero` the B5/B6 assembly
consumes. Once B1 supplies the geometric fields for a rank-zero `p`, the membrane atoms of its
collapse row are complete. -/
noncomputable def TraceMembraneLeaves.ofRankZeroTauMembrane
    (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)]
    (QC : TopCat) (QT2 : T2Space QC) (QCompact : CompactSpace QC)
    (ιY : C((τ.surf.M : Type), (QC : Type))) (hιY : IsClosedEmbedding ιY)
    (mid : ℕ) (eQ : Homology QC 1 ≃ₗ[ZMod 2] (Fin mid → ZMod 2))
    (HAQ : HandleAttachment.{0, 0})
    (weld : HandleAttachment.Weld HAQ (ktHandleAttachment s.M D5 S hS φ hφ hφinj))
    (hQ : letI := QT2; letI := QCompact
      ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Q : Type) ≃ₜ HAQ.carrier)
    (glueτ : letI := QT2; letI := QCompact
      ∀ x : ↑(sub (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Uᶜ),
        weld.carrierMap (hQ ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).ι
            (subInclCM (capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Uᶜ x)))
          = (capstoneB s t S hS φ hφ hφinj cd hseam d).e
              (Sum.inr (τ.emb ((capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).homτ x))))
    (chartQ : letI := QT2; letI := QCompact
      ChartedSpace MembraneModel ↑(capstoneEmptySourceReal σ τ QC ιY hιY mid eQ).Q) :
    TraceMembraneLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ :=
  TraceMembraneLeaves.ofTauMembraneWeldDatum s t S hS φ hφ hφinj cd hseam d σ τ
    (TauMembraneWeldDatum.ofRankZero s t S hS φ hφ hφinj cd hseam d σ τ
      QC QT2 QCompact ιY hιY mid eQ HAQ weld hQ glueτ chartQ)

/-- **Rank-zero Brown preservation is hypothesis-free**: for a rank-zero target the terminal-step
Brown/ABK invariance `σ.q.brown = τ.q.brown` needs NO membrane datum at all — both enhancement
spaces are empty-indexed, so both grades vanish (`brown_zero_of_isEmpty` twice). Records that in
the collapse sector the mod-8 grade carries no obstruction; the load is entirely geometric. -/
theorem rankZero_brown_preserved
    {s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)] :
    σ.q.brown = τ.q.brown :=
  (brown_zero_of_isEmpty σ.q).trans (brown_zero_of_isEmpty τ.q).symm

end SKEFTHawking.PinPlusCharPairEmptySourceRealization
