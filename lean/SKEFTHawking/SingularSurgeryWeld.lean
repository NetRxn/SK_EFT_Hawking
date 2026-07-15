/-
# Phase 5q.H W-D — SURGERY WAVE 4, KEYSTONE: the handle-attachment weld
# (the membrane-into-carrier tether, "the same two-region weld ONE level down")

Companion to `SingularSurgeryFoundation.lean` (the opener, which shipped the surgery-trace carrier
`HandleAttachment.carrier = B ⊔_φ Ha` with its compact-Hausdorff instance stack and the two
closed-embedded ends). This module builds the **weld keystone**: a morphism of `HandleAttachment`
data — region maps `fB : B ⇒ B'`, `fHa : Ha ⇒ Ha'` respecting the attaching data — induces a
**closed embedding of carriers** `Q = B ⊔_φ Ha  ↪  W = B' ⊔_{φ'} Ha'`.

This is precisely the tangential-enrichment weld both Surgery-Wave-4 consumers bottom out in: the
surgery-trace MEMBRANE `Q = Σ×[0,½] ∪ handle ∪ Σ'×[½,1]` (a dim-3 handle attachment) rides INSIDE
the surgery-trace BORDISM `W = M × I` (a dim-5 handle attachment) via the same pushout weld one
dimension down — the cylinder part `Σ×[0,1]` maps into `B = M×I` by `emb × id`, the handle part maps
into the ambient handle, and the two agree on the attaching seam. The keystone proves that this weld
is a closed embedding purely from: `fB`, `fHa` closed (injective) region maps + attaching-data
compatibility (`hSmap`/`hφ`) + attaching-region exactness (`hSreflect`). Q compact + W Hausdorff
(both from the opener's instance stack) upgrade continuous-injective to closed-embedding for free.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryFoundation

namespace SKEFTHawking.SurgeryFoundation

open Topology

namespace HandleAttachment

/-! ## §1. The weld datum — a morphism of handle attachments. -/

/-- **A weld of one handle attachment into another.** Region maps `fB : Q.B ⇒ W.B`,
`fHa : Q.Ha ⇒ W.Ha` (each an injective continuous map — a topological embedding of the corresponding
end) that respect the attaching data:

* `hSmap` — the region map `fHa` carries `Q`'s attaching region `S` into `W`'s attaching region `S'`;
* `hSreflect` — and reflects it exactly (`fHa a ∈ S' → a ∈ S`), so the weld does not spuriously glue
  interior handle points to the seam;
* `hφ` — the attaching maps commute: `φ'(fHa a) = fB (φ a)` on the seam.

From this the induced map on carriers `Q.carrier ↪ W.carrier` is a closed embedding. This is the
membrane-into-bordism tether, one dimension down: `fB = emb × id` (the cylinder membrane into `M×I`),
`fHa` the handle-of-handle map. -/
structure Weld (HAQ HAW : HandleAttachment) where
  /-- the cylinder-end region map `Q.B → W.B` (`= σ.emb × id`). -/
  fB : C(HAQ.B, HAW.B)
  /-- the handle-end region map `Q.Ha → W.Ha`. -/
  fHa : C(HAQ.Ha, HAW.Ha)
  /-- the cylinder-end map is injective (a topological embedding). -/
  fB_inj : Function.Injective fB
  /-- the handle-end map is injective. -/
  fHa_inj : Function.Injective fHa
  /-- `fHa` carries the attaching region into the ambient one. -/
  hSmap : ∀ a ∈ HAQ.S, fHa a ∈ HAW.S
  /-- `fHa` reflects the attaching region exactly — no spurious seam gluing. -/
  hSreflect : ∀ a : HAQ.Ha, fHa a ∈ HAW.S → a ∈ HAQ.S
  /-- the attaching maps commute on the seam: `φ'(fHa a) = fB (φ a)`. -/
  hφ : ∀ a : ↥HAQ.S, HAW.φ ⟨fHa (a : HAQ.Ha), hSmap (a : HAQ.Ha) a.2⟩ = fB (HAQ.φ a)

variable {HAQ HAW : HandleAttachment} (w : Weld HAQ HAW)

/-- The underlying `⊕`-map `Q.B ⊕ Q.Ha → W.B ⊕ W.Ha`. -/
def Weld.sumMap : (HAQ.B ⊕ HAQ.Ha) → (HAW.B ⊕ HAW.Ha) := Sum.map w.fB w.fHa

/-! ## §2. The weld respects and reflects the adjunction relation. -/

/-- **The `⊕`-map RESPECTS the adjunction relation** — glued seam points stay glued (`hφ`), so it
descends to the carriers. -/
theorem Weld.sumMap_respects {x y : HAQ.B ⊕ HAQ.Ha} (h : adjRel HAQ.φ x y) :
    adjRel HAW.φ (w.sumMap x) (w.sumMap y) := by
  cases x <;> cases y <;> simp only [Weld.sumMap, Sum.map_inl, Sum.map_inr, adjRel] at h ⊢
  · exact congrArg w.fB h
  · obtain ⟨ha, e⟩ := h; exact ⟨w.hSmap _ ha, (w.hφ ⟨_, ha⟩).trans (congrArg w.fB e)⟩
  · obtain ⟨ha, e⟩ := h; exact ⟨w.hSmap _ ha, (w.hφ ⟨_, ha⟩).trans (congrArg w.fB e)⟩
  · exact congrArg w.fHa h

/-- **The `⊕`-map REFLECTS the adjunction relation** — its images are glued only where the sources
were (uses `fB`/`fHa` injectivity + attaching-region exactness `hSreflect`). This is what forces the
induced carrier map to be injective. -/
theorem Weld.sumMap_reflects {x y : HAQ.B ⊕ HAQ.Ha}
    (h : adjRel HAW.φ (w.sumMap x) (w.sumMap y)) : adjRel HAQ.φ x y := by
  cases x <;> cases y <;> simp only [Weld.sumMap, Sum.map_inl, Sum.map_inr, adjRel] at h ⊢
  · exact w.fB_inj h
  · obtain ⟨h', e⟩ := h
    have ha := w.hSreflect _ h'
    exact ⟨ha, w.fB_inj ((w.hφ ⟨_, ha⟩).symm.trans e)⟩
  · obtain ⟨h', e⟩ := h
    have ha := w.hSreflect _ h'
    exact ⟨ha, w.fB_inj ((w.hφ ⟨_, ha⟩).symm.trans e)⟩
  · exact w.fHa_inj h

/-! ## §3. The induced carrier map — a closed embedding. -/

/-- **The induced map on carriers** `Q.carrier → W.carrier`, welding the membrane into the bordism
carrier. Descends the `⊕`-map through the two adjunction quotients (`sumMap_respects`). -/
noncomputable def Weld.carrierMap : C(HAQ.carrier, HAW.carrier) where
  toFun := Quotient.lift (fun x => (Quotient.mk (adjSetoid HAW.hφinj) (w.sumMap x)))
    (fun _ _ hab => Quotient.sound (w.sumMap_respects hab))
  continuous_toFun :=
    continuous_quot_lift _ (continuous_quotient_mk'.comp (w.fB.continuous.sumMap w.fHa.continuous))

/-- The weld sends cylinder points to cylinder points via `fB`. -/
@[simp] theorem Weld.carrierMap_fromCyl (b : HAQ.B) :
    w.carrierMap (HAQ.fromCyl b) = HAW.fromCyl (w.fB b) := rfl

/-- The weld sends handle points to handle points via `fHa`. -/
@[simp] theorem Weld.carrierMap_fromHandle (a : HAQ.Ha) :
    w.carrierMap (HAQ.fromHandle a) = HAW.fromHandle (w.fHa a) := rfl

/-- **The weld is injective** (`sumMap_reflects` + `Quotient.eq`). -/
theorem Weld.carrierMap_injective : Function.Injective w.carrierMap := by
  intro x y hxy
  induction x using Quotient.ind with | _ a =>
  induction y using Quotient.ind with | _ b =>
  exact Quotient.sound (w.sumMap_reflects (Quotient.exact hxy))

/-- **THE KEYSTONE — the membrane weld is a closed embedding.** `Q.carrier` is compact and
`W.carrier` is Hausdorff (both from the opener's instance stack), so the continuous injection
`carrierMap` is automatically a closed embedding: the surgery-trace membrane sits inside the
surgery-trace bordism as a genuine closed subspace, welded region-by-region. -/
theorem Weld.isClosedEmbedding_carrierMap : IsClosedEmbedding w.carrierMap :=
  w.carrierMap.continuous.isClosedEmbedding w.carrierMap_injective

end HandleAttachment

end SKEFTHawking.SurgeryFoundation
