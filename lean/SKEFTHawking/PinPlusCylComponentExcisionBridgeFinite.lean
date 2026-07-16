import Mathlib
import SKEFTHawking.PinPlusCylComponentExcisionBridge
import SKEFTHawking.SingularRelativeDisjointUnionFundClassFinite
import SKEFTHawking.PinPlusCylDataDischargeDisconnectedD

/-!
# Phase 5q.H — THE k-COMPONENT DISCONNECTED `D` (finite partition over `ConnectedComponents M`)

The two-piece base (`PinPlusCylComponentExcisionBridgeConsume.nonempty_cylinderRelFundClassDatum_of_twoPiece`)
assembled the disconnected cylinder relative fundamental-class datum `D` for a base split into TWO clopen
connected pieces. This module lifts it to the GENERAL possibly-disconnected closed charted manifold `M`,
with NO disconnected-specific posit: `cylW M = ⊔_{c : ConnectedComponents M} (C_c × I)` is a FINITE clopen
partition (compact charted ⟹ finitely many components, each clopen; `C_c := connectedComponent (reps c)`),
each piece is CONNECTED, so its per-piece detection witness is the excision-bridge keystone
`restrictsToRelGenOn_component`, and the finite-partition assembly
(`SingularRelativeDisjointUnionFundClassFinite.hasRelFundClass_of_finite_clopen_partition`) sums the
per-component classes into the disconnected `HasRelFundClass (∂W) cylGen`.

Feeding that into `cylinderRelFundClassDatum` yields the disconnected `D` field
(`cylinderRelFundClassDatum_of_components`) — UNCONDITIONALLY for any closed charted `M`, connected or not,
with NO homeomorphism transport of Lefschetz–Wu data (the standing wall) and NO global
punctured-top-vanishing (each component supplies its own class via the connected engine, restricted to its
OWN preconnected piece — the punctured-top no-go is never touched).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularRelativeDisjointUnionFundClass
open SKEFTHawking.SingularRelativeDisjointUnionFundClassFinite
open SKEFTHawking.PinPlusCylComponentExcisionBridge
open SKEFTHawking.PinPlusCylDataDischargeDisconnectedD

namespace SKEFTHawking.PinPlusCylComponentExcisionBridgeFinite

noncomputable section

variable {M : Type} [TopologicalSpace M]

/-! ## §1. A chosen representative point per connected component. -/

/-- **A chosen representative point per connected component** (a section of `ConnectedComponents.mk`). -/
def reps : ConnectedComponents M → M :=
  Function.surjInv ConnectedComponents.surjective_coe

theorem reps_mk (c : ConnectedComponents M) : ConnectedComponents.mk (reps c) = c :=
  Function.surjInv_eq ConnectedComponents.surjective_coe c

/-! ## §2. The disconnected cylinder `HasRelFundClass` from the component partition. -/

variable {m' : ℕ} [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **The disconnected cylinder relative fundamental class, via the component partition.** For a general
possibly-disconnected closed charted manifold `M`, the interior generator family `cylGen` has a relative
fundamental class: `cylW M = ⊔_c (C_c × I)` is a finite clopen partition into CONNECTED pieces, each piece
supplies its detection witness through the excision bridge `restrictsToRelGenOn_component`, and the
finite-partition assembly sums them. NO homeomorphism transport, NO global punctured-top-vanishing (each
witness is built from the connected engine on its own preconnected component). -/
theorem hasRelFundClass_cylGen_components [T1Space (cylW M)] :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M
  haveI : Finite (ConnectedComponents M) := inferInstance
  haveI : Fintype (ConnectedComponents M) := Fintype.ofFinite _
  -- the clopen connected-component pieces of the base
  set C : ConnectedComponents M → Set M := fun c => connectedComponent (reps c) with hC
  have hCclopen : ∀ c, IsClopen (C c) := fun c =>
    ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
  -- the ambient cylinder pieces `U c = C c ×ˢ univ`
  set U : ConnectedComponents M → Set ↑(TopCat.of (cylW M)) :=
    fun c => (C c ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1))) with hU
  -- per-component detection witnesses via the excision bridge (each `C c` is connected + nonempty)
  have hwit : ∀ c, ∃ αU : RelativeHomology
      (restr (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) (U c)) (m' + 1 + 2),
      RestrictsToRelGenOn (X := TopCat.of (cylW M)) (m := m' + 1)
        ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m')) (· ∈ U c)
        (excisionMap (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
          (U c) (m' + 1 + 2) αU) := by
    intro c
    haveI : Nonempty ↥(C c) := ⟨⟨reps c, mem_connectedComponent⟩⟩
    haveI : PreconnectedSpace ↥(C c) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
    haveI : T1Space (cylW ↥(C c)) := inferInstance
    exact restrictsToRelGenOn_component (m' := m') (C c) (hCclopen c)
  choose αU hαU using hwit
  -- assemble via the finite clopen partition
  refine hasRelFundClass_of_finite_clopen_partition (m := m' + 1) U
    (fun c => (hCclopen c).prod isClopen_univ) ?_ ?_ ((cylModel m').boundary (cylW M))
    (cylGen (M := M) (m' := m')) αU hαU
  · -- pairwise disjoint: distinct components are disjoint, lifted to the products
    intro c c' hcc'
    have hbase : Disjoint (C c) (C c') := by
      apply connectedComponent_disjoint
      intro heq
      exact hcc' (by rw [← reps_mk c, ← reps_mk c', ConnectedComponents.coe_eq_coe]; exact heq)
    rw [Set.disjoint_left]
    rintro p hp hp'
    exact (Set.disjoint_left.mp hbase) hp.1 hp'.1
  · -- cover: every point of `cylW M` lies in the piece of its base component
    intro p
    refine ⟨ConnectedComponents.mk p.1, ?_, Set.mem_univ _⟩
    show p.1 ∈ connectedComponent (reps (ConnectedComponents.mk p.1))
    have : connectedComponent (reps (ConnectedComponents.mk p.1)) = connectedComponent p.1 :=
      ConnectedComponents.coe_eq_coe.mp (by rw [reps_mk])
    rw [this]; exact mem_connectedComponent

/-! ## §3. The disconnected `D` field. -/

/-- **THE k-COMPONENT DISCONNECTED `D`.** The cylinder relative fundamental-class datum `D` for a general
possibly-disconnected closed charted manifold `M`, assembled by `cylinderRelFundClassDatum` from the
component-partition class `hasRelFundClass_cylGen_components`. This is the disconnected `D` field with NO
disconnected-specific posit — the connected components ARE the atoms, each supplied by the excision bridge.
No homeomorphism transport; no global punctured-top-vanishing. -/
def cylinderRelFundClassDatum_of_components [T1Space (cylW M)] :
    RelFundClassDatum (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) :=
  cylinderRelFundClassDatum (hasRelFundClass_cylGen_components (m' := m') (M := M))

end

end SKEFTHawking.PinPlusCylComponentExcisionBridgeFinite
