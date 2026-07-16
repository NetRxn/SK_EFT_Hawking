import Mathlib
import SKEFTHawking.PinPlusCylComponentExcisionBridge
import SKEFTHawking.PinPlusCylDataDischargeDisconnectedD

/-!
# Phase 5q.H — CONSUMING THE EXCISION BRIDGE: the two-piece disconnected `D` (route (b) validation)

The excision bridge (`PinPlusCylComponentExcisionBridge.restrictsToRelGenOn_component`) supplies, for a
clopen connected piece, the per-piece detection witness `cylinderRelFundClassDatum_of_clopenSplit`
consumes. This module fires the composition end-to-end for the simplest genuinely-DISCONNECTED base: a
closed charted 4-manifold `M = C ⊔ Cᶜ` split into TWO clopen CONNECTED components. Both per-piece
witnesses come from the bridge (`C` for `U = C ×ˢ univ`, `Cᶜ` for `Uᶜ = (C ×ˢ univ)ᶜ = Cᶜ ×ˢ univ`),
and the binary engine assembles the disconnected relative fundamental-class datum `D` — with NO
homeomorphism-transport of Lefschetz–Wu data, the standing wall.

This validates the route-(b) architecture: the disconnected `D` field IS dischargeable from the
per-component connected classes via the excision bridge. The general `k`-component case needs the
finite relative-⊔ tower (summing the bridge witnesses over `ConnectedComponents M`); the two-piece
case here is the binary base of that tower.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularRelativeDisjointUnionFundClass
open SKEFTHawking.PinPlusCylComponentExcisionBridge
open SKEFTHawking.PinPlusCylDataDischargeDisconnectedD

namespace SKEFTHawking.PinPlusCylComponentExcisionBridgeConsume

noncomputable section

variable {m' : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

omit [T2Space M] [CompactSpace M] in
/-- **The clopen complement of a cylinder piece is the complement piece**: `(C ×ˢ univ)ᶜ = Cᶜ ×ˢ univ`
in `cylW M = M × [0,1]` (the interval factor is `univ`, so the complement is entirely in the base). The
set identity that lets the bridge witness for `Cᶜ` serve as the `Uᶜ`-side witness. -/
theorem compl_cylPiece (C : Set M) :
    ((C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)))ᶜ : Set ↑(TopCat.of (cylW M)))
      = Cᶜ ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := by
  ext p
  simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_compl_iff]

/-- **THE TWO-PIECE DISCONNECTED `D` via the excision bridge.** For a closed charted 4-manifold
`M = C ⊔ Cᶜ` split into two clopen CONNECTED pieces, the disconnected cylinder relative
fundamental-class datum `D` EXISTS — assembled by `cylinderRelFundClassDatum_of_clopenSplit` from the
two bridge witnesses (`restrictsToRelGenOn_component` on `C` and on `Cᶜ`). No homeomorphism-transport
of Lefschetz–Wu data; only per-component connected classes + the clopen-split engine. -/
theorem nonempty_cylinderRelFundClassDatum_of_twoPiece [T1Space (cylW M)]
    (C : Set M) (hC : IsClopen C)
    [Nonempty ↥C] [PreconnectedSpace ↥C] [T1Space (cylW ↥C)]
    [Nonempty ↥(Cᶜ)] [PreconnectedSpace ↥(Cᶜ)] [T1Space (cylW ↥(Cᶜ))] :
    Nonempty (RelFundClassDatum (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M))) := by
  obtain ⟨αU, hdetU⟩ := restrictsToRelGenOn_component (m' := m') C hC
  obtain ⟨αUc, hdetUc⟩ := restrictsToRelGenOn_component (m' := m') (Cᶜ) hC.compl
  -- the `Cᶜ`-bridge witness lands over `Cᶜ ×ˢ univ`; convert it to the engine's `(C ×ˢ univ)ᶜ` form
  -- (`compl_cylPiece`), reverting both `αUc` and `hdetUc` so the rewrite motive is type-correct.
  revert αUc hdetUc
  rw [← compl_cylPiece C]
  intro αUc hdetUc
  exact ⟨cylinderRelFundClassDatum_of_clopenSplit (isClopen_cylPiece hC) αU αUc hdetU hdetUc⟩

end

end SKEFTHawking.PinPlusCylComponentExcisionBridgeConsume
