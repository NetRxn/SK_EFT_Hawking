import Mathlib

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6a) — the directed poset of compacts in an open

The Poincaré-duality **open-cover induction** (Hatcher 3.36) inducts over opens `W`, with the
compactly-supported cohomology `Hᵏ_c(W) = colim_{K ⊆ W compact} Hᵏ(M | K)` — a filtered colimit over the
**sub-poset of compacts contained in `W`**, `CompactsIn W = {K : Compacts // ↑K ⊆ W}`. This module
establishes that sub-poset as a **directed order** (`IsDirected` via `⊔`, since the union of two compacts
in `W` is a compact in `W`) that is `Nonempty` (`⊥ = ∅ ⊆ W`) — exactly the index structure
`Module.DirectLimit` needs to form `Hᵏ_c(W)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

namespace SKEFTHawking.SingularCompactsInOpen

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- **The compacts contained in an open `W`** — the index sub-poset of the compactly-supported cohomology
`Hᵏ_c(W)`. -/
def CompactsIn (W : Set X) : Type _ := {K : Compacts X // (↑K : Set X) ⊆ W}

noncomputable instance (W : Set X) : PartialOrder (CompactsIn W) :=
  Subtype.partialOrder _

/-- The supremum (union) of two compacts in `W` is again a compact in `W` — the directedness witness. -/
def CompactsIn.sup {W : Set X} (a b : CompactsIn W) : CompactsIn W :=
  ⟨a.1 ⊔ b.1, by rw [Compacts.coe_sup]; exact Set.union_subset a.2 b.2⟩

instance (W : Set X) : IsDirected (CompactsIn W) (· ≤ ·) where
  directed a b := ⟨CompactsIn.sup a b, Subtype.coe_le_coe.mp le_sup_left,
    Subtype.coe_le_coe.mp le_sup_right⟩

instance (W : Set X) : Nonempty (CompactsIn W) :=
  ⟨⟨⊥, by rw [Compacts.coe_bot]; exact Set.empty_subset W⟩⟩

noncomputable instance (W : Set X) : DecidableEq (CompactsIn W) := Classical.decEq _

/-- **Binary split of a compact in a union of opens** (`IsCompact.binary_compact_cover`, packaged for the
`CompactsIn` index): a compact `K ⊆ U ∪ V` (with `U`, `V` open) is the union `↑K_U ∪ ↑K_V` of a compact
`K_U ∈ CompactsIn U` and a compact `K_V ∈ CompactsIn V`. The geometric input of the compactly-supported-
cohomology Mayer–Vietoris middle exactness (the merged colimit-compact splits across the cover). -/
theorem compactsIn_binary_cover [R1Space X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (K : CompactsIn (U ∪ V)) :
    ∃ (KU : CompactsIn U) (KV : CompactsIn V), (↑K.1 : Set X) = ↑KU.1 ∪ ↑KV.1 := by
  obtain ⟨K₁, K₂, hK₁c, hK₂c, hK₁U, hK₂V, hsplit⟩ :=
    K.1.isCompact'.binary_compact_cover hU hV K.2
  exact ⟨⟨⟨K₁, hK₁c⟩, hK₁U⟩, ⟨⟨K₂, hK₂c⟩, hK₂V⟩, hsplit⟩

end SKEFTHawking.SingularCompactsInOpen
