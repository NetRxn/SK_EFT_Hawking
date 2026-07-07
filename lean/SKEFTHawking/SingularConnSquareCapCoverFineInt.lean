/-
# Phase 5q.H (E1 CSC-PD tower) — cover-totality of `{val⁻¹U, val⁻¹V}` on `sub(U∪V)` (integral, hmatch prep)

The cover-totality helpers for the integral connecting-square seam-match `hmatch` (brick 6b), completing the
deferred part-2 tools of `SingularConnSquareLHSSubdivInt`. The cover `{val⁻¹U, val⁻¹V}` of `sub (U ∪ V)` is
total (union = univ), so every chain of `sub (U ∪ V)` is subordinate to it — the `exists_iterate_mvUnionInt`
precondition for cover-fine subdividing the cap cycle `cap g z_K`.

⚠ NOTE (empirically confirmed 2026-07-07, matching the mod-2 §Residual of `SingularConnSquareLHSExplicit`):
the `exists_iterate_mvUnionInt`-APPLICATION statement `∃ m, Sdᵐ c ∈ mvUnionChainsInt (val⁻¹U) (val⁻¹V) n`
canNOT be elaborated as a STANDALONE lemma — the elaborator's `isDefEq`/`whnf` descent through the two
stacked `sub` subtypes (`sub (val⁻¹U)` over `sub (U ∪ V)` with the concrete `Subtype.val ⁻¹'` cover) exceeds
200 000 heartbeats. The cover-fine subdivision + partition MUST be assembled at the CONSUMER site (brick 6b),
where the concrete preimage cover instantiates lazily as a unification variable. These two membership helpers
(no `mvUnionChains` conclusion) elaborate fine.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeMVInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIsoInt (mem_subspaceChainsInt_of_support)

namespace SKEFTHawking.SingularConnSquareCapCoverFineInt

variable {X : TopCat}

/-- `val⁻¹U ∪ val⁻¹V = univ` in `sub (U ∪ V)`: every point of the subspace lies in `U` or `V`. -/
theorem preimage_union_eq_univ_subInt (U V : Set ↑X) :
    (Subtype.val ⁻¹' U ∪ Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro p
  rcases p.2 with hp | hp
  · exact Or.inl hp
  · exact Or.inr hp

/-- **Every chain of `sub (U ∪ V)` is subordinate to the cover `{val⁻¹U, val⁻¹V}`** (their union is `univ`
in the subspace, so `subspaceChainsInt = ⊤`). The `exists_iterate_mvUnionInt` precondition (fed lazily at
the consumer to avoid the whnf wall). -/
theorem mem_subspaceChains_preimage_unionInt (U V : Set ↑X) (n : ℕ)
    (r : SingularChainInt (sub (U ∪ V)) n) :
    r ∈ subspaceChainsInt
        (Subtype.val ⁻¹' U ∪ Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) n := by
  rw [preimage_union_eq_univ_subInt]
  exact mem_subspaceChainsInt_of_support (fun _ _ => Set.subset_univ _)

end SKEFTHawking.SingularConnSquareCapCoverFineInt
