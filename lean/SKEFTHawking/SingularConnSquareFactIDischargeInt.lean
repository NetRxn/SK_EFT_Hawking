/-
# Phase 5q.H (E1 CSC-PD tower) — Route B, the fact-(i) stage-1 + discharge (integral)

The fact-(i) assembly layer: the three `fact_i_stage1` sub-bricks → `fact_i_stage1Int` → `fact_i_dischargeInt`.
NOTE (architectural, recorded): the mod-2 `cap_induced_partition_of_split`/`legW_iterate_cap_class_eq` are
built on `SingularSubspaceChainsEquiv.subspaceChainsEquiv` + `mk_eq_of_mem_boundaries`, which have NO ℤ
analog by design — the ℤ substrate replaces them with the committed descent bridge
`SingularHomologyDescentBridgeInt.homology_eq_of_ambient_boundaryInt` (the honest-`−` homology realizer) +
`chainIncl_mem_subspaceChainsInt_iff`. So those two bricks are ℤ-realizer RE-derivations, not verbatim ports
(no missing primitives).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareFactIInt
import SKEFTHawking.SingularSubdivisionInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularRelativeMVInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularSubdivisionInt (singularSdInt)
open SKEFTHawking.SingularExcisionIsoInt (singularSdInt_iterate_mem_subspaceChainsInt)
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- **Ambient THREE-set cover-fine split** (integral). ℤ port of the mod-2
`SingularConnSquareCloseNC.exists_iterate_three_set_split_amb`. Char-2-free: Brick E applied twice over
committed `exists_iterate_cover_split_ambInt`, no sign content. -/
theorem exists_iterate_three_set_split_ambInt {U V LU LV : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V) (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ)
    (hLU : LU ⊆ U) (hLV : LV ⊆ V) {n : ℕ}
    (f : SingularChainInt X n) (hf : f ∈ subspaceChainsInt (U ∪ V) n) :
    ∃ (μ : ℕ) (f₁ f₂ f₃ : SingularChainInt X n),
      f₁ ∈ subspaceChainsInt (U ∩ LVᶜ) n ∧ f₂ ∈ subspaceChainsInt (V ∩ LUᶜ) n
      ∧ f₃ ∈ subspaceChainsInt (U ∩ V) n
      ∧ (⇑(singularSdInt X n))^[μ] f = f₁ + f₂ + f₃ := by
  have hcov : U ∪ V ⊆ (U ∩ LVᶜ) ∪ ((V ∩ LUᶜ) ∪ (U ∩ V)) := by
    rintro x (hxU | hxV)
    · by_cases hxV : x ∈ V
      · exact Or.inr (Or.inr ⟨hxU, hxV⟩)
      · exact Or.inl ⟨hxU, fun hLVx => hxV (hLV hLVx)⟩
    · by_cases hxU : x ∈ U
      · exact Or.inr (Or.inr ⟨hxU, hxV⟩)
      · exact Or.inr (Or.inl ⟨hxV, fun hLUx => hxU (hLU hLUx)⟩)
  obtain ⟨μ₁, f₁', rest, hf₁', hrest, hsplit₁⟩ :=
    exists_iterate_cover_split_ambInt (hU.inter hLVc) ((hV.inter hLUc).union (hU.inter hV)) f
      (subspaceChainsInt_mono hcov n hf)
  obtain ⟨μ₂, f₂, f₃, hf₂, hf₃, hsplit₂⟩ :=
    exists_iterate_cover_split_ambInt (hV.inter hLUc) (hU.inter hV) rest hrest
  have hadd : ∀ (k : ℕ) (a b : SingularChainInt X n),
      (⇑(singularSdInt X n))^[k] (a + b)
        = (⇑(singularSdInt X n))^[k] a + (⇑(singularSdInt X n))^[k] b := by
    intro k
    induction k with
    | zero => intro a b; rfl
    | succ k ih => intro a b; simp only [Function.iterate_succ_apply, map_add, ih]
  refine ⟨μ₂ + μ₁, (⇑(singularSdInt X n))^[μ₂] f₁', f₂, f₃,
    singularSdInt_iterate_mem_subspaceChainsInt hf₁' μ₂, hf₂, hf₃, ?_⟩
  rw [Function.iterate_add_apply, hsplit₁, hadd, hsplit₂, add_assoc]

end SKEFTHawking.SingularConnSquareCloseNCInt
