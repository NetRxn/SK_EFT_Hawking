import Mathlib
import SKEFTHawking.SingularRelativeDisjointUnionDetect

/-!
# Phase 5q.H — PER-POINT INTERIOR DETECTION (the closed-piece interior-point strengthening)

`SingularRelativeDisjointUnionDetect.restrictsToRelGenOn_of_relIncl_ne_zero` discharges the per-piece
detection witness `RestrictsToRelGenOn S gen (· ∈ U) (excisionMap S U αU)` from a nonzero intrinsic
restriction, but demands the piece `U` be **globally open** (`IsOpen U`) — the hypothesis of the
excision cover `{x}ᶜ ∪ U = univ`. That global hypothesis is stronger than the argument needs: the
excision `excisionMap {x}ᶜ U` is an isomorphism at a single point `x` as soon as `x ∈ interior U`
(then `{x}ᶜ ∪ interior U = univ`), with no openness demanded of `U` away from `x`.

This module records that **per-point** strengthening. For an interior point `x ∈ interior U` (with `U`
possibly only closed), a nonzero intrinsic restriction of `αU` at `x` still forces the ambient
detection `restrictBd S hx (excisionMap S U αU) = (gen x hx).symm 1`. Consequently a **closed** piece
`U` detects the interior generator at every point of its topological interior `interior U` — the honest
statement of "a closed collar/cylinder piece detects at its manifold-interior points, though not at its
frontier". The predicate is folded over `interior U`, so this is the interior-only twin of the
open-piece brick, usable wherever a piece is closed but the detection is only needed at interior points.

* `excision_cover_compl_singleton_interior` — the excision cover from `x ∈ interior U` (no `IsOpen U`).
* `restrictBd_excisionMap_eq_gen_of_mem_interior` — the pointwise detection at `x ∈ interior U`.
* `restrictsToRelGenOn_of_relIncl_ne_zero_interior` — the folded interior-piece detection witness.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeDisjointUnionFundClass
open SKEFTHawking.SingularRelativeExcisionRestrict
open SKEFTHawking.SingularRelativeDisjointUnionDetect

namespace SKEFTHawking.SingularRelativeDisjointUnionDetectInterior

variable {X : TopCat}

/-- **The excision cover for a punctured neighbourhood, from `x ∈ interior U`.** The interiors of
`{x}ᶜ` and `U` cover `X` whenever `x` is an interior point of `U` — `{x}` is closed so `{x}ᶜ` is open
with interior itself, and `interior U` supplies the missing point `x`. This is the per-point weakening
of `excision_cover_compl_singleton`: no global `IsOpen U`, only `x ∈ interior U`. -/
theorem excision_cover_compl_singleton_interior [T1Space ↑X] {U : Set ↑X} {x : ↑X}
    (hxU : x ∈ interior U) :
    (⋃ V ∈ ({({x}ᶜ : Set ↑X), U} : Set (Set ↑X)), interior V) = Set.univ := by
  have hxcl : IsOpen ({x}ᶜ : Set ↑X) := isOpen_compl_singleton
  refine Set.eq_univ_of_forall (fun y => ?_)
  rw [Set.mem_iUnion₂]
  by_cases hy : y = x
  · exact ⟨U, by simp, hy ▸ hxU⟩
  · exact ⟨({x}ᶜ : Set ↑X), by simp, by rw [hxcl.interior_eq]; exact hy⟩

/-- **The pointwise detection at an interior point of a (possibly closed) piece.** For `x ∈ interior U`
(with `x ∉ S`), if the intrinsic local restriction `relIncl … αU` of `αU` inside `sub U` is nonzero at
`x`, then `excisionMap S U αU` restricts to the unique generator `(gen x hx).symm 1` at `x`. The
excision `excisionMap {x}ᶜ U` is an iso at `x` (`{x}ᶜ ∪ interior U = univ`) and `H_{m+2}(X, {x}ᶜ) ≅ ℤ/2`,
so the excised nonzero class is the generator — with no global openness on `U`, only `x ∈ interior U`. -/
theorem restrictBd_excisionMap_eq_gen_of_mem_interior {m : ℕ} [T1Space ↑X] {S U : Set ↑X} {x : ↑X}
    (hx : x ∉ S) (hxU : x ∈ interior U)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (αU : RelativeHomology (restr S U) (m + 2))
    (hne : relIncl (restr_mono U (Set.subset_compl_singleton_iff.mpr hx)) (m + 2) αU ≠ 0) :
    restrictBd S hx (m + 2) (excisionMap S U (m + 2) αU) = (gen x hx).symm 1 := by
  rw [restrictBd_excisionMap hx (m + 2) αU]
  set v := excisionMap ({x}ᶜ) U (m + 2)
    (relIncl (restr_mono U (Set.subset_compl_singleton_iff.mpr hx)) (m + 2) αU) with hv
  have hinj : Function.Injective (excisionMap ({x}ᶜ) U (m + 2)) :=
    excisionMap_injective ({x}ᶜ) U (m + 1) (excision_cover_compl_singleton_interior hxU)
  have hv_ne : v ≠ 0 := by
    intro h0
    exact hne (hinj (hv.symm.trans (h0.trans (map_zero _).symm)))
  have hgv_ne : gen x hx v ≠ 0 := fun h =>
    hv_ne ((gen x hx).injective (h.trans (map_zero (gen x hx)).symm))
  have h1 : gen x hx v = 1 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (gen x hx v) with h | h
    · exact absurd h hgv_ne
    · exact h
  rw [← h1, LinearEquiv.symm_apply_apply]

/-- **The interior-piece detection witness.** For a (possibly closed) piece `U` and a supplied
per-ambient generator family `gen`, if the intrinsic local restriction of `αU` is nonzero at every
**interior** point `x ∈ interior U`, then `excisionMap S U αU` detects the generator on `interior U`
(the folded `RestrictsToRelGenOn` witness, predicate `(· ∈ interior U)`). The interior-only twin of
`restrictsToRelGenOn_of_relIncl_ne_zero`: it drops the global `IsOpen U` hypothesis, detecting exactly
on the topological interior — the sharp statement for a closed collar/cylinder piece. -/
theorem restrictsToRelGenOn_of_relIncl_ne_zero_interior {m : ℕ} [T1Space ↑X] {S U : Set ↑X}
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (αU : RelativeHomology (restr S U) (m + 2))
    (hne : ∀ (x : ↑X) (hx : x ∉ S), x ∈ interior U →
      relIncl (restr_mono U (Set.subset_compl_singleton_iff.mpr hx)) (m + 2) αU ≠ 0) :
    RestrictsToRelGenOn S gen (· ∈ interior U) (excisionMap S U (m + 2) αU) := by
  intro x hx hxU
  exact restrictBd_excisionMap_eq_gen_of_mem_interior hx hxU gen αU (hne x hx hxU)

end SKEFTHawking.SingularRelativeDisjointUnionDetectInterior
