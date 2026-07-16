import Mathlib
import SKEFTHawking.SingularRelativeExcisionRestrict
import SKEFTHawking.SingularRelativeDisjointUnionFundClass

/-!
# Phase 5q.H — THE PER-PIECE DETECTION FROM NONZERO INTRINSIC RESTRICTION (route (b), nonzero side)

The disconnected `[W, ∂W]` engine (`SingularRelativeDisjointUnionFundClass`) needs, per clopen piece
`U`, a witness `RestrictsToRelGenOn S gen (· ∈ U) (excisionMap S U αU)` — the SAME-piece detection at
every interior point of `U`. This module discharges that witness from a single, minimal input: the
INTRINSIC local restriction of `αU` inside the piece is **nonzero**.

The mechanism combines two facts:

* the excision–restriction naturality (`restrictBd_excisionMap`): the ambient detection at `x ∈ U`
  equals the excision (over `{x}ᶜ`) of the intrinsic restriction `relIncl … αU` inside `sub U`;
* over `ℤ/2` the local homology `H_{m+2}(X, {x}ᶜ) ≅ ℤ/2` has a UNIQUE nonzero element, and the
  excision `excisionMap {x}ᶜ U` is an ISOMORPHISM (its interiors cover: `x ∈ U` open, `{x}` closed by
  `T1`, so `{x}ᶜ ∪ U = univ`). Hence a nonzero intrinsic restriction excises to a nonzero — thus the
  unique generator `(gen x hx).symm 1`, for ANY generator family `gen`.

This is exactly the route-(b) reduction on the nonzero side: the per-piece detection reduces to
"the piece's fundamental class restricts nonzero at each of its interior points", with NO on-the-nose
generator matching (the `ℤ/2` uniqueness absorbs it).

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

namespace SKEFTHawking.SingularRelativeDisjointUnionDetect

variable {X : TopCat}

/-- **The excision cover for a punctured neighbourhood**: for an open `U ∋ x` in a `T1` space, the
interiors of `{x}ᶜ` and `U` cover `X` (`{x}` is closed, so `{x}ᶜ` is open with interior itself, and
`{x}ᶜ ∪ U ⊇ {x}ᶜ ∪ {x} = univ`). The hypothesis of `excisionMap_injective`/`excisionMap_surjective`
for the pair `({x}ᶜ, U)`. -/
theorem excision_cover_compl_singleton [T1Space ↑X] {U : Set ↑X} {x : ↑X}
    (hUopen : IsOpen U) (hxU : x ∈ U) :
    (⋃ V ∈ ({({x}ᶜ : Set ↑X), U} : Set (Set ↑X)), interior V) = Set.univ := by
  have hxcl : IsOpen ({x}ᶜ : Set ↑X) := isOpen_compl_singleton
  refine Set.eq_univ_of_forall (fun y => ?_)
  rw [Set.mem_iUnion₂]
  by_cases hy : y = x
  · exact ⟨U, by simp, by rw [hUopen.interior_eq]; exact hy ▸ hxU⟩
  · exact ⟨({x}ᶜ : Set ↑X), by simp, by rw [hxcl.interior_eq]; exact hy⟩

/-- **The per-piece detection from a nonzero intrinsic restriction.** For an open piece `U` in a `T1`
space and a supplied per-ambient generator family `gen`, if the intrinsic local restriction
`relIncl … αU` of `αU` inside `sub U` is nonzero at every interior point `x ∈ U`, then
`excisionMap S U αU` detects the generator on `U` — the folded `RestrictsToRelGenOn` witness. The
excision `excisionMap {x}ᶜ U` is an iso and `H_{m+2}(X, {x}ᶜ) ≅ ℤ/2`, so the excised nonzero class is
the unique generator. -/
theorem restrictsToRelGenOn_of_relIncl_ne_zero {m : ℕ} [T1Space ↑X] {S U : Set ↑X}
    (hUopen : IsOpen U)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (αU : RelativeHomology (restr S U) (m + 2))
    (hne : ∀ (x : ↑X) (hx : x ∉ S), x ∈ U →
      relIncl (restr_mono U (Set.subset_compl_singleton_iff.mpr hx)) (m + 2) αU ≠ 0) :
    RestrictsToRelGenOn S gen (· ∈ U) (excisionMap S U (m + 2) αU) := by
  intro x hx hxU
  rw [restrictBd_excisionMap hx (m + 2) αU]
  set v := excisionMap ({x}ᶜ) U (m + 2)
    (relIncl (restr_mono U (Set.subset_compl_singleton_iff.mpr hx)) (m + 2) αU) with hv
  have hinj : Function.Injective (excisionMap ({x}ᶜ) U (m + 2)) :=
    excisionMap_injective ({x}ᶜ) U (m + 1) (excision_cover_compl_singleton hUopen hxU)
  have hv_ne : v ≠ 0 := by
    intro h0
    exact hne x hx hxU (hinj (hv.symm.trans (h0.trans (map_zero _).symm)))
  have hgv_ne : gen x hx v ≠ 0 := fun h =>
    hv_ne ((gen x hx).injective (h.trans (map_zero (gen x hx)).symm))
  have h1 : gen x hx v = 1 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (gen x hx v) with h | h
    · exact absurd h hgv_ne
    · exact h
  rw [← h1, LinearEquiv.symm_apply_apply]

end SKEFTHawking.SingularRelativeDisjointUnionDetect
