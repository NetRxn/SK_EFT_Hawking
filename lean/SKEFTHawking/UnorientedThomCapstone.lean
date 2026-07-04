import SKEFTHawking.PinPlusGMWitness

/-!
# The `Ω₄^{Pin⁺} ≅ ℤ/16` capstone reduced to the named unoriented-Thom detection Prop

Phase 5q.H — the honest apex of the direct (unoriented) injectivity route. The tied carrier's structured
bordism relation (`IsDataBordant`) uses a genuine unoriented `Bordism` plus grade-`16` matching, so
`[s,str] = 0` iff `s` unoriented-bounds AND `str.grade16 = 0`. Grade-`0` therefore reduces the whole
injectivity (`ker abkGMTied16 = ⊥`) to a single geometric statement about the carrier's own manifolds:

  **every certified-Pin⁺ (`w₂ = 0`, via `PinPlusCertK`) 4-manifold with vanishing top SW number
  `w₁⁴` (`swTotalNe = 0`, via `htie`) bounds.**

This is exactly the (unoriented) Thom-detection theorem specialized to the Pin⁺ + grade-`0` case: by the Wu
collapse (`wuW4 = w₁⁴`, merged) and `w₂ = 0`, ALL Stiefel–Whitney numbers of such a manifold vanish, so
Thom's `Ω_*^O ≅ π_*(MO)` detection gives that it is null-bordant. The reduction below is UNCONDITIONAL and
kernel-pure; the sole remaining input is this one named geometric Prop (the `hyp:rokhlin_sigma_mod_16`
Rokhlin-class node in its most elementary in-carrier form) — a from-scratch bordism-classification foundation.
-/

namespace SKEFTHawking.UnorientedThomCapstone

open scoped Manifold
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusTiedData SKEFTHawking.PinPlusGMTiedData
open SKEFTHawking.PinPlusGMWitness

universe u

/-- **`ker abkGMTied16 = ⊥` from the unoriented Thom-detection input.** The hypothesis `hthom` is the sole
disclosed geometric Prop: every certified-Pin⁺ 4-manifold with vanishing `w₁⁴` (`swTotalNe = 0`) bounds. A
grade-`0` class has `swTotalNe = 0` (via `htie`) and carries the Pin⁺ cert; `hthom` then bounds its manifold,
so the class is `0` (grade-matched to the empty structure). -/
theorem grade0_bounds_of_thom
    (hthom : ∀ (s : SingularManifold.{0, u, 0, 0} PUnit.{u+1} 0 (𝓡 4)) (t2 : T2Space s.M),
      PinPlusCertK (𝓡 4) s → swTotalNe s t2 = 0 →
        Nonempty (Bordism ((𝓡 4).prod (𝓡∂ 1)) s emptySM))
    (x : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hx : (abkGMTied16 (k := 0) (I := 𝓡 4) :
        DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16) x = 0) : x = 0 := by
  induction x using Quot.ind with | _ p =>
  obtain ⟨s, str⟩ := p
  have hg : str.grade16 = 0 := hx
  have hsw : swTotalNe s str.t2 = 0 := by
    have h := str.htie
    rw [hg, map_zero] at h
    exact h.symm
  obtain ⟨b⟩ := hthom s str.t2 str.cert hsw
  show DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩ = 0
  refine DataBordismGrp.mk_eq_of_bordant _ ⟨b, ⟨PLift.up ?_⟩⟩
  exact hg

/-- **`Ω₄^{Pin⁺} ≅ ℤ/16` GIVEN the named unoriented-Thom detection.** The entire result rests on the single
geometric Prop `hthom` (certified-Pin⁺ + `w₁⁴ = 0` ⟹ bounds) — the elementary in-carrier form of the
Rokhlin-class node, whose discharge is the from-scratch unoriented-bordism-classification (Thom) foundation. -/
theorem omega4PinPlusGMTied_equiv_zmod16_of_thom
    (hthom : ∀ (s : SingularManifold.{0, u, 0, 0} PUnit.{u+1} 0 (𝓡 4)) (t2 : T2Space s.M),
      PinPlusCertK (𝓡 4) s → swTotalNe s t2 = 0 →
        Nonempty (Bordism ((𝓡 4).prod (𝓡∂ 1)) s emptySM)) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  omega4PinPlusGMTied_equiv_zmod16_of_grade0_bounds (grade0_bounds_of_thom hthom)

end SKEFTHawking.UnorientedThomCapstone
