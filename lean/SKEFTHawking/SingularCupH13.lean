/-
# Phase 5q.F — the singular ℤ/2 cup product at bidegree `(1,3)`

The degree-`(1,3)` analogue of the surface form `cupH` (`(1,1)→2`) and the 4-manifold
intersection form `cupH24` (`(2,2)→4`). This module supplies the **concrete** cup product

  `cupH13 : Cohomology X 1 →ₗ[ZMod 2] Cohomology X 3 →ₗ[ZMod 2] Cohomology X 4`,

which `PoincareDualityWuFormula.PoincareDual4Lo` previously carried as the *abstract* field
`cup13 : H¹ →ₗ H³ →ₗ H⁴` (because the project's concrete singular cup product existed only at
bidegrees `(1,1)` and `(2,2)`). With `cupH13` in hand the first-Wu-class PD datum's cup pairing
becomes a genuine construction: it is the homology descent of the chain-level Alexander–Whitney
cup `cup` at the split `1 + 3 = 4`.

The general chain-level machinery is reused verbatim — `cup`, `cupₗ`, `cup_cocycle`,
`cup_coboundary_right`, `coboundary_cup` are all general in `(p, q)`. The `(1,3)` case differs from
`(2,2)` only in the degree arithmetic `1 + 3 = 4` and in the left-coboundary descent, which here
fires at the split `(0,3)` (the left argument `H¹ = ker δ¹` is a coboundary of a `0`-cochain) rather
than the `(1,2)` split `cupH24` uses. No general `cupH : Cohomology X a →ₗ Cohomology X b →ₗ
Cohomology X (a+b)` exists in the project, so the `(1,3)` form is built explicitly here.
-/
import SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularCohomologyMod2

open CategoryTheory Opposite

variable {X : TopCat}

/-! ### The cup product on cohomology `H¹ × H³ → H⁴` (the degree-`(1,3)` intersection form)

The exact degree-`(1,3)` analogue of `cupH` / `cupH24`. The construction mirrors the `(2,2)→4` case
verbatim with the back degree bumped `2 → 3`; the only new ingredient is the left-coboundary descent
at degree `(0,3)` (`cup_coboundary_left_0_3`) that replaces `cup_coboundary_left_1_2`. -/

/-- **Coboundary ⌣ cocycle is a coboundary** (left argument, degrees `0,3`): if `g : C³` is a cocycle
then `δa ⌣ g = δ(a ⌣ g)` for `a : C⁰`. The exact degree-bumped mirror of `cup_coboundary_left_deg0`
(degrees `0,1`) and `cup_coboundary_left_1_2` (degrees `1,2`): cast-free because the degrees are
concrete (`(0+3)+1 = 4 = 3+1`) and `frontBig`/`backBig` at split `(0,3)` are definitionally the
`frontFace`/`backFace` of `cup _ g` at split `(1,3)`. The left-argument analogue of
`cup_coboundary_right`, valid in the degree the `(1,3)` intersection form needs (`H¹ × H³ → H⁴`). -/
theorem cup_coboundary_left_0_3 (a : SingularCochain X 0) (g : SingularCochain X 3)
    (hg : coboundaryₗ X 3 g = 0) :
    coboundaryₗ X (0 + 3) (cup a g) = cup (coboundaryₗ X 0 a) g := by
  funext τ
  show coboundary X (0 + 3) (cup a g) τ = cup (coboundaryₗ X 0 a) g τ
  rw [coboundary_cup, cup_apply]
  have hg' : coboundary X 3 g (backSmall τ) = 0 := congrFun hg (backSmall τ)
  rw [hg', mul_zero, add_zero]
  rfl

/-- For a fixed degree-1 cocycle `fc`, cup-with-`fc` descends to a linear map `H³ → H⁴`. The cup lands
in cocycles (`cup_cocycle`); it kills `H³`-coboundaries because `f ⌣ δb = δ(f ⌣ b)`
(`cup_coboundary_right`). -/
noncomputable def cupRightH13 (fc : LinearMap.ker (coboundaryₗ X 1)) :
    Cohomology X 3 →ₗ[ZMod 2] Cohomology X 4 :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((cupₗ 1 3 fc.1).domRestrict (LinearMap.ker (coboundaryₗ X 3))).codRestrict
        (LinearMap.ker (coboundaryₗ X 4)) fun gc => by
          rw [LinearMap.mem_ker]
          exact cup_cocycle fc.1 gc.1 (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)))
    (by
      intro gc hgc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hgc
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, cupₗ_apply]
      show cup fc.1 gc.1 ∈ LinearMap.range (coboundaryₗ X 3)
      obtain ⟨b, hb⟩ := hgc
      refine ⟨cup fc.1 b, ?_⟩
      rw [← hb]
      exact cup_coboundary_right fc.1 b (LinearMap.mem_ker.mp fc.2))

/-- The computation rule for `cupRightH13` on a representative cocycle `gc`. -/
theorem cupRightH13_apply_mk (fc : LinearMap.ker (coboundaryₗ X 1))
    (gc : LinearMap.ker (coboundaryₗ X 3)) :
    cupRightH13 fc (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨cup fc.1 gc.1, cup_cocycle fc.1 gc.1
          (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X 4)) := by
  rfl

/-- **The cup product on `H¹ × H³ → H⁴`** — a genuine `ℤ/2`-bilinear map: the degree-`(1,3)`
intersection form `H¹(X) × H³(X) → H⁴(X)`, the concrete realization of the abstract `cup13` field of
`PoincareDualityWuFormula.PoincareDual4Lo`. Well-defined: `cup_cocycle` lands it in cocycles;
`cup_coboundary_right`/`cup_coboundary_left_0_3` kill coboundaries in each argument. The degree-`(1,3)`
analogue of the surface form `cupH` and the 4-manifold form `cupH24`. -/
noncomputable def cupH13 : Cohomology X 1 →ₗ[ZMod 2] Cohomology X 3 →ₗ[ZMod 2] Cohomology X 4 :=
  Submodule.liftQ _
    { toFun := cupRightH13
      map_add' := fun fc fc' => by
        ext x
        obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        simp only [LinearMap.add_apply, cupRightH13_apply_mk]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_add, cup_add_left]
      map_smul' := fun c fc => by
        ext x
        obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        simp only [LinearMap.smul_apply, RingHom.id_apply, cupRightH13_apply_mk]
        congr 1
        apply Subtype.ext
        simp only [SetLike.val_smul, cup_smul_left] }
    (by
      intro fc hfc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hfc
      rw [LinearMap.mem_ker]
      ext x
      obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.zero_apply]
      change cupRightH13 fc (Submodule.Quotient.mk gc) = 0
      rw [cupRightH13_apply_mk]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
      show cup fc.1 gc.1 ∈ LinearMap.range (coboundaryₗ X 3)
      obtain ⟨a, ha⟩ := hfc
      refine ⟨cup a gc.1, ?_⟩
      rw [← ha]
      exact cup_coboundary_left_0_3 a gc.1 (LinearMap.mem_ker.mp gc.2))

/-- The computation rule for `cupH13` on representative cocycles `fc : ker δ¹`, `gc : ker δ³`. -/
@[simp] theorem cupH13_mk_mk (fc : LinearMap.ker (coboundaryₗ X 1))
    (gc : LinearMap.ker (coboundaryₗ X 3)) :
    cupH13 (Submodule.Quotient.mk fc) (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨cup fc.1 gc.1, cup_cocycle fc.1 gc.1
          (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X 4)) := by
  show cupRightH13 fc (Submodule.Quotient.mk gc) = _
  exact cupRightH13_apply_mk fc gc

end SKEFTHawking.SingularCohomologyMod2
