import Mathlib
import SKEFTHawking.SingularSteenrodSq2
import SKEFTHawking.SingularRelativeBockstein
import SKEFTHawking.SingularRelativeAbsCompat

/-!
# Phase 5q.F — the relative sub-top Steenrod square `relSq² : Hⁿ(X,S) → Hⁿ⁺²(X,S)` and naturality

Relativizes `SingularSteenrodSq2.Sq2` over the annihilator subcomplex `relCochains S`, exactly as
`SingularRelativeBockstein.relSq1` relativizes the absolute `Sq¹`. The mechanism is the same
**annihilation argument**: every operator in the `Sq²` tower (`cup`, `cupOne33`, `cupTwo33`,
`cupOne23`) is a sum of products of *face-restrictions* of its arguments, and a subspace simplex's
faces are subspace simplices (general `simplexIncl` naturality), so a relative first factor kills the
product. Hence:

* the diagonal `x ⌣₁ x` of a relative cocycle is a relative `(n+2)`-cocycle (`relSq2cocycle`);
* the `Sq²` well-definedness witness `x ⌣₂ δc + (c ⌣₁ δc + c ⌣ c)` is a *relative* coboundary;
* the additivity witness `x ⌣₂ y` is a *relative* coboundary.

`relSq² : RelativeCohomology S 3 →ₗ[ℤ/2] RelativeCohomology S 5` is precisely the `(2,3)`
`PoincareLefschetzWu5.LefschetzWuDatum.sqOp` for a compact `5`-manifold-with-boundary, and
`relToAbs_relSq2` is the pair-restriction naturality `j*(relSq² x) = Sq²(j* x)` (holding on the nose).
-/

namespace SKEFTHawking.SingularRelativeSteenrodSq2

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeBockstein
  SKEFTHawking.SingularRelativeAbsCompat SKEFTHawking.SingularRelativeCup

variable {X : TopCat} {S : Set X}

/-! ## §1. General `simplexIncl` naturality and the annihilation lemmas -/

/-- **General `simplexIncl` naturality**: for any `g : [m] ⟶ [n]`, restricting a subspace simplex
`simplexIncl S n τ` along `g` is the subspace simplex of the restricted `τ`. The arbitrary-morphism
version of `simplexIncl_face` (which is `g = δ i`); `toSSet.map (incl)` is a simplicial map. -/
theorem simplexIncl_map {m n : ℕ} (g : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).map g.op (simplexIncl S n τ)
      = simplexIncl S m ((TopCat.toSSet.obj (sub S)).map g.op τ) := by
  -- v4.32: `FunctorToTypes.naturality` is deprecated in favour of `NatTrans.naturality_apply`,
  -- which states the equation in the opposite orientation (hence `.symm`).
  simpa only [simplexIncl] using
    (NatTrans.naturality_apply (TopCat.toSSet.map (inclMap S)) g.op τ).symm

/-- The absolute cup of a relative first factor annihilates the subcomplex (`f` kills subspace
simplices, and `frontFace` of a subspace simplex is a subspace simplex). -/
theorem cup_mem_relCochains {p q : ℕ} (f : relCochains S p) (g : SingularCochain X q) :
    cup (f : SingularCochain X p) g ∈ relCochains S (p + q) := by
  apply mem_relCochains_of_vanish
  intro τ
  rw [cup_apply]
  unfold frontFace
  rw [simplexIncl_map (frontIncl p q), relCochain_vanish f, zero_mul]

/-- `cupOne33` of a relative first factor annihilates the subcomplex. -/
theorem cupOne33_mem_relCochains (a : relCochains S 3) (b : SingularCochain X 3) :
    cupOne33 (a : SingularCochain X 3) b ∈ relCochains S 5 := by
  apply mem_relCochains_of_vanish
  intro τ
  simp only [cupOne33]
  rw [simplexIncl_map cuA0, simplexIncl_map cuA1, simplexIncl_map cuA2,
    relCochain_vanish a, relCochain_vanish a, relCochain_vanish a, zero_mul, zero_mul, zero_mul,
    add_zero, add_zero]

/-- `cupTwo33` of a relative first factor annihilates the subcomplex. -/
theorem cupTwo33_mem_relCochains (a : relCochains S 3) (b : SingularCochain X 3) :
    cupTwo33 (a : SingularCochain X 3) b ∈ relCochains S 4 := by
  apply mem_relCochains_of_vanish
  intro τ
  simp only [cupTwo33]
  rw [simplexIncl_map cwx0123, simplexIncl_map cwx0234, simplexIncl_map cwx0134,
    relCochain_vanish a, relCochain_vanish a, relCochain_vanish a, zero_mul, zero_mul, zero_mul,
    add_zero, add_zero, add_zero]

/-- `cupOne23` of a relative first factor annihilates the subcomplex. -/
theorem cupOne23_mem_relCochains (c : relCochains S 2) (d : SingularCochain X 3) :
    cupOne23 (c : SingularCochain X 2) d ∈ relCochains S 4 := by
  apply mem_relCochains_of_vanish
  intro τ
  simp only [cupOne23]
  rw [simplexIncl_map cwc034, simplexIncl_map cwc014,
    relCochain_vanish c, relCochain_vanish c, zero_mul, zero_mul, add_zero]

/-! ## §2. The relative `Sq²` cocycle and quotient descent -/

/-- The **relative `Sq²` cocycle**: `x ⌣₁ x` packaged as a relative `5`-cocycle (relative by
`cupOne33_mem_relCochains`, cocycle by `cupOne33_diag_cocycle`). Mirrors `relSq1cocycle`. -/
noncomputable def relSq2cocycle (a : LinearMap.ker (relCoboundaryₗ S 3)) :
    LinearMap.ker (relCoboundaryₗ S 5) :=
  ⟨⟨cupOne33 a.1.1 a.1.1, cupOne33_mem_relCochains a.1 a.1.1⟩,
    (relCoboundary_eq_zero_iff _).mpr
      (cupOne33_diag_cocycle a.1.1 ((relCoboundary_eq_zero_iff a.1).mp (LinearMap.mem_ker.mp a.2)))⟩

@[simp] theorem relSq2cocycle_coe (a : LinearMap.ker (relCoboundaryₗ S 3)) :
    ((relSq2cocycle a : LinearMap.ker (relCoboundaryₗ S 5)) : SingularCochain X 5)
      = cupOne33 a.1.1 a.1.1 := rfl

/-- **Relative well-definedness**: the difference `x ⌣₁ x − x' ⌣₁ x'` of cohomologous relative
`3`-cocycles (`δβ = x − x'`, `β` relative) is a **relative** `5`-coboundary. The witness
`x' ⌣₂ δβ + (β ⌣₁ δβ + β ⌣ β)` is relative because every summand has a relative first factor
(§1 annihilation); its coboundary is the difference by the absolute `sq2_cochain_shift`. -/
theorem relSq2cochain_sub_mem_range (a a' : LinearMap.ker (relCoboundaryₗ S 3))
    (β : relCochains S 2) (hβ : coboundary X 2 (β : SingularCochain X 2) = a.1.1 - a'.1.1) :
    ∃ w : relCochains S 4, coboundaryₗ X 4 (w : SingularCochain X 4)
      = cupOne33 a.1.1 a.1.1 - cupOne33 a'.1.1 a'.1.1 := by
  have hz : coboundaryₗ X 3 a'.1.1 =
      0 := (relCoboundary_eq_zero_iff a'.1).mp (LinearMap.mem_ker.mp a'.2)
  refine ⟨⟨cupTwo33 a'.1.1 (coboundaryₗ X 2 (β : SingularCochain X 2))
      + (cupOne23 (β : SingularCochain X 2) (coboundaryₗ X 2 (β : SingularCochain X 2))
        + cup (β : SingularCochain X 2) (β : SingularCochain X 2)),
    Submodule.add_mem _ (cupTwo33_mem_relCochains a'.1 _)
      (Submodule.add_mem _ (cupOne23_mem_relCochains β _)
        (cup_mem_relCochains β (β : SingularCochain X 2)))⟩, ?_⟩
  have hac : a.1.1 = a'.1.1 + coboundaryₗ X 2 (β : SingularCochain X 2) := by
    rw [show coboundaryₗ X 2 (β : SingularCochain X 2)
      = coboundary X 2 (β : SingularCochain X 2) from rfl, hβ]; abel
  show coboundaryₗ X 4 _ = cupOne33 a.1.1 a.1.1 - cupOne33 a'.1.1 a'.1.1
  rw [hac, sq2_cochain_shift a'.1.1 (β : SingularCochain X 2) hz]
  abel

/-- The **relative `Sq²` set-function** `[x] ↦ [x ⌣₁ x]` on `Hⁿ(X,S)`. Mirrors `relSq1fun`. -/
noncomputable def relSq2fun (x : RelativeCohomology S 3) : RelativeCohomology S 5 := by
  refine Quotient.liftOn' x (fun a => RelativeCohomology.mk S 5 (relSq2cocycle a)) ?_
  rintro a a' hrel
  rw [Submodule.quotientRel_def] at hrel
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub] at hrel
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  rw [show relCoboundaryRange S 5 = LinearMap.range (relCoboundaryₗ S 4) from rfl]
  obtain ⟨β, hβ⟩ := hrel
  have hβ_coe : coboundary X 2 (β : SingularCochain X 2) = a.1.1 - a'.1.1 := by
    have := congrArg Subtype.val hβ
    rwa [relCoboundaryₗ_coe, AddSubgroupClass.coe_sub] at this
  obtain ⟨w, hw⟩ := relSq2cochain_sub_mem_range a a' β hβ_coe
  refine ⟨w, ?_⟩
  apply Subtype.ext
  rw [relCoboundaryₗ_coe, AddSubgroupClass.coe_sub, relSq2cocycle_coe, relSq2cocycle_coe]
  exact hw

@[simp] theorem relSq2fun_mk (a : LinearMap.ker (relCoboundaryₗ S 3)) :
    relSq2fun (RelativeCohomology.mk S 3 a) = RelativeCohomology.mk S 5 (relSq2cocycle a) := rfl

/-- `relSq2fun` is **additive**: the cross term `x ⌣₁ y + y ⌣₁ x = δ(x ⌣₂ y)` is a relative
`5`-coboundary (`cupTwo33_mem_relCochains` + `cupTwo33_coboundary`). -/
theorem relSq2fun_add (x y : RelativeCohomology S 3) :
    relSq2fun (x + y) = relSq2fun x + relSq2fun y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show relSq2fun (RelativeCohomology.mk S 3 (a + b))
      = relSq2fun (RelativeCohomology.mk S 3 a) + relSq2fun (RelativeCohomology.mk S 3 b)
  rw [relSq2fun_mk, relSq2fun_mk, relSq2fun_mk]
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
  erw [← Submodule.Quotient.mk_add]
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub, AddMemClass.coe_add]
  rw [show relCoboundaryRange S 5 = LinearMap.range (relCoboundaryₗ S 4) from rfl]
  refine ⟨⟨cupTwo33 a.1.1 b.1.1, cupTwo33_mem_relCochains a.1 b.1.1⟩, ?_⟩
  have hx : coboundaryₗ X 3 a.1.1 = 0 := (relCoboundary_eq_zero_iff a.1).mp (LinearMap.mem_ker.mp a.2)
  have hy : coboundaryₗ X 3 b.1.1 = 0 := (relCoboundary_eq_zero_iff b.1).mp (LinearMap.mem_ker.mp b.2)
  apply Subtype.ext
  rw [relCoboundaryₗ_coe, AddSubgroupClass.coe_sub, AddSubmonoid.coe_add,
    relSq2cocycle_coe, relSq2cocycle_coe, relSq2cocycle_coe]
  show coboundaryₗ X 4 (cupTwo33 a.1.1 b.1.1)
      = cupOne33 (a.1.1 + b.1.1) (a.1.1 + b.1.1) - (cupOne33 a.1.1 a.1.1 + cupOne33 b.1.1 b.1.1)
  rw [show coboundaryₗ X 4 (cupTwo33 a.1.1 b.1.1) = coboundary X 4 (cupTwo33 a.1.1 b.1.1) from rfl,
    cupTwo33_coboundary a.1.1 b.1.1 hx hy, cupOne33_add_left, cupOne33_add_right,
    cupOne33_add_right]
  abel

/-- `relSq2fun 0 = 0`, from additivity. -/
theorem relSq2fun_zero : relSq2fun (0 : RelativeCohomology S 3) = 0 := by
  have h := relSq2fun_add (0 : RelativeCohomology S 3) 0
  rw [add_zero] at h
  have h2 : relSq2fun (0 : RelativeCohomology S 3) + 0
      = relSq2fun (0 : RelativeCohomology S 3) + relSq2fun 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- **The relative sub-top Steenrod square** `relSq² : H³(X,S;ℤ/2) →ₗ[ℤ/2] H⁵(X,S;ℤ/2)`, `[x] ↦
[x ⌣₁ x]` — the `(2,3)` `PoincareLefschetzWu5.LefschetzWuDatum.sqOp` for a compact
`5`-manifold-with-boundary (the analogue at `k = 2` of `relSq¹` at the `(1,4)` leg). -/
noncomputable def relSq2 : RelativeCohomology S 3 →ₗ[ZMod 2] RelativeCohomology S 5 where
  toFun := relSq2fun
  map_add' := relSq2fun_add
  map_smul' r x := by
    fin_cases r
    · show relSq2fun ((0 : ZMod 2) • x) = (0 : ZMod 2) • relSq2fun x
      rw [zero_smul, zero_smul, relSq2fun_zero]
    · show relSq2fun ((1 : ZMod 2) • x) = (1 : ZMod 2) • relSq2fun x
      rw [one_smul, one_smul]

@[simp] theorem relSq2_apply (a : LinearMap.ker (relCoboundaryₗ S 3)) :
    relSq2 (RelativeCohomology.mk S 3 a) = RelativeCohomology.mk S 5 (relSq2cocycle a) := rfl

/-! ## §3. Pair-restriction naturality `j*(relSq² x) = Sq²(j* x)` -/

/-- **The absolutification intertwines the relative and absolute `Sq²`**: `j*(relSq² x) = Sq²(j* x)`
for `x ∈ H³(X,S)`. Holds on the nose (both sides are `[x ⌣₁ x]`). The compatibility with pair
restriction (and with the absolute `Sq²`) that `LefschetzWuDatum.sqOp` consumes at the `(2,3)` leg. -/
theorem relToAbs_relSq2 (x : RelativeCohomology S 3) :
    relToAbs (relSq2 x) = Sq2 (relToAbs x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relToAbs (relSq2 (RelativeCohomology.mk S 3 a))
    = Sq2 (relToAbs (RelativeCohomology.mk S 3 a))
  rw [relSq2_apply, relToAbs_mk, relToAbs_mk]
  show Cohomology.mk X 5 (relToAbsCocycleₗ (relSq2cocycle a))
    = Sq2 (Cohomology.mk X 3 (relToAbsCocycleₗ a))
  rw [Sq2_mk]
  rfl

/-! ## §4. The `(2,3)` Wu-datum `sqOp` plug-in

`PoincareLefschetzWu5.LefschetzWuDatum X S k nk n` carries `sqOp : RelativeCohomology S nk →ₗ[ℤ/2]
RelativeCohomology S n` abstractly. At the `(2,3)` leg `(k, nk, n) = (2, 3, 5)` this is exactly the
type of `relSq2`, so a `(2,3)` datum `P₂₃ : LefschetzWuDatum X S 2 3 5` is now built with
`sqOp := lefschetzWu23_sqOp` — the previously-abstract Steenrod-`Sq²` field discharged concretely
(the `k = 2` analogue of the `(1,4)` leg's `sqOp := relSq1`). The `wu_relation` `⟨v₂ ⌣ a, [M]⟩ =
⟨Sq² a, [M]⟩` then holds against a genuine sub-top square, and `relToAbs_relSq2` supplies the
pair-restriction naturality the tower's `absToRel`/`relToAbs` legs consume. No deep instance work is
performed here (the remaining datum fields — `mu`, `cup`, Poincaré–Lefschetz duality — are the tower's
concern); this fixes only the `sqOp` field's value and its type. -/
noncomputable abbrev lefschetzWu23_sqOp :
    RelativeCohomology S 3 →ₗ[ZMod 2] RelativeCohomology S 5 := relSq2

end SKEFTHawking.SingularRelativeSteenrodSq2
