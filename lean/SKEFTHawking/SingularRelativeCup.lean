/-
# Phase 5q.H (W-A item 1a) — the relative cup product `H^k(X) × H^m(X,S) → H^{k+m}(X,S)`

The absolute×relative→relative cup for a subspace `S ⊆ X`, realising the abstract `cup` field of
`PoincareLefschetzWu5.LefschetzWuDatum`. The engine is the Alexander–Whitney cochain cup
`SingularCohomologyMod2.cup` with `cup f g σ = f (frontFace σ) * g (backFace σ)`: cupping an absolute
cochain `a` on the LEFT with a **relative** cochain `b` on the RIGHT lands in the relative cochains,
because the `backFace` of a subspace simplex is a subspace simplex (`backFace_simplexIncl`), so
`b (backFace σ) = 0` whenever `σ` lies in `S`. The right (relative) argument descends to relative
cohomology using ONLY the general right-Leibniz `cup_coboundary_right` (available at all degrees),
so the fixed-left-cocycle map `relCupRightGeneralH` is generic in `(k, m)` — the exact relative
mirror of `SingularCupCapHomology.cupRightGeneralH`. The full bilinear map on `H^k(X)` descends the
left argument via the degree-specific left-Leibniz (`cup_coboundary_left_0_4`, `cup_coboundary_left_1_3`,
cast-free at the concrete tower degrees), giving `relCupH14 : H¹×H⁴(X,S)→H⁵(X,S)` and
`relCupH23 : H²×H³(X,S)→H⁵(X,S)` — the `(1,4)` and `(2,3)` `cup` fields of the `n=5` Wu datum.

All cohomology is the project's genuine singular ℤ/2 (co)homology. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMod2
import SKEFTHawking.SingularRelativeCap

namespace SKEFTHawking.SingularRelativeCup

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeCap

variable {X : TopCat} {S : Set X}

/-! ## §1. The annihilation lemma: absolute ⌣ relative lands in relative cochains -/

/-- A relative cochain `f ∈ Cⁿ(X,S)` **vanishes on every subspace simplex** `simplexIncl S n τ`:
`single (simplexIncl S n τ) 1` is a subspace chain, on which `f` pairs to `0` (`kronecker_single`). -/
theorem relCochain_vanish {n : ℕ} (f : relCochains S n)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n))) :
    (f : SingularCochain X n) (simplexIncl S n τ) = 0 := by
  have hmem : Finsupp.single (simplexIncl S n τ) (1 : ZMod 2) ∈ subspaceChains S n :=
    ⟨Finsupp.single τ 1, by rw [chainIncl_single]⟩
  have h := f.2 _ hmem
  rwa [kronecker_single, one_mul] at h

/-- **The relative cup annihilation.** For any absolute `a : Cᵏ(X)` and relative `b ∈ Cᵐ(X,S)`, the
Alexander–Whitney cup `a ⌣ b` again vanishes on subspace `(k+m)`-chains: on a subspace simplex
`simplexIncl S (k+m) τ` the value is `a (frontFace …) * b (backFace (simplexIncl S (k+m) τ))`, and
`backFace (simplexIncl S (k+m) τ) = simplexIncl S m (backFace τ)` (`backFace_simplexIncl`) is a
subspace simplex, so `b` kills it (`relCochain_vanish`). Hence `a ⌣ b ∈ Cᵏ⁺ᵐ(X,S)`. -/
theorem cup_mem_relCochains {k m : ℕ} (a : SingularCochain X k) (b : relCochains S m) :
    cup a (b : SingularCochain X m) ∈ relCochains S (k + m) := by
  intro c hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero]; simp only [kronecker_apply, Finsupp.sum_zero_index]
  | add c₁ c₂ h₁ h₂ => rw [map_add, kronecker_add_right, h₁, h₂, add_zero]
  | single τ a' =>
      rw [chainIncl_single, kronecker_single, cup_apply, backFace_simplexIncl,
        relCochain_vanish b (backFace τ), mul_zero, mul_zero]

/-! ## §2. The relative cup at cochain level and the generic right cup on cohomology -/

/-- A relative cocycle test: `δ_rel f = 0` iff the underlying absolute coboundary vanishes. -/
theorem relCoboundary_eq_zero_iff {n : ℕ} (f : relCochains S n) :
    relCoboundaryₗ S n f = 0 ↔ coboundary X n (f : SingularCochain X n) = 0 := by
  rw [Subtype.ext_iff, relCoboundaryₗ_coe, ZeroMemClass.coe_zero]

/-- The **relative cup at cochain level**, right argument: for a fixed absolute cochain `a : Cᵏ(X)`,
`b ↦ a ⌣ b` as a `ℤ/2`-linear map `Cᵐ(X,S) → Cᵏ⁺ᵐ(X,S)` (well-typed by `cup_mem_relCochains`). -/
noncomputable def relCupCochainₗ {k m : ℕ} (a : SingularCochain X k) :
    relCochains S m →ₗ[ZMod 2] relCochains S (k + m) :=
  ((cupₗ k m a).comp (relCochains S m).subtype).codRestrict (relCochains S (k + m))
    (fun b => cup_mem_relCochains a b)

@[simp] theorem relCupCochainₗ_coe {k m : ℕ} (a : SingularCochain X k) (b : relCochains S m) :
    (relCupCochainₗ a b : SingularCochain X (k + m)) = cup a (b : SingularCochain X m) := rfl

/-- **Absolute-cocycle ⌣ relative-cocycle is a relative cocycle.** For `a` an absolute `k`-cocycle
and `gc` a relative `m`-cocycle, `a ⌣ gc` is a relative `(k+m)`-cocycle: `δ(a⌣gc) = a⌣δgc = 0`
(`cup_coboundary_right`, general). Packaged as a linear map on relative cocycles. -/
noncomputable def relCupCocycleₗ {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k)) :
    LinearMap.ker (relCoboundaryₗ S m) →ₗ[ZMod 2] LinearMap.ker (relCoboundaryₗ S (k + m)) :=
  ((relCupCochainₗ a.1).domRestrict (LinearMap.ker (relCoboundaryₗ S m))).codRestrict
    (LinearMap.ker (relCoboundaryₗ S (k + m))) fun gc => by
      rw [LinearMap.mem_ker, relCoboundary_eq_zero_iff, LinearMap.domRestrict_apply,
        relCupCochainₗ_coe]
      show coboundaryₗ X (k + m) (cup a.1 (gc.1 : SingularCochain X m)) = 0
      rw [cup_coboundary_right a.1 _ (LinearMap.mem_ker.mp a.2)]
      have hz : coboundaryₗ X m (gc.1 : SingularCochain X m) = 0 :=
        (relCoboundary_eq_zero_iff gc.1).mp (LinearMap.mem_ker.mp gc.2)
      rw [hz, ← cupₗ_apply, map_zero]

@[simp] theorem relCupCocycleₗ_coe {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k))
    (gc : LinearMap.ker (relCoboundaryₗ S m)) :
    ((relCupCocycleₗ a gc : LinearMap.ker (relCoboundaryₗ S (k + m))) : SingularCochain X (k + m))
      = cup a.1 (gc.1 : SingularCochain X m) := rfl

/-- For a fixed `k`-**cocycle** `a` (`δa = 0`), cup-with-`a` on the LEFT descends to a linear map on
relative cohomology `Hᵐ(X,S) → Hᵏ⁺ᵐ(X,S)`. The cup lands in relative cocycles (`relCupCocycleₗ`); it
kills relative coboundaries because `a ⌣ δβ = δ(a ⌣ β)` (`cup_coboundary_right`). Generic in `(k, m)`
— the exact relative mirror of `SingularCupCapHomology.cupRightGeneralH`. -/
noncomputable def relCupRightGeneralH {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k)) :
    RelativeCohomology S m →ₗ[ZMod 2] RelativeCohomology S (k + m) :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (relCupCocycleₗ a))
    (by
      intro gc hgc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hgc
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
      cases m with
      | zero =>
          rw [show relCoboundaryRange S 0 = (⊥ : Submodule (ZMod 2) (relCochains S 0)) from rfl,
            Submodule.mem_bot] at hgc
          have : gc = 0 := Subtype.ext hgc
          rw [this, map_zero]
          exact Submodule.zero_mem _
      | succ j =>
          rw [show relCoboundaryRange S (j + 1) = LinearMap.range (relCoboundaryₗ S j) from rfl] at hgc
          obtain ⟨b, hb⟩ := hgc
          rw [show relCoboundaryRange S (k + (j + 1)) = LinearMap.range (relCoboundaryₗ S (k + j))
            from rfl]
          refine ⟨relCupCochainₗ a.1 b, ?_⟩
          apply Subtype.ext
          rw [relCoboundaryₗ_coe, relCupCochainₗ_coe]
          show coboundaryₗ X (k + j) (cup a.1 (b : SingularCochain X j)) = _
          rw [cup_coboundary_right a.1 _ (LinearMap.mem_ker.mp a.2)]
          show cup a.1 (coboundaryₗ X j (b : SingularCochain X j)) = ((relCupCocycleₗ a gc :
            LinearMap.ker (relCoboundaryₗ S (k + j + 1))) : SingularCochain X (k + j + 1))
          rw [relCupCocycleₗ_coe]
          congr 1
          show coboundary X j (b : SingularCochain X j) = _
          rw [← relCoboundaryₗ_coe, hb])

/-- Computation rule for `relCupRightGeneralH` on a representative relative cocycle `gc`. -/
@[simp] theorem relCupRightGeneralH_apply_mk {k m : ℕ}
    (a : LinearMap.ker (coboundaryₗ X k)) (gc : LinearMap.ker (relCoboundaryₗ S m)) :
    relCupRightGeneralH a (RelativeCohomology.mk S m gc)
      = RelativeCohomology.mk S (k + m) (relCupCocycleₗ a gc) := rfl

/-- Computation rule in the raw `Submodule.Quotient.mk` form — the form `mk_surjective` produces, so it
`rw`-matches without the `RelativeCohomology.mk` reducibility wall (friction catalog). -/
theorem relCupRightGeneralH_mk {k m : ℕ}
    (a : LinearMap.ker (coboundaryₗ X k)) (gc : LinearMap.ker (relCoboundaryₗ S m)) :
    relCupRightGeneralH a (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (relCupCocycleₗ a gc) := rfl

/-! ## §3. The `n = 5` bilinear relative cups `H¹×H⁴→H⁵` and `H²×H³→H⁵` (left-argument descent)

Descending the LEFT (absolute) argument to a genuine cohomology class needs the left-Leibniz
`δa ⌣ g = δ(a ⌣ g)` for a relative cocycle `g`. In-tree this is proven only at `(0,1)` and `(1,2)`;
the two Wu-tower degrees are `(0,4)` (for `H¹`) and `(1,3)` (for `H²`), both cast-free at the concrete
degrees exactly as `cup_coboundary_left_deg0`. -/

/-- **Coboundary ⌣ cocycle is a coboundary** (left argument, degrees `0,4`): `δa ⌣ g = δ(a ⌣ g)` for
`a : C⁰`, `g : C⁴` a cocycle. The `(0,4)` degree-bumped mirror of `cup_coboundary_left_deg0`,
cast-free (`(0+4)+1 = 5 = 0+5` and `frontBig`/`backBig` at split `(0,4)` are definitionally the
`frontFace`/`backFace` of `cup _ g` at split `(1,4)`). The left descent the `H¹` Wu class needs. -/
theorem cup_coboundary_left_0_4 (a : SingularCochain X 0) (g : SingularCochain X 4)
    (hg : coboundaryₗ X 4 g = 0) :
    coboundaryₗ X 4 (cup a g) = cup (coboundaryₗ X 0 a) g := by
  funext τ
  show coboundary X (0 + 4) (cup a g) τ = cup (coboundaryₗ X 0 a) g τ
  rw [coboundary_cup, cup_apply]
  have hg' : coboundary X 4 g (backSmall τ) = 0 := congrFun hg (backSmall τ)
  rw [hg', mul_zero, add_zero]
  rfl

/-- **Coboundary ⌣ cocycle is a coboundary** (left argument, degrees `1,3`): `δa ⌣ g = δ(a ⌣ g)` for
`a : C¹`, `g : C³` a cocycle. The `(1,3)` mirror of `cup_coboundary_left_deg0`, cast-free
(`(1+3)+1 = 5 = 2+3` and `frontBig`/`backBig` at split `(1,3)` are definitionally the `frontFace`/
`backFace` of `cup _ g` at split `(2,3)`). The left descent the `H²` Wu class needs. -/
theorem cup_coboundary_left_1_3 (a : SingularCochain X 1) (g : SingularCochain X 3)
    (hg : coboundaryₗ X 3 g = 0) :
    coboundaryₗ X (1 + 3) (cup a g) = cup (coboundaryₗ X 1 a) g := by
  funext τ
  show coboundary X (1 + 3) (cup a g) τ = cup (coboundaryₗ X 1 a) g τ
  rw [coboundary_cup, cup_apply]
  have hg' : coboundary X 3 g (backSmall τ) = 0 := congrFun hg (backSmall τ)
  rw [hg', mul_zero, add_zero]
  rfl

/-- The **left-argument bilinear packaging** of `relCupRightGeneralH`: `a ↦ (b ↦ a ⌣ b)` as a genuine
`ℤ/2`-linear map `ker δ_k → (Hᵐ(X,S) →ₗ Hᵏ⁺ᵐ(X,S))`, linear in the left cocycle `a` (cup is bilinear).
Generic in `(k, m)`; extracting it as a named def (elaborated once) keeps the downstream `liftQ` kill
proofs from defeq-expanding this map's `map_add'`/`map_smul'` fields (the whnf-blowup friction). -/
noncomputable def relCupLeftₗ {k m : ℕ} :
    LinearMap.ker (coboundaryₗ X k)
      →ₗ[ZMod 2] RelativeCohomology S m →ₗ[ZMod 2] RelativeCohomology S (k + m) where
  toFun a := relCupRightGeneralH a
  map_add' fc fc' := by
    ext x
    obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show relCupRightGeneralH (fc + fc') (Submodule.Quotient.mk gc)
      = relCupRightGeneralH fc (Submodule.Quotient.mk gc)
        + relCupRightGeneralH fc' (Submodule.Quotient.mk gc)
    rw [relCupRightGeneralH_mk, relCupRightGeneralH_mk, relCupRightGeneralH_mk,
      show relCupCocycleₗ (fc + fc') gc = relCupCocycleₗ fc gc + relCupCocycleₗ fc' gc from by
        apply Subtype.ext
        apply Subtype.ext
        simp only [relCupCocycleₗ_coe, Submodule.coe_add, cup_add_left]]
    exact Submodule.Quotient.mk_add _
  map_smul' c fc := by
    ext x
    obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show relCupRightGeneralH (c • fc) (Submodule.Quotient.mk gc)
      = c • relCupRightGeneralH fc (Submodule.Quotient.mk gc)
    rw [relCupRightGeneralH_mk, relCupRightGeneralH_mk,
      show relCupCocycleₗ (c • fc) gc = c • relCupCocycleₗ fc gc from by
        apply Subtype.ext
        apply Subtype.ext
        simp only [relCupCocycleₗ_coe, SetLike.val_smul, cup_smul_left]]
    exact Submodule.Quotient.mk_smul _ _ _

@[simp] theorem relCupLeftₗ_apply {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k))
    (y : RelativeCohomology S m) : relCupLeftₗ a y = relCupRightGeneralH a y := rfl

/-- **The `(1,4)` relative cup** `H¹(X) × H⁴(X,S) → H⁵(X,S)` — a genuine `ℤ/2`-bilinear map. Right
argument descends via `relCupRightGeneralH`; the left argument descends (`relCupLeftₗ`) because
`H¹`-coboundaries are killed by `cup_coboundary_left_0_4`. The `cup` field of the `(1,4)`
`LefschetzWuDatum`. -/
noncomputable def relCupH14 :
    Cohomology X 1 →ₗ[ZMod 2] RelativeCohomology S 4 →ₗ[ZMod 2] RelativeCohomology S 5 :=
  Submodule.liftQ _ relCupLeftₗ
    (by
      intro fc hfc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hfc
      rw [LinearMap.mem_ker]
      ext x
      obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.zero_apply, relCupLeftₗ_apply]
      show relCupRightGeneralH fc (RelativeCohomology.mk S 4 gc) = 0
      rw [relCupRightGeneralH_apply_mk, RelativeCohomology.mk_eq_zero_iff,
        show relCoboundaryRange S (1 + 4) = LinearMap.range (relCoboundaryₗ S 4) from rfl]
      rw [show coboundaryRange X 1 = LinearMap.range (coboundaryₗ X 0) from rfl] at hfc
      obtain ⟨α, hα⟩ := hfc
      refine ⟨relCupCochainₗ α gc.1, ?_⟩
      apply Subtype.ext
      rw [relCoboundaryₗ_coe, relCupCochainₗ_coe, relCupCocycleₗ_coe]
      show coboundaryₗ X 4 (cup α (gc.1 : SingularCochain X 4)) = cup fc.1 (gc.1 : SingularCochain X 4)
      rw [cup_coboundary_left_0_4 α _ ((relCoboundary_eq_zero_iff gc.1).mp
        (LinearMap.mem_ker.mp gc.2)), hα])

/-- The computation rule for `relCupH14` on representative cocycles. -/
@[simp] theorem relCupH14_mk_mk (fc : LinearMap.ker (coboundaryₗ X 1))
    (gc : LinearMap.ker (relCoboundaryₗ S 4)) :
    relCupH14 (Cohomology.mk X 1 fc) (RelativeCohomology.mk S 4 gc)
      = RelativeCohomology.mk S 5 (relCupCocycleₗ fc gc) := rfl

/-- **The `(2,3)` relative cup** `H²(X) × H³(X,S) → H⁵(X,S)` — a genuine `ℤ/2`-bilinear map. Left
argument descent kills `H²`-coboundaries via `cup_coboundary_left_1_3`. The `cup` field of the
`(2,3)` `LefschetzWuDatum`. -/
noncomputable def relCupH23 :
    Cohomology X 2 →ₗ[ZMod 2] RelativeCohomology S 3 →ₗ[ZMod 2] RelativeCohomology S 5 :=
  Submodule.liftQ _ relCupLeftₗ
    (by
      intro fc hfc
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hfc
      rw [LinearMap.mem_ker]
      ext x
      obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.zero_apply, relCupLeftₗ_apply]
      show relCupRightGeneralH fc (RelativeCohomology.mk S 3 gc) = 0
      rw [relCupRightGeneralH_apply_mk, RelativeCohomology.mk_eq_zero_iff,
        show relCoboundaryRange S (2 + 3) = LinearMap.range (relCoboundaryₗ S 4) from rfl]
      rw [show coboundaryRange X 2 = LinearMap.range (coboundaryₗ X 1) from rfl] at hfc
      obtain ⟨α, hα⟩ := hfc
      refine ⟨relCupCochainₗ α gc.1, ?_⟩
      apply Subtype.ext
      rw [relCoboundaryₗ_coe, relCupCochainₗ_coe, relCupCocycleₗ_coe]
      show coboundaryₗ X (1 + 3) (cup α (gc.1 : SingularCochain X 3))
        = cup fc.1 (gc.1 : SingularCochain X 3)
      rw [cup_coboundary_left_1_3 α _ ((relCoboundary_eq_zero_iff gc.1).mp
        (LinearMap.mem_ker.mp gc.2)), hα])

/-- The computation rule for `relCupH23` on representative cocycles. -/
@[simp] theorem relCupH23_mk_mk (fc : LinearMap.ker (coboundaryₗ X 2))
    (gc : LinearMap.ker (relCoboundaryₗ S 3)) :
    relCupH23 (Cohomology.mk X 2 fc) (RelativeCohomology.mk S 3 gc)
      = RelativeCohomology.mk S 5 (relCupCocycleₗ fc gc) := rfl

end SKEFTHawking.SingularRelativeCup
