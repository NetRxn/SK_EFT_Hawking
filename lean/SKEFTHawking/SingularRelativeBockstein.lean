/-
# Phase 5q.H (W-A item 1b) — the relative Steenrod square `Sq¹` on `Hⁿ(X, S; ℤ/2)`

The mod-2 Bockstein `Sq¹` on the cohomology of a pair `(X, S)`, realising the abstract `sqOp` field of
`PoincareLefschetzWu5.LefschetzWuDatum` at the `Sq¹` legs. The engine is the in-tree cochain Bockstein
`SingularBockstein.Sq1cochain a = half (δ₄ (lift a))`. The construction **relativizes cleanly**: the
`ℤ/4`-lift `lift` and the `ℤ/4`-coboundary `δ₄` are built from face maps, and `simplexIncl` commutes
with faces (`simplexIncl_face`), so on a subspace simplex `simplexIncl S n τ` a relative cochain's lift
vanishes, hence `δ₄(lift a)` vanishes there and `Sq1cochain a` annihilates the subspace subcomplex. The
subspace chains form a subcomplex, so both descent legs (cocycle→cocycle via `Sq1cochain_cocycle`;
well-definedness via a relative `Sq1cochain_coboundary` whose ℤ/4 defect cochain is itself relative)
respect the annihilator, giving `relSq1 : Hⁿ⁺¹(X,S) → Hⁿ⁺²(X,S)`.

## The `Sq²` situation (report for the `1d` `(2,3)` instance)

The `(2,3)` Wu-datum leg needs `Sq² : H³(X,S) → H⁵(X,S)` — a genuine degree-3 Steenrod square, NOT the
cup-square (`x ↦ x⌣x` is `Sqᵏ` only on `Hᵏ`; on `H³` the cup-square is `Sq³ : H³ → H⁶`). The project
has no general `Sq²` (only the `H²` cup-square `cupSquare2 : H² → H⁴ = Sq²|_{H²}`), so the `(2,3)`
`sqOp` is out of reach of the in-tree machinery — see the module report. This file delivers the `Sq¹`
side (the `(1,4)` leg's `sqOp = Sq¹ : H⁴(X,S) → H⁵(X,S)`).

All cohomology is the project's genuine singular ℤ/2 (co)homology. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularBockstein
import SKEFTHawking.SingularRelativeCohomologyMod2
import SKEFTHawking.SingularRelativeCup

namespace SKEFTHawking.SingularRelativeBockstein

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularBockstein SKEFTHawking.SingularRelativeCup

variable {X : TopCat} {S : Set X}

/-! ## §1. A relative cochain vanishing test and the `Sq¹`-annihilation -/

/-- A singular cochain that **vanishes on every subspace simplex** is a relative cochain (the converse
of `relCochain_vanish`): its Kronecker pairing against a subspace chain reduces, over the generators
`simplexIncl S n τ`, to values it kills. The reusable "pointwise-vanishing ⟹ relative" bridge. -/
theorem mem_relCochains_of_vanish {n : ℕ} (f : SingularCochain X n)
    (h : ∀ τ, f (simplexIncl S n τ) = 0) : f ∈ relCochains S n := by
  intro c hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero]; simp only [kronecker_apply, Finsupp.sum_zero_index]
  | add c₁ c₂ h₁ h₂ => rw [map_add, kronecker_add_right, h₁, h₂, add_zero]
  | single τ a' => rw [chainIncl_single, kronecker_single, h τ, mul_zero]

/-- The **ℤ/4-lift of a relative cochain vanishes on subspace simplices**: `lift a σ = ↑(a σ).val`, and
`a` kills subspace simplices (`relCochain_vanish`). -/
theorem relCochain_lift_vanish {n : ℕ} (a : relCochains S n)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n))) :
    lift (a : SingularCochain X n) (simplexIncl S n τ) = 0 := by
  rw [lift_apply, relCochain_vanish a τ]
  simp

/-- **`Sq1cochain` of a relative cochain vanishes on subspace simplices.** On `simplexIncl S (n+1) τ`
the `ℤ/4`-coboundary `δ₄(lift a)` is a signed sum of `lift a (face i (simplexIncl S (n+1) τ))
= lift a (simplexIncl S n (face i τ))` (`simplexIncl_face`), each `0` by `relCochain_lift_vanish`, so
`half 0 = 0`. -/
theorem relSq1cochain_vanish {n : ℕ} (a : relCochains S n)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (n + 1)))) :
    Sq1cochain (a : SingularCochain X n) (simplexIncl S (n + 1) τ) = 0 := by
  rw [Sq1cochain_apply]
  have h0 : coboundary4 X n (lift (a : SingularCochain X n)) (simplexIncl S (n + 1) τ) = 0 := by
    rw [coboundary4_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [← simplexIncl_face S n τ i, relCochain_lift_vanish a (face i τ), mul_zero]
  rw [h0, half_zero]

/-- **The `Sq¹`-annihilation**: `Sq1cochain a ∈ Cⁿ⁺¹(X,S)` whenever `a ∈ Cⁿ(X,S)`. The relative Bockstein
at cochain level lands in the relative cochains — `Sq¹` preserves the annihilator subcomplex. -/
theorem relSq1cochain_mem {n : ℕ} (a : relCochains S n) :
    Sq1cochain (a : SingularCochain X n) ∈ relCochains S (n + 1) :=
  mem_relCochains_of_vanish _ (relSq1cochain_vanish a)

/-! ## §2. The relative well-definedness leg -/

/-- **Relative Bockstein of a relative coboundary is a relative coboundary.** Mirrors
`SingularBockstein.Sq1cochain_coboundary`, but the ℤ/4 defect cochain `g` (whose `castHom` witnesses the
coboundary) is itself **relative**: on a subspace simplex both `lift(δβ)` and `δ₄(lift β)` vanish
(`β` relative), so `g` — and hence its mod-2 reduction — annihilates the subcomplex. This upgrades the
absolute preimage to a relative one, the extra fact the relative descent needs over the absolute one. -/
theorem relSq1cochain_coboundary {m : ℕ} (β : relCochains S m) :
    ∃ w : relCochains S (m + 1),
      coboundary X (m + 1) (w : SingularCochain X (m + 1))
        = Sq1cochain (coboundary X m (β : SingularCochain X m)) := by
  set b : SingularCochain X m := (β : SingularCochain X m) with hb_def
  set d : SingularCochain X (m + 1) := coboundaryₗ X m b with hd
  have hd_mem : d ∈ relCochains S (m + 1) := coboundary_mem_relCochains S m b β.2
  set g : Cochain4 X (m + 1) :=
    fun σ => ((half (lift d σ - coboundary4 X m (lift b) σ)).val : ZMod 4) with hg
  -- the same ℤ/4 defect identities as the absolute proof
  have hdefect : ∀ σ, lift d σ - coboundary4 X m (lift b) σ = 2 * g σ := by
    intro σ
    have heven : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
        (lift d σ - coboundary4 X m (lift b) σ) = 0 := by
      rw [map_sub, castHom_coboundary4_lift]
      rw [show (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (lift d σ) = d σ from castHom_lift d σ]
      rw [hd]; show coboundary X m b σ - coboundary X m b σ = 0; ring
    rw [hg]; rw [two_mul_half_val_of_even _ heven]
  have hcob : ∀ σ, coboundary4 X (m + 1) (lift d) σ = 2 * coboundary4 X (m + 1) g σ := by
    intro σ
    have hsub : lift d = coboundary4 X m (lift b) + fun σ => 2 * g σ := by
      funext σ; rw [Pi.add_apply]; rw [← hdefect σ]; ring
    rw [hsub, coboundary4_apply]
    simp only [Pi.add_apply]
    have hsplit : coboundary4 X (m + 1) (coboundary4 X m (lift b)) σ
        + ∑ i : Fin (m + 1 + 2), (-1 : ZMod 4) ^ (i : ℕ) * (2 * g (face i σ))
        = ∑ i : Fin (m + 1 + 2), (-1 : ZMod 4) ^ (i : ℕ) *
            (coboundary4 X m (lift b) (face i σ) + 2 * g (face i σ)) := by
      rw [coboundary4_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [← hsplit, coboundary4_comp_coboundary4 X m (lift b)]
    show (0 : ZMod 4) + _ = _
    rw [zero_add, coboundary4_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  -- the mod-2 defect cochain `castHom ∘ g` is relative: it vanishes on subspace simplices
  have hgrel : (fun τ => (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (g τ))
      ∈ relCochains S (m + 1) := by
    apply mem_relCochains_of_vanish
    intro τ
    have hd0 : lift d (simplexIncl S (m + 1) τ) = 0 :=
      relCochain_lift_vanish ⟨d, hd_mem⟩ τ
    have hb0 : coboundary4 X m (lift b) (simplexIncl S (m + 1) τ) = 0 := by
      rw [coboundary4_apply]
      apply Finset.sum_eq_zero
      intro i _
      rw [← simplexIncl_face S m τ i, relCochain_lift_vanish β (face i τ), mul_zero]
    show (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (g (simplexIncl S (m + 1) τ)) = 0
    rw [hg]
    simp only [hd0, hb0, sub_zero, half_zero, ZMod.val_zero, Nat.cast_zero, map_zero]
  refine ⟨⟨fun τ => (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (g τ), hgrel⟩, ?_⟩
  funext σ
  show coboundary X (m + 1) (fun τ => (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (g τ)) σ
      = Sq1cochain d σ
  rw [← castHom_coboundary4, Sq1cochain_apply, hcob, half_two_smul]

/-- **Cohomologous relative cocycles have cohomologous relative Bocksteins.** For relative cocycles
`a, a'` differing by a relative coboundary `δβ` (`β` relative), `Sq1cochain a − Sq1cochain a'` is a
relative coboundary: by `Sq1cochain_add`, it equals `Sq1cochain(δβ) + δ(a' ⌣₀ δβ)`; the first is a
relative coboundary (`relSq1cochain_coboundary`), the second is the relative coboundary of the relative
product cochain `a' ⌣₀ δβ` (relative because `a'` kills subspace simplices). The relative descent leg. -/
theorem relSq1cochain_sub_mem_range {m : ℕ} (a a' : relCochains S (m + 1))
    (ha' : coboundaryₗ X (m + 1) (a' : SingularCochain X (m + 1)) = 0) (β : relCochains S m)
    (hβ : relCoboundaryₗ S m β = a - a') :
    ∃ w : relCochains S (m + 1), coboundary X (m + 1) (w : SingularCochain X (m + 1))
      = Sq1cochain (a : SingularCochain X (m + 1)) - Sq1cochain (a' : SingularCochain X (m + 1)) := by
  have hβ_coe : coboundary X m (β : SingularCochain X m)
      = (a : SingularCochain X (m + 1)) - (a' : SingularCochain X (m + 1)) := by
    have := congrArg (Subtype.val) hβ
    rwa [relCoboundaryₗ_coe, AddSubgroupClass.coe_sub] at this
  have hcc : coboundaryₗ X (m + 1) (coboundary X m (β : SingularCochain X m)) = 0 :=
    congrFun (by funext g; exact coboundary_comp_coboundary X m g) β.1
  have hac : (a : SingularCochain X (m + 1))
      = (a' : SingularCochain X (m + 1)) + coboundary X m (β : SingularCochain X m) := by
    rw [hβ_coe]; abel
  obtain ⟨w1, hw1⟩ := relSq1cochain_coboundary β
  have hprod_rel :
      (fun τ => (a' : SingularCochain X (m + 1)) τ * coboundary X m (β : SingularCochain X m) τ)
        ∈ relCochains S (m + 1) := by
    apply mem_relCochains_of_vanish
    intro τ
    rw [relCochain_vanish a' τ, zero_mul]
  refine ⟨w1 + ⟨_, hprod_rel⟩, ?_⟩
  have hlin : coboundary X (m + 1) ((w1 : SingularCochain X (m + 1))
        + fun τ => (a' : SingularCochain X (m + 1)) τ * coboundary X m (β : SingularCochain X m) τ)
      = coboundary X (m + 1) (w1 : SingularCochain X (m + 1))
        + coboundary X (m + 1)
          (fun τ => (a' : SingularCochain X (m + 1)) τ * coboundary X m (β : SingularCochain X m) τ) :=
    map_add (coboundaryₗ X (m + 1)) _ _
  show coboundary X (m + 1) ((w1 : SingularCochain X (m + 1))
      + fun τ => (a' : SingularCochain X (m + 1)) τ * coboundary X m (β : SingularCochain X m) τ)
    = Sq1cochain (a : SingularCochain X (m + 1)) - Sq1cochain (a' : SingularCochain X (m + 1))
  rw [hlin, hw1, hac, Sq1cochain_add (a' : SingularCochain X (m + 1))
    (coboundary X m (β : SingularCochain X m)) ha' hcc]
  abel

/-! ## §3. The relative Bockstein `Sq¹ : Hⁿ⁺¹(X,S) → Hⁿ⁺²(X,S)` -/

/-- The **relative Bockstein cocycle**: `Sq1cochain a` packaged as a relative `(n+2)`-cocycle (relative
by `relSq1cochain_mem`, cocycle by `Sq1cochain_cocycle`). Naming it (elaborated once) keeps the
quotient-descent and additivity proofs from defeq-expanding the inline cocycle proof (whnf-blowup). -/
noncomputable def relSq1cocycle {n : ℕ} (a : LinearMap.ker (relCoboundaryₗ S (n + 1))) :
    LinearMap.ker (relCoboundaryₗ S (n + 1 + 1)) :=
  ⟨⟨Sq1cochain a.1.1, relSq1cochain_mem a.1⟩,
    (relCoboundary_eq_zero_iff _).mpr
      (Sq1cochain_cocycle a.1.1 ((relCoboundary_eq_zero_iff a.1).mp (LinearMap.mem_ker.mp a.2)))⟩

@[simp] theorem relSq1cocycle_coe {n : ℕ} (a : LinearMap.ker (relCoboundaryₗ S (n + 1))) :
    ((relSq1cocycle a : LinearMap.ker (relCoboundaryₗ S (n + 1 + 1))) : SingularCochain X (n + 1 + 1))
      = Sq1cochain a.1.1 := rfl

/-- The underlying set-function of the relative Bockstein: `[a] ↦ [Sq1cochain a]` on `Hⁿ⁺¹(X,S)`.
Well-defined by `relSq1cocycle` (lands in relative cocycles) and `relSq1cochain_sub_mem_range` (kills
the difference of cohomologous relative cocycles). Mirrors `SingularBockstein.Sq1fun` over the
annihilator subcomplex. -/
noncomputable def relSq1fun {n : ℕ} (x : RelativeCohomology S (n + 1)) :
    RelativeCohomology S (n + 1 + 1) := by
  refine Quotient.liftOn' x
    (fun a => RelativeCohomology.mk S (n + 1 + 1) (relSq1cocycle a)) ?_
  rintro a a' hrel
  rw [Submodule.quotientRel_def] at hrel
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub] at hrel
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  rw [show relCoboundaryRange S (n + 1 + 1) = LinearMap.range (relCoboundaryₗ S (n + 1)) from rfl]
  obtain ⟨β, hβ⟩ := hrel
  obtain ⟨w, hw⟩ := relSq1cochain_sub_mem_range a.1 a'.1
    ((relCoboundary_eq_zero_iff a'.1).mp (LinearMap.mem_ker.mp a'.2)) β hβ
  refine ⟨w, ?_⟩
  apply Subtype.ext
  rw [relCoboundaryₗ_coe, AddSubgroupClass.coe_sub, relSq1cocycle_coe, relSq1cocycle_coe]
  exact hw

@[simp] theorem relSq1fun_mk {n : ℕ} (a : LinearMap.ker (relCoboundaryₗ S (n + 1))) :
    relSq1fun (RelativeCohomology.mk S (n + 1) a)
      = RelativeCohomology.mk S (n + 1 + 1) (relSq1cocycle a) := rfl

/-! ## §4. `relSq¹` as a `ℤ/2`-linear map -/

/-- `relSq1fun` is **additive**: the `coboundary (a·b)` defect of `Sq1cochain_add` is the relative
coboundary of the relative product cochain `a ⌣₀ b` (relative because `a` kills subspace simplices),
hence vanishes in `Hⁿ⁺²(X,S)`. -/
theorem relSq1fun_add {n : ℕ} (x y : RelativeCohomology S (n + 1)) :
    relSq1fun (x + y) = relSq1fun x + relSq1fun y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show relSq1fun (RelativeCohomology.mk S (n + 1) (a + b))
      = relSq1fun (RelativeCohomology.mk S (n + 1) a) + relSq1fun (RelativeCohomology.mk S (n + 1) b)
  rw [relSq1fun_mk, relSq1fun_mk, relSq1fun_mk]
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
  erw [← Submodule.Quotient.mk_add]
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub, AddMemClass.coe_add]
  rw [show relCoboundaryRange S (n + 1 + 1) = LinearMap.range (relCoboundaryₗ S (n + 1)) from rfl]
  have hprod_rel : (fun τ => a.1.1 τ * b.1.1 τ) ∈ relCochains S (n + 1) := by
    apply mem_relCochains_of_vanish
    intro τ
    rw [relCochain_vanish a.1 τ, zero_mul]
  refine ⟨⟨_, hprod_rel⟩, ?_⟩
  apply Subtype.ext
  rw [relCoboundaryₗ_coe, AddSubgroupClass.coe_sub, AddSubmonoid.coe_add,
    relSq1cocycle_coe, relSq1cocycle_coe, relSq1cocycle_coe]
  show coboundary X (n + 1) (fun τ => a.1.1 τ * b.1.1 τ)
    = Sq1cochain (a.1.1 + b.1.1) - (Sq1cochain a.1.1 + Sq1cochain b.1.1)
  rw [Sq1cochain_add a.1.1 b.1.1 ((relCoboundary_eq_zero_iff a.1).mp (LinearMap.mem_ker.mp a.2))
    ((relCoboundary_eq_zero_iff b.1).mp (LinearMap.mem_ker.mp b.2))]
  abel

/-- `relSq1fun 0 = 0` — from additivity (`f 0 = f 0 + f 0`). -/
theorem relSq1fun_zero {n : ℕ} : relSq1fun (0 : RelativeCohomology S (n + 1)) = 0 := by
  have h := relSq1fun_add (0 : RelativeCohomology S (n + 1)) 0
  rw [add_zero] at h
  have h3 : relSq1fun (0 : RelativeCohomology S (n + 1)) + 0
      = relSq1fun (0 : RelativeCohomology S (n + 1)) + relSq1fun (0 : RelativeCohomology S (n + 1)) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h3).symm

/-- `relSq1fun` is **`ℤ/2`-scalar-linear**: scalars are `{0,1}`, so `c • x` is `0` (→ `relSq1fun_zero`)
or `x`. -/
theorem relSq1fun_smul {n : ℕ} (c : ZMod 2) (x : RelativeCohomology S (n + 1)) :
    relSq1fun (c • x) = c • relSq1fun x := by
  rcases (by decide +revert : c = 0 ∨ c = 1) with rfl | rfl
  · rw [zero_smul, zero_smul, relSq1fun_zero]
  · rw [one_smul, one_smul]

/-- **The relative mod-2 Bockstein `relSq¹ : Hⁿ⁺¹(X,S) →ₗ[ZMod 2] Hⁿ⁺²(X,S)`** — the genuine relative
cohomology operation, the relativization of `SingularBockstein.Sq1` over the annihilator subcomplex.
This realises the `sqOp = Sq¹` field of `PoincareLefschetzWu5.LefschetzWuDatum` (the `(1,4)` leg's
`Sq¹ : H⁴(X,S) → H⁵(X,S)` is `relSq¹` at `n = 3`). -/
noncomputable def relSq1 {X : TopCat} {S : Set X} {n : ℕ} :
    RelativeCohomology S (n + 1) →ₗ[ZMod 2] RelativeCohomology S (n + 1 + 1) where
  toFun := relSq1fun
  map_add' := relSq1fun_add
  map_smul' := relSq1fun_smul

/-- The computation rule for `relSq¹` on a representative relative cocycle. -/
@[simp] theorem relSq1_apply {n : ℕ} (a : LinearMap.ker (relCoboundaryₗ S (n + 1))) :
    relSq1 (RelativeCohomology.mk S (n + 1) a)
      = RelativeCohomology.mk S (n + 1 + 1) (relSq1cocycle a) := rfl

end SKEFTHawking.SingularRelativeBockstein
