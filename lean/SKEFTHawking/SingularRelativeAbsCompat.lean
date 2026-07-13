/-
# Phase 5q.H (W-A item 1, compatibility legs) — the pair→absolute map and its cup / Sq¹ naturality

The **absolutification** (pair-restriction) map `j* : Hᵐ(X, S; ℤ/2) → Hᵐ(X; ℤ/2)`, `[a] ↦ [a]`, induced
by the inclusion of the relative cochain complex `Cᵐ(X,S) = relCochains ↪ Cᵐ(X)` (a relative cochain
IS an absolute cochain). It descends because the inclusion is a cochain map. The two naturality legs the
Poincaré–Lefschetz Wu tower consumes:

* **cup naturality** (`relToAbs_cup`): `j*(a ⌣ b) = a ⌣ j*(b)` — the absolutification of the relative
  cup `H^k(X) × H^m(X,S) → H^{k+m}(X,S)` is the absolute cup `H^k(X) × H^m(X) → H^{k+m}(X)`;
* **`Sq¹` naturality** (`relToAbs_relSq1`): `j*(relSq¹ x) = Sq¹(j* x)` — the absolutification intertwines
  the relative and absolute Bocksteins.

Both hold on the nose at the cochain level (the underlying cochains are literally equal), so they are
`rfl` after the computation rules. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`,
no new project axiom, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCup
import SKEFTHawking.SingularRelativeBockstein
import SKEFTHawking.SingularCupCapHomology

namespace SKEFTHawking.SingularRelativeAbsCompat

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularBockstein SKEFTHawking.SingularCupCapHomology
  SKEFTHawking.SingularRelativeCup SKEFTHawking.SingularRelativeBockstein

variable {X : TopCat} {S : Set X}

/-! ## §1. The absolutification map `Hᵐ(X,S) → Hᵐ(X)` -/

/-- A relative cocycle, forgotten to an absolute cocycle (`relCochains ↪ SingularCochain` on cocycles):
`a ↦ a` as a cochain, still a cocycle since `δ_rel a = 0 ⟺ δ a = 0`. -/
noncomputable def relToAbsCocycleₗ {m : ℕ} :
    LinearMap.ker (relCoboundaryₗ S m) →ₗ[ZMod 2] LinearMap.ker (coboundaryₗ X m) :=
  (((relCochains S m).subtype.comp (LinearMap.ker (relCoboundaryₗ S m)).subtype)).codRestrict
    (LinearMap.ker (coboundaryₗ X m))
    (fun a => (relCoboundary_eq_zero_iff a.1).mp (LinearMap.mem_ker.mp a.2))

@[simp] theorem relToAbsCocycleₗ_coe {m : ℕ} (a : LinearMap.ker (relCoboundaryₗ S m)) :
    ((relToAbsCocycleₗ a : LinearMap.ker (coboundaryₗ X m)) : SingularCochain X m) = a.1.1 := rfl

/-- **The absolutification / pair-restriction map** `j* : Hᵐ(X, S) → Hᵐ(X)`, `[a] ↦ [a]`. Well-defined:
`relToAbsCocycleₗ` carries relative cocycles to absolute cocycles, and relative coboundaries (`δ_rel β`)
to absolute coboundaries (`δ β`). The forgetful leg of the long exact sequence of the pair. -/
noncomputable def relToAbs {m : ℕ} : RelativeCohomology S m →ₗ[ZMod 2] Cohomology X m :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp relToAbsCocycleₗ)
    (by
      intro a ha
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
      cases m with
      | zero =>
          rw [show relCoboundaryRange S 0 = (⊥ : Submodule (ZMod 2) (relCochains S 0)) from rfl,
            Submodule.mem_bot] at ha
          rw [show coboundaryRange X 0 = (⊥ : Submodule (ZMod 2) (SingularCochain X 0)) from rfl,
            Submodule.mem_bot]
          rw [show ((relToAbsCocycleₗ a : LinearMap.ker (coboundaryₗ X 0)) : SingularCochain X 0)
              = a.1.1 from rfl, show a.1 = 0 from ha]
          rfl
      | succ j =>
          rw [show relCoboundaryRange S (j + 1) = LinearMap.range (relCoboundaryₗ S j) from rfl] at ha
          rw [show coboundaryRange X (j + 1) = LinearMap.range (coboundaryₗ X j) from rfl]
          obtain ⟨β, hβ⟩ := ha
          refine ⟨β.1, ?_⟩
          rw [relToAbsCocycleₗ_coe]
          have := congrArg Subtype.val hβ
          rwa [relCoboundaryₗ_coe] at this)

@[simp] theorem relToAbs_mk {m : ℕ} (a : LinearMap.ker (relCoboundaryₗ S m)) :
    relToAbs (RelativeCohomology.mk S m a) = Cohomology.mk X m (relToAbsCocycleₗ a) := rfl

/-! ## §2. Cup naturality: `j*(a ⌣ b) = a ⌣ j*(b)` -/

/-- **The absolutification commutes with the cup** (generic `(k, m)`): the pair-restriction of the
relative cup `a ⌣ b ∈ Hᵏ⁺ᵐ(X,S)` (with `a ∈ Hᵏ(X)` a fixed cocycle, `b ∈ Hᵐ(X,S)`) is the absolute
cup `a ⌣ j*(b) ∈ Hᵏ⁺ᵐ(X)`. Holds on the nose (the underlying cochains are literally `cup a.1 b.1`).
This is the compatibility with pair restriction that `LefschetzWuDatum.cup` consumes. -/
theorem relToAbs_cup {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k)) (y : RelativeCohomology S m) :
    relToAbs (relCupRightGeneralH a y) = cupRightGeneralH a (relToAbs y) := by
  obtain ⟨gc, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [relCupRightGeneralH_mk]
  show relToAbs (RelativeCohomology.mk S (k + m) (relCupCocycleₗ a gc))
    = cupRightGeneralH a (relToAbs (RelativeCohomology.mk S m gc))
  rw [relToAbs_mk, relToAbs_mk, cupRightGeneralH_apply_mk]
  rfl

/-! ## §3. `Sq¹` naturality: `j*(relSq¹ x) = Sq¹(j* x)` -/

/-- **The absolutification intertwines the relative and absolute Bocksteins**: `j*(relSq¹ x) = Sq¹(j* x)`
for `x ∈ Hⁿ⁺¹(X,S)`. Holds on the nose (both sides are `[Sq1cochain x]`). This is the compatibility with
pair restriction (and with the absolute `Sq¹`) that `LefschetzWuDatum.sqOp` consumes. -/
theorem relToAbs_relSq1 {n : ℕ} (x : RelativeCohomology S (n + 1)) :
    relToAbs (relSq1 x) = Sq1 (relToAbs x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show relToAbs (relSq1 (RelativeCohomology.mk S (n + 1) a))
    = Sq1 (relToAbs (RelativeCohomology.mk S (n + 1) a))
  rw [relSq1_apply, relToAbs_mk, relToAbs_mk]
  show Cohomology.mk X (n + 1 + 1) (relToAbsCocycleₗ (relSq1cocycle a))
    = Sq1 (Submodule.Quotient.mk (relToAbsCocycleₗ a))
  rw [Sq1_apply]
  rfl

end SKEFTHawking.SingularRelativeAbsCompat
