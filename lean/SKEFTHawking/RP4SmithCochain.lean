import Mathlib
import SKEFTHawking.RP4Transfer

/-!
# Phase 5q.G (B-arc, M3-a) — the cochain-level Smith transfer of the antipodal cover

The cochain dual of the M2 transfer: `τ^# : Cⁿ(S⁴) → Cⁿ(ℝP⁴)`, `(τ^#y)(σ) = y(σ₊) + y(σ₋)`
(sum over the two lifts). Together with the pullback `π^# = cochainPullback mkC` this opens the
**cohomological** Smith sequence, whose connecting map is the cup-ladder generator of
`H^*(ℝP⁴; ℤ/2)` (M3-c..i). The `δ`-commutation dualizes the M2-c face-pair combinatorics
(`face_pair_sum`): the faces of the two lifts are the two lifts of the faces, as a set.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4Covering SKEFTHawking.RP4Transfer
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.RP4SmithCochain

/-! ## §1. The cochain transfer and its `δ`-commutation -/

/-- **The cochain transfer** `τ^# : Cⁿ(S⁴) → Cⁿ(ℝP⁴)` — evaluate on both lifts and add. -/
noncomputable def cochainTransfer (n : ℕ) :
    SingularCochain (TopCat.of S4) n →ₗ[ZMod 2] SingularCochain (TopCat.of RP4) n where
  toFun y := fun σ => y (liftPlus σ) + y (liftMinus σ)
  map_add' y z := by
    funext σ
    show (y + z) (liftPlus σ) + (y + z) (liftMinus σ) = _
    simp only [Pi.add_apply]
    abel
  map_smul' c y := by
    funext σ
    show (c • y) (liftPlus σ) + (c • y) (liftMinus σ) = _
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem cochainTransfer_apply {n : ℕ} (y : SingularCochain (TopCat.of S4) n)
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    cochainTransfer n y σ = y (liftPlus σ) + y (liftMinus σ) := rfl

/-- **The face-pair value identity** — the cochain shadow of `face_pair_sum`: evaluating any
cochain on the two faces-of-lifts equals evaluating it on the two lifts-of-faces. -/
theorem face_pair_value {n : ℕ} (y : SingularCochain (TopCat.of S4) n)
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    y (face i (liftPlus σ)) + y (face i (liftMinus σ))
      = y (liftPlus (face i σ)) + y (liftMinus (face i σ)) := by
  have h := congrArg (Finsupp.linearCombination (ZMod 2) y) (face_pair_sum σ i)
  simpa only [map_add, Finsupp.linearCombination_single, one_smul] using h

/-- **The transfer is a cochain map**: `δ(τ^#y) = τ^#(δy)` — per-face, via `face_pair_value`. -/
theorem coboundary_cochainTransfer {n : ℕ} (y : SingularCochain (TopCat.of S4) n) :
    coboundary (TopCat.of RP4) n (cochainTransfer n y)
      = cochainTransfer (n + 1) (coboundary (TopCat.of S4) n y) := by
  funext σ
  show ∑ i : Fin (n + 2), (y (liftPlus (face i σ)) + y (liftMinus (face i σ)))
    = (∑ i : Fin (n + 2), y (face i (liftPlus σ)))
      + ∑ i : Fin (n + 2), y (face i (liftMinus σ))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => (face_pair_value y σ i).symm)

/-- The transfer of a cocycle is a cocycle. -/
theorem cochainTransfer_mem_ker {n : ℕ} (y : LinearMap.ker (coboundaryₗ (TopCat.of S4) n)) :
    cochainTransfer n y.1 ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP4) n) := by
  rw [LinearMap.mem_ker]
  show coboundary (TopCat.of RP4) n (cochainTransfer n y.1) = 0
  rw [coboundary_cochainTransfer,
    show coboundary (TopCat.of S4) n y.1 = coboundaryₗ (TopCat.of S4) n y.1 from rfl,
    LinearMap.mem_ker.mp y.2, map_zero]

/-- **The cohomology transfer** `τ^* : Hⁿ(S⁴) → Hⁿ(ℝP⁴)` — the descended cochain transfer
(mirrors `cohomologyPullback`'s descent shape). -/
noncomputable def cohomologyTransfer (n : ℕ) :
    Cohomology (TopCat.of S4) n →ₗ[ZMod 2] Cohomology (TopCat.of RP4) n :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((cochainTransfer n).domRestrict (LinearMap.ker (coboundaryₗ (TopCat.of S4) n))).codRestrict
        (LinearMap.ker (coboundaryₗ (TopCat.of RP4) n)) fun y => cochainTransfer_mem_ker y))
    (by
      intro y hy
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hy
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
      cases n with
      | zero =>
          have hy0 : (y.1 : SingularCochain (TopCat.of S4) 0) = 0 := by
            have h0 := hy
            rwa [show coboundaryRange (TopCat.of S4) 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
              Submodule.mem_bot] at h0
          rw [show coboundaryRange (TopCat.of RP4) 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
            Submodule.mem_bot, hy0, map_zero]
      | succ m =>
          obtain ⟨b, hb⟩ := hy
          refine ⟨cochainTransfer m b, ?_⟩
          show coboundaryₗ (TopCat.of RP4) m (cochainTransfer m b) = cochainTransfer (m + 1) y.1
          rw [show coboundaryₗ (TopCat.of RP4) m (cochainTransfer m b)
              = coboundary (TopCat.of RP4) m (cochainTransfer m b) from rfl,
            coboundary_cochainTransfer]
          rw [show coboundary (TopCat.of S4) m b = coboundaryₗ (TopCat.of S4) m b from rfl, hb])

/-- The computation rule for `cohomologyTransfer` on a representative cocycle. -/
@[simp] theorem cohomologyTransfer_mk {n : ℕ}
    (y : LinearMap.ker (coboundaryₗ (TopCat.of S4) n)) :
    cohomologyTransfer n (Cohomology.mk (TopCat.of S4) n y)
      = Cohomology.mk (TopCat.of RP4) n ⟨cochainTransfer n y.1, cochainTransfer_mem_ker y⟩ :=
  Submodule.liftQ_apply _ _ _

end SKEFTHawking.RP4SmithCochain
