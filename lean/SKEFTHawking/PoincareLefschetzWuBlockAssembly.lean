/-
# Phase 5q.H (W-A addClosure, layer 4 assembly) — the pinned union W-admissibility on the sum set

The capstone gluing all the disjoint-union Wu machinery: from two **pinned** Lefschetz–Wu pairs on the
summand pairs `(A, S₁)`, `(B, S₂)` (the `w₂ = 0` filters of `WAdmPinned b₁`, `WAdmPinned b₂`) plus the
**block-sum relative fundamental class** interface `SumRelFundClass` (the μ-block-sum residual,
layer 3), we assemble a pinned Lefschetz–Wu pair on the union pair `(A ⊔ B, S₁ ⊔ S₂)` with `w₂ = 0`.

Everything except the `SumRelFundClass` interface is discharged from the substrate: `cup`/`Sq` block
compatibility from the layer-2 naturality (`SingularRelativeCupSqNaturality`), `μ` block compatibility
from `SumRelFundClass.sumD_mu`, the `nondeg` field from `blockCup_injective`, the `dimeq` field from
`dimeq_block`, `w₂ = 0` from `wuW2_block_eq_zero`, and the pins from
`ofRelFund14_pinned`/`ofRelFund23_pinned`. This reduces the bordism-level `addClosure` to the
`SumRelFundClass` interface plus the (mechanical) `boundary_disjointUnion` datum transport onto
`∂(b₁.add b₂)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzWuBlock
import SKEFTHawking.SingularRelativeCupSqNaturality
import SKEFTHawking.PoincareLefschetzWuAssembly
import SKEFTHawking.PinPlusWAdmPinnedCore

namespace SKEFTHawking.PoincareLefschetzWuBlockAssembly

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularRelativeCohomologyDisjointSum
open SKEFTHawking.SingularRelativeCupSqNaturality
open SKEFTHawking.SingularRelativeCup SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.PoincareLefschetzWuBlock
open SKEFTHawking.PinPlusWAdmPinned

variable {A B : TopCat} {S₁ : Set ↑A} {S₂ : Set ↑B}

/-! ## §1. The `SumRelFundClass` interface — the block-sum relative fundamental class (layer-3 residual) -/

/-- The block-sum relative fundamental class of a disjoint union: from a relative fundamental class on
each summand pair, a relative fundamental class on the union pair whose functional is the **μ-block
sum** `⟨·, [W₁,∂W₁] ⊔ [W₂,∂W₂]⟩ = ⟨inl*·, [W₁,∂W₁]⟩ + ⟨inr*·, [W₂,∂W₂]⟩`. This bundles exactly the
one deep residual: the geometric additivity of the relative fundamental class over `⊔` (relative
homology `⊔`-additivity + local-homology excision at interior points; the relative analogue of
`SingularWuSumEmpty.fundamentalClass_sum_*`). -/
structure SumRelFundClass (A B : TopCat) (S₁ : Set ↑A) (S₂ : Set ↑B) where
  /-- the block-sum relative fundamental-class datum on the union pair. -/
  sumD : RelFundClassDatum (m := 3) S₁ → RelFundClassDatum (m := 3) S₂
      → RelFundClassDatum (m := 3) (sumSet A B S₁ S₂)
  /-- the μ of the block sum IS the block sum of the μ's (Kronecker-adjoint of the class `⊔`-sum). -/
  sumD_mu : ∀ (D₁ : RelFundClassDatum (m := 3) S₁) (D₂ : RelFundClassDatum (m := 3) S₂)
      (z : RelativeCohomology (sumSet A B S₁ S₂) 5),
      (sumD D₁ D₂).mu z
        = D₁.mu (relCohomPullback (inlMap A B) (mapsTo_inl A B S₁ S₂) 5 z)
          + D₂.mu (relCohomPullback (inrMap A B) (mapsTo_inr A B S₁ S₂) 5 z)

/-! ## §2. The assembly -/

/-- **The pinned union W-admissibility on the sum set** — the disjoint-union `addClosure` up to the
`boundary_disjointUnion` set transport. From pinned `(1,4)`/`(2,3)` Lefschetz–Wu data on each summand
with `w₂ = 0`, plus the `SumRelFundClass` interface, there is a pinned `(1,4)`/`(2,3)` pair on the
union pair with `w₂ = 0`. -/
theorem exists_wuAdmPinned_sum
    (sums : SumRelFundClass A B S₁ S₂)
    {P14₁ : LefschetzWuDatum A S₁ 1 4 5} {P23₁ : LefschetzWuDatum A S₁ 2 3 5}
    {P14₂ : LefschetzWuDatum B S₂ 1 4 5} {P23₂ : LefschetzWuDatum B S₂ 2 3 5}
    (pin14₁ : LefschetzWuPinned14 P14₁) (pin23₁ : LefschetzWuPinned23 P23₁)
    (pin14₂ : LefschetzWuPinned14 P14₂) (pin23₂ : LefschetzWuPinned23 P23₂)
    (hwu₁ : wuW2 P14₁ P23₁ = 0) (hwu₂ : wuW2 P14₂ P23₂ = 0) :
    ∃ (Pu14 : LefschetzWuDatum (sumSpace A B) (sumSet A B S₁ S₂) 1 4 5)
      (Pu23 : LefschetzWuDatum (sumSpace A B) (sumSet A B S₁ S₂) 2 3 5),
      LefschetzWuPinned14 Pu14 ∧ LefschetzWuPinned23 Pu23 ∧ wuW2 Pu14 Pu23 = 0 := by
  obtain ⟨D14₁, hD14₁⟩ := pin14₁.muPin
  obtain ⟨D14₂, hD14₂⟩ := pin14₂.muPin
  obtain ⟨D23₁, hD23₁⟩ := pin23₁.muPin
  obtain ⟨D23₂, hD23₂⟩ := pin23₂.muPin
  -- §2a. The `(1,4)` leg.
  have nd14 : Function.Injective
      ⇑((relCupH14 (X := sumSpace A B) (S := sumSet A B S₁ S₂)).compr₂ (sums.sumD D14₁ D14₂).mu) := by
    refine blockCup_injective
      (fun v y => relCohomPullback_relCupH14 (inlMap A B) (mapsTo_inl A B S₁ S₂) v y)
      (fun v y => relCohomPullback_relCupH14 (inrMap A B) (mapsTo_inr A B S₁ S₂) v y)
      (fun z => sums.sumD_mu D14₁ D14₂ z) ?_ ?_
    · rw [← pin14₁.cupPin, ← hD14₁]; exact P14₁.nondeg
    · rw [← pin14₂.cupPin, ← hD14₂]; exact P14₂.nondeg
  have de14 : Module.finrank (ZMod 2) (Cohomology (sumSpace A B) 1)
      = Module.finrank (ZMod 2) (RelativeCohomology (sumSet A B S₁ S₂) 4) := by
    haveI := P14₁.findimAbs; haveI := P14₂.findimAbs
    haveI := P14₁.findimRel; haveI := P14₂.findimRel
    exact dimeq_block P14₁.dimeq P14₂.dimeq
  set Pu14 := LefschetzWuDatum.ofRelFund14 (sums.sumD D14₁ D14₂)
    (finiteDimensional_cohomology_disjointSum A B 1 P14₁.findimAbs P14₂.findimAbs)
    (finiteDimensional_relCohomology_disjointSum A B S₁ S₂ 4 P14₁.findimRel P14₂.findimRel)
    nd14 de14 with hPu14
  -- §2b. The `(2,3)` leg.
  have nd23 : Function.Injective
      ⇑((relCupH23 (X := sumSpace A B) (S := sumSet A B S₁ S₂)).compr₂ (sums.sumD D23₁ D23₂).mu) := by
    refine blockCup_injective
      (fun v y => relCohomPullback_relCupH23 (inlMap A B) (mapsTo_inl A B S₁ S₂) v y)
      (fun v y => relCohomPullback_relCupH23 (inrMap A B) (mapsTo_inr A B S₁ S₂) v y)
      (fun z => sums.sumD_mu D23₁ D23₂ z) ?_ ?_
    · rw [← pin23₁.cupPin, ← hD23₁]; exact P23₁.nondeg
    · rw [← pin23₂.cupPin, ← hD23₂]; exact P23₂.nondeg
  have de23 : Module.finrank (ZMod 2) (Cohomology (sumSpace A B) 2)
      = Module.finrank (ZMod 2) (RelativeCohomology (sumSet A B S₁ S₂) 3) := by
    haveI := P23₁.findimAbs; haveI := P23₂.findimAbs
    haveI := P23₁.findimRel; haveI := P23₂.findimRel
    exact dimeq_block P23₁.dimeq P23₂.dimeq
  set Pu23 := LefschetzWuDatum.ofRelFund23 (sums.sumD D23₁ D23₂)
    (finiteDimensional_cohomology_disjointSum A B 2 P23₁.findimAbs P23₂.findimAbs)
    (finiteDimensional_relCohomology_disjointSum A B S₁ S₂ 3 P23₁.findimRel P23₂.findimRel)
    nd23 de23 with hPu23
  -- §2c. The block hypotheses.
  have H14 : WuBlockHyp Pu14 P14₁ P14₂ :=
    { cup_inl := fun v y => by
        rw [pin14₁.cupPin]; exact relCohomPullback_relCupH14 (inlMap A B) (mapsTo_inl A B S₁ S₂) v y
      cup_inr := fun v y => by
        rw [pin14₂.cupPin]; exact relCohomPullback_relCupH14 (inrMap A B) (mapsTo_inr A B S₁ S₂) v y
      mu := fun z => by
        rw [hD14₁, hD14₂]; exact sums.sumD_mu D14₁ D14₂ z
      sq_inl := fun y => by
        rw [pin14₁.sqPin]; exact relCohomPullback_relSq1 (inlMap A B) (mapsTo_inl A B S₁ S₂) y
      sq_inr := fun y => by
        rw [pin14₂.sqPin]; exact relCohomPullback_relSq1 (inrMap A B) (mapsTo_inr A B S₁ S₂) y }
  have H23 : WuBlockHyp Pu23 P23₁ P23₂ :=
    { cup_inl := fun v y => by
        rw [pin23₁.cupPin]; exact relCohomPullback_relCupH23 (inlMap A B) (mapsTo_inl A B S₁ S₂) v y
      cup_inr := fun v y => by
        rw [pin23₂.cupPin]; exact relCohomPullback_relCupH23 (inrMap A B) (mapsTo_inr A B S₁ S₂) v y
      mu := fun z => by
        rw [hD23₁, hD23₂]; exact sums.sumD_mu D23₁ D23₂ z
      sq_inl := fun y => by
        rw [pin23₁.sqPin]; exact relCohomPullback_relSq2 (inlMap A B) (mapsTo_inl A B S₁ S₂) y
      sq_inr := fun y => by
        rw [pin23₂.sqPin]; exact relCohomPullback_relSq2 (inrMap A B) (mapsTo_inr A B S₁ S₂) y }
  refine ⟨Pu14, Pu23, ?_, ?_, ?_⟩
  · rw [hPu14]; exact ofRelFund14_pinned (sums.sumD D14₁ D14₂) _ _ nd14 de14
  · rw [hPu23]; exact ofRelFund23_pinned (sums.sumD D23₁ D23₂) _ _ nd23 de23
  · exact wuW2_block_eq_zero H14 H23 hwu₁ hwu₂

end SKEFTHawking.PoincareLefschetzWuBlockAssembly
