/-
# Phase 5q.H Track 2 — the `.cls = crossH [M]` IDENTIFICATION (the opacity killer)

The cylinder Poincaré–Lefschetz `nondeg` residual (`…CylinderSuspDual.hproj{23,14}`) pairs cup classes
against the DATUM class `(cylinderDatum hcls).cls` — which, through `relFundClassDatumOf`, is the
`Classical.choose`-hidden `hcls.choose` (the existence witness), NOT literally the explicit
cross-product candidate `[W,∂W] = [M] × [I,∂I]`. This module KILLS that opacity.

## The mechanism — determinedness ⇒ uniqueness ⇒ identification

Two payoffs of the now-CLOSED interior determinedness `cylinder_hdet`
(`determinedByPoints 5 (interiorSlab M)`, `…PinPlusCylinderInteriorChart`):

* the DATUM class `(cylinderDatum hcls).cls` restricts to the cylinder interior generator `cylGen` at
  every interior point (its `.restricts` field — the `HasRelFundClass.choose_spec`);
* the explicit candidate `cylFundClassCandidate = crossH [M]` also restricts to `cylGen` everywhere
  (`cylFundClassCandidate_restricts`, reconstructed here from the same interior-local-Künneth
  nonvanishing `alphaU ≠ 0` route that discharged `hcls`: `restrictBd candidate = crossHloc([M]|σ)`,
  nonzero in the two-element `ℤ/2` interior local homology).

The relative fundamental class is UNIQUE given `cylinder_hdet` (`cylinderRelFundClass_unique_of_slab`:
two classes agreeing on the interior generator everywhere are equal — the collar-residual-free Wall 2).
Both classes restrict to `cylGen`, so they are EQUAL:

  **`cylinderDatum_cls_eq_crossH : (cylinderDatum (hasRelFundClass_cylGen …)).cls = cylFundClassCandidate`**

`cylFundClassCandidate = crossH (S := ∂W) (m'+1) [M]` is literally the honest product class
`[M] × [I,∂I]`. With this identification the datum functional `(cylinderDatum hcls).mu` reads as an
EXPLICIT relative-Kronecker pairing against `crossH [M]` (`cylinderDatum_mu_eq_crossH`) — so every
`[W,∂W]`-pairing in `hproj{23,14}` becomes a pairing against the explicit cross class, and downstream
cap-cross projection consumers can compute at the chain level.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PinPlusCylinderInteriorChart
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossRestrict
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalBridge
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderClsIdent

noncomputable section

/-! ## §1. The explicit candidate restricts to the interior generator (general `m'`) -/

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **The explicit cross candidate `[M] × [I,∂I]` restricts to the interior generator everywhere.**
Reconstructed from the same `alphaU ≠ 0` interior-local-Künneth route that discharged `hcls`: at every
interior point the candidate's boundary restriction is `crossHloc([M]|σ)`
(`restrictBd_candidate_eq_crossHloc`), nonzero by `crossHloc_ne_zero_of_alphaU_ne_zero` +
`alphaU_ne_zero`; a nonzero element of the two-element `ℤ/2` interior local homology IS the generator
(`restrictsToRelGen_candidate_of_ne_zero`). This is the standalone `RestrictsToRelGen` proof for the
EXPLICIT class the datum's `.restricts` hides behind `Classical.choose`. -/
theorem cylFundClassCandidate_restricts [T1Space (cylW M)] :
    RestrictsToRelGen (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m'))
      (cylFundClassCandidate (M := M) (m' := m')) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M))
  refine restrictsToRelGen_candidate_of_ne_zero (fun x hx => ?_)
  rw [restrictBd_candidate_eq_crossHloc x hx z hz.symm]
  exact crossHloc_ne_zero_of_alphaU_ne_zero x hx z hz.symm (alphaU_ne_zero x hx z hz.symm)

/-! ## §2. The identification `(cylinderDatum …).cls = crossH [M]` (m' = 2, the consumer degree) -/

variable {N : Type} [TopologicalSpace N] [T2Space N] [CompactSpace N] [Nonempty N]
  [PreconnectedSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) N] [T1Space (cylW N)]

/-- **The opacity killer: the datum class is the explicit cross class.** The `Classical.choose`-hidden
`(cylinderDatum (hasRelFundClass_cylGen)).cls` EQUALS the explicit product candidate
`cylFundClassCandidate = crossH [M] = [M] × [I,∂I]`. Both restrict to the cylinder interior generator
`cylGen` everywhere (the datum by its `.restricts` field, the candidate by
`cylFundClassCandidate_restricts`); the relative fundamental class is unique given the closed interior
determinedness `cylinder_hdet` (`cylinderRelFundClass_unique_of_slab`), so the two coincide. -/
theorem cylinderDatum_cls_eq_crossH :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := N))).cls
      = cylFundClassCandidate (M := N) (m' := 2) :=
  cylinderRelFundClass_unique_of_slab (cylGen (M := N) (m' := 2)) cylinder_hdet
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := N))).restricts
    cylFundClassCandidate_restricts

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderClsIdent
