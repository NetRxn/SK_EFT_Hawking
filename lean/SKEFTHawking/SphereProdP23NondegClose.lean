/-
# Route (c′) P5 — the `(2,3)` `nondeg` assembly by the DIRECT cap-injectivity argument

The `S²×D³` `(2,3)` Poincaré–Lefschetz non-degeneracy — `Function.Injective ((relCupH23).compr₂ D.mu)`
for the relative fundamental-class datum `D` — proven DIRECTLY, with NO `β`/`hcompat` intertwining
(no `[D³,∂D³]` cup-Fubini residual). The chain is P1→P4:

* the cap–connecting square (`SingularCapConnecting.connecting_capRelH`, P2) +
  `connecting_sphereDiskBoundary_ne_zero` (P1) + `eq_betaClass_of_ne_zero` (P3) +
  `capH21_sub_ne_zero` (P4) give the **cap detection** `a ≠ 0 ⟹ capRelH 2 2 a [W,∂W] ≠ 0`;
* the banked adjunction `SingularRelativeCupCap23.relKroneckerH_relCupH23`
  (`⟨a ∪ b, [W,∂W]⟩ = ⟨b, a ⌢ [W,∂W]⟩`) + the perfect relative Kronecker pairing
  (`SingularRelativeKroneckerEquiv.relKroneckerHEquiv`) turn the nonzero cap into a nonzero pairing
  functional, hence injectivity.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SphereProdP23Nondeg
import SKEFTHawking.SphereDiskConnectingDetect
import SKEFTHawking.SingularCapConnecting
import SKEFTHawking.SphereProdHFourMod2Detect
import SKEFTHawking.SphereProdCapDetect
import SKEFTHawking.SingularRelativeKroneckerEquiv
import SKEFTHawking.SingularRelativeCupCap23

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCapHomology
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SingularPairLES
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SphereDiskConnectingDetect
open SKEFTHawking.SphereProdHFourMod2Detect
open SKEFTHawking.SphereProdCapDetect
open SKEFTHawking.SingularRelativeKroneckerEquiv
open SKEFTHawking.SingularRelativeCupCap23

namespace SKEFTHawking.SphereProdP23NondegClose

/-- **The `(2,3)` `nondeg`, direct cap-injectivity argument (parametrized).** For any relative
fundamental-class datum `D` on `(S²×D³, S²×S²)` whose class is nonzero (`hcls`) and whose cohomology
restriction to the boundary is nonzero on nonzero classes (`hfeeder`), the sphereDisk `(2,3)` pairing
`(a,b) ↦ ⟨a ∪ b, [W,∂W]⟩` is left non-degenerate. No `β`/`hcompat` residual — the detection is the
P1→P4 cap chain + the perfect relative Kronecker pairing. -/
theorem sphereDiskNondeg23_direct
    [FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3)]
    (D : RelFundClassDatum (m := 3) (X := TopCat.of SphereDisk) sphereDiskBoundarySet)
    (hcls : D.cls ≠ 0)
    (hfeeder : ∀ a : Cohomology (TopCat.of SphereDisk) 2, a ≠ 0 →
        cohomologyPullback (SingularCapConnecting.inclC sphereDiskBoundarySet) 2 a ≠ 0) :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet)).compr₂ D.mu) := by
  -- (B) the cap detection: a ≠ 0 ⟹ capRelH 2 2 a D.cls ≠ 0
  have hcapdet : ∀ a : Cohomology (TopCat.of SphereDisk) 2, a ≠ 0 →
      capRelH 2 2 a D.cls ≠ 0 := by
    intro a ha hcap0
    have hg' := hfeeder a ha
    have hconn4 : connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 4 D.cls = betaClass :=
      eq_betaClass_of_ne_zero (connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 4 D.cls)
        (connecting_sphereDiskBoundary_ne_zero D.cls hcls)
    have hnat := SingularCapConnecting.connecting_capRelH (X := TopCat.of SphereDisk)
      sphereDiskBoundarySet a D.cls
    -- term-mode chain (avoids concrete-type `rw`/`apply` isDefEq blowup):
    --   capH 2 1 g' β = capH 2 1 g' (δ₄ cls) = δ₂ (a ⌢ cls) = δ₂ 0 = 0
    have hzero : capH 2 1 (cohomologyPullback (SingularCapConnecting.inclC sphereDiskBoundarySet) 2 a)
        betaClass = 0 :=
      (congrArg (fun z => capH 2 1
          (cohomologyPullback (SingularCapConnecting.inclC sphereDiskBoundarySet) 2 a) z)
        hconn4.symm).trans
        (hnat.symm.trans
          ((congrArg (fun w => connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2 w)
            hcap0).trans (map_zero _)))
    exact capH21_sub_ne_zero _ hg' hzero
  -- (C) the perfect-pairing finish + assembly
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hane
  apply hcapdet a hane
  refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (capRelH 2 2 a D.cls)).mp ?_
  intro φ
  obtain ⟨ω, rfl⟩ :=
    (relKroneckerHEquiv (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2).surjective φ
  exact (LinearMap.congr_fun (relKroneckerHEquiv_apply (X := TopCat.of SphereDisk)
      sphereDiskBoundarySet 2 ω) (capRelH 2 2 a D.cls)).trans
    ((relKroneckerH_relCupH23 a ω D.cls).symm.trans
      ((D.mu_apply (relCupH23 a ω)).symm.trans (LinearMap.congr_fun ha ω)))

end SKEFTHawking.SphereProdP23NondegClose
