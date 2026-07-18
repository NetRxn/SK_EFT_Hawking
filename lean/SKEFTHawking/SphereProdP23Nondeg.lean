/-
# Phase 5q.H — the `(2,3)` Lefschetz `nondeg` for `S²×D³` (P23): the intertwining reduction

The last of the four `ofRelFund23` numerics for the FIXED carrier `W = SphereDisk = S²×D³`,
`∂W = sphereDiskBoundarySet ≃ S²×S²` (the other three — `findimAbs`, `findimRel`, `dimeq` — are
banked in `SphereProdP23`). `nondeg` is the LEFT non-degeneracy of the Poincaré–Lefschetz pairing
`H²(S²×D³;ℤ/2) × H³(S²×D³,S²×S²;ℤ/2) → ℤ/2`, `(a,b) ↦ ⟨a ∪ b, [W,∂W]⟩` — injectivity of
`(relCupH23).compr₂ D.mu`.

## The reduction (mirror of the cylinder, `PoincareLefschetzRelFundClassCylinderNondeg`)

The `S²×D³` analogue of `cylinder_nondeg23_of_intertwining` (`D³ ≈` a "3-dim interval": contractible,
`∂D³ = S²`). Via the §2 iso-transport criterion
`PoincareLefschetzWuPairingCriterion.lefschetzPairing_injective_of_congr`, the sphereDisk `(2,3)`
non-degeneracy reduces to ONE intertwining datum `(α, β, hcompat)` plus a base pairing perfectness:

* `α : H²(S²×D³;ℤ/2) ≅ H²(S²;ℤ/2)` — the contractible-`D³`-factor collapse (cohomology side,
  `prodContractibleCohomologyEquiv`), banked here as `sphereDiskCollapseCohom`.
* `β : H³(S²×D³,S²×S²;ℤ/2) ≅ H⁰(S²;ℤ/2)` — the relative Künneth `H⁰(S²)⊗H³(D³,∂D³)` (the top
  `[D³,∂D³]` relative class, `H³(D³,∂D³;ℤ/2) = ℤ/2`).
* `hcompat : μ(a ∪ b) = ⟨α a ∪ β b, [S²]⟩` — the `[D³,∂D³]` cup-Fubini (the DEEP residual).

`sphereProd_nondeg23_of_intertwining` proves genuine injectivity from these inputs, consuming the base
`S²` pairing perfectness. `S²`'s own top pairing perfectness is the 2-manifold analogue of
`SingularPD4Instances.nondeg_of_closed`, supplied here from `SingularSurfaceIntersectionForm`
(`surfaceFundamentalFunctional_ne_zero` + `dim H²(S²) = 1`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SphereProdP23
import SKEFTHawking.PoincareLefschetzWuPairingCriterion
import SKEFTHawking.PoincareLefschetzWuAssembly
import SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
import SKEFTHawking.SingularCohomologyHomotopy
import SKEFTHawking.SingularSurfaceIntersectionForm

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PoincareLefschetzWuPairingCriterion
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.SingularCohomologyHomotopy
open SKEFTHawking.SingularProdContractibleInt (ProdSp)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularDiskAcyclic (Disk contraction slice_contraction_zero slice_contraction_one)

namespace SKEFTHawking.SphereProdP23Nondeg

noncomputable section

/-! ## §1. `α` — the contractible-`D³`-factor collapse on cohomology, `H²(S²×D³) ≅ H²(S²)`. -/

/-- **The contractible-factor cohomology collapse specialised to `SphereDisk`**:
`Hⁿ⁺¹(S²×D³;ℤ/2) ≅ Hⁿ⁺¹(S²;ℤ/2)`, the cohomology mirror of `sphereDiskCollapse` (homology), via the
`D³ = Disk 3` straight-line contraction (`prodContractibleCohomologyEquiv`, then `.symm` for the
`ProdSp → S²` variance). -/
def sphereDiskCollapseCohom (n : ℕ) :
    Cohomology (TopCat.of SphereDisk) (n + 1) ≃ₗ[ZMod 2] Cohomology (TopCat.of TwoSphere) (n + 1) :=
  sphereDisk_eq_prodSp ▸
    (prodContractibleCohomologyEquiv (TopCat.of TwoSphere) (Disk 3) ⟨0, by simp⟩
      (contraction (n := 3)) slice_contraction_zero slice_contraction_one n).symm

/-! ## §2. The `(2,3)` `nondeg` reduction via the intertwining. -/

/-- **The `S²×D³` `(2,3)` Lefschetz non-degeneracy, reduced to a named intertwining + base pairing.**
Given cohomology equivalences `α : H²(S²×D³) ≅ V'`, `β : H³(S²×D³,S²×S²) ≅ W'` intertwining the
sphereDisk pairing with a base pairing `B'` (`μ(a ∪ b) = B'(α a)(β b)`), left-injectivity of the base
pairing transports to the sphereDisk pairing. This is the honest reduction of the `(2,3)` `nondeg`
field of `PoincareLefschetzWuAssembly.LefschetzWuDatum.ofRelFund23` to the intertwining datum — the
`S²×D³` mirror of `PoincareLefschetzRelFundClassCylinderNondeg.cylinder_nondeg23_of_intertwining`. -/
theorem sphereProd_nondeg23_of_intertwining {V' W' : Type}
    [AddCommGroup V'] [Module (ZMod 2) V'] [AddCommGroup W'] [Module (ZMod 2) W']
    (D : RelFundClassDatum (m := 3) (X := TopCat.of SphereDisk) sphereDiskBoundarySet)
    (B' : V' →ₗ[ZMod 2] W' →ₗ[ZMod 2] ZMod 2)
    (α : Cohomology (TopCat.of SphereDisk) 2 ≃ₗ[ZMod 2] V')
    (β : RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3 ≃ₗ[ZMod 2] W')
    (hcompat : ∀ (a : Cohomology (TopCat.of SphereDisk) 2)
        (b : RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3),
        D.mu (relCupH23 (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet) a b)
          = B' (α a) (β b))
    (hB' : Function.Injective ⇑B') :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet)).compr₂ D.mu) :=
  lefschetzPairing_injective_of_congr D.mu
    (relCupH23 (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet)) B' α β hcompat hB'

end

end SKEFTHawking.SphereProdP23Nondeg
