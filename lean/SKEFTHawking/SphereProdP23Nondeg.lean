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

/-! ## §3. The base `S²` pairing — the top `H²(S²) × H⁰(S²) → ℤ/2` perfectness.

The 2-manifold analogue of `SingularPD4Instances.nondeg_of_closed`: for the closed charted surface
`S²`, the top fundamental functional `μ = ⟨·, [S²]⟩ : H²(S²;ℤ/2) → ℤ/2` is INJECTIVE — the honest
`H²(S²) ≅ ℤ/2` duality. Combined with `H⁰(S²) ≅ ℤ/2` (folded into `W' = ℤ/2`) this gives the perfect
base pairing `B'(a, c) = μ(a) · c` the intertwining transports. -/

open SKEFTHawking.SingularSurfaceIntersectionForm

/-- **`dim_{ℤ/2} H²(S²;ℤ/2) = 1`** — the exact rank of the 2-sphere's top cohomology, via the perfect
Kronecker pairing `kroneckerHEquiv 1 : H²(S²) ≃ (H₂(S²))^*` and `topSphereIso 1 : H₂(S²) ≃ ℤ/2`. -/
theorem finrank_twoSphere_cohomology_two :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of TwoSphere) (0 + 2)) = 1 := by
  rw [(SKEFTHawking.SingularKroneckerEquiv.kroneckerHEquiv (X := TopCat.of TwoSphere) 1).finrank_eq,
    Subspace.dual_finrank_eq, (SKEFTHawking.SingularLineMinusPoint.topSphereIso 1).finrank_eq,
    Module.finrank_self]

/-- **The `S²` top fundamental functional `μ = ⟨·, [S²]⟩ : H²(S²;ℤ/2) → ℤ/2` is injective** — the
2-manifold analogue of the closed-4-manifold `nondeg_of_closed` core. Injective because it is nonzero
(`surfaceFundamentalFunctional_ne_zero`) on a `1`-dimensional space
(`finrank_twoSphere_cohomology_two`): equal-finrank ⟹ injective ⟺ surjective, and a nonzero map into
`ℤ/2` is surjective. -/
theorem twoSphere_fundamentalFunctional_injective :
    Function.Injective ⇑(surfaceFundamentalFunctional (M := TwoSphere)) := by
  haveI : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of TwoSphere) (0 + 2)) :=
    SKEFTHawking.SingularMVCohomologyFinite.finiteDimensional_cohomology_of_homology
      (X := TopCat.of TwoSphere) 1 SKEFTHawking.SphereProdP23.finiteDimensional_twoSphere_homology_two
  rw [← LinearMap.ker_eq_bot]
  have hrn := LinearMap.finrank_range_add_finrank_ker (surfaceFundamentalFunctional (M := TwoSphere))
  rw [finrank_twoSphere_cohomology_two] at hrn
  have hne : LinearMap.range (surfaceFundamentalFunctional (M := TwoSphere)) ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot]; exact surfaceFundamentalFunctional_ne_zero
  have hpos : 0 < Module.finrank (ZMod 2)
      (LinearMap.range (surfaceFundamentalFunctional (M := TwoSphere))) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne)
  have hle : Module.finrank (ZMod 2)
      (LinearMap.range (surfaceFundamentalFunctional (M := TwoSphere)))
      ≤ Module.finrank (ZMod 2) (ZMod 2) := Submodule.finrank_le _
  rw [Module.finrank_self] at hle
  have hker0 : Module.finrank (ZMod 2)
      (LinearMap.ker (surfaceFundamentalFunctional (M := TwoSphere))) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hker0

/-- **The base `S²` pairing** `B'(a, c) = ⟨a, [S²]⟩ · c : H²(S²;ℤ/2) × ℤ/2 → ℤ/2`, with the second
argument the `ℤ/2` into which `H⁰(S²)` (spanned by the unit) is folded. Genuinely the top
Poincaré pairing of `S²` (the `[S²]` fundamental functional in the first slot). -/
def sphereBaseB : Cohomology (TopCat.of TwoSphere) (0 + 2) →ₗ[ZMod 2] ZMod 2 →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.lsmul (ZMod 2) (ZMod 2)).comp (surfaceFundamentalFunctional (M := TwoSphere))

@[simp] theorem sphereBaseB_apply (a : Cohomology (TopCat.of TwoSphere) (0 + 2)) (c : ZMod 2) :
    sphereBaseB a c = surfaceFundamentalFunctional (M := TwoSphere) a * c := rfl

/-- **The base `S²` pairing is left non-degenerate** — the 2-manifold analogue of
`SingularPD4Instances.nondeg_of_closed`. Injectivity in the first argument follows from injectivity of
the `[S²]` fundamental functional (`twoSphere_fundamentalFunctional_injective`): `B' a = 0` forces
`⟨a,[S²]⟩ = B' a 1 = 0`, hence `a = 0`. -/
theorem sphereBaseB_injective : Function.Injective ⇑sphereBaseB := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine (injective_iff_map_eq_zero _).mp twoSphere_fundamentalFunctional_injective a ?_
  have := LinearMap.congr_fun ha 1
  rwa [sphereBaseB_apply, mul_one, LinearMap.zero_apply] at this

/-! ## §5. The `(2,3)` `nondeg` reduction with the base `S²` pairing baked in.

The exact `S²×D³` mirror of `cylinder_nondeg23_of_intertwining` (whose base `nondeg_of_closed` is
baked). Only `(α, β, hcompat)` remain as inputs; the base pairing perfectness is consumed via
`sphereBaseB_injective`. The sole residual is the intertwining — cohomology `D³`-collapse (`α`), the
relative Künneth iso (`β`), and the `[D³,∂D³]` cup-Fubini `μ(a ∪ b) = ⟨α a ∪ β b, [S²]⟩` (`hcompat`). -/

/-- **The `S²×D³` `(2,3)` Lefschetz non-degeneracy, base pairing baked.** Given the intertwining
`α : H²(S²×D³) ≅ H²(S²)`, `β : H³(S²×D³,S²×S²) ≅ ℤ/2` (the folded `H⁰(S²)⊗H³(D³,∂D³)`), and the
cup-Fubini compatibility `μ(a ∪ b) = ⟨α a, [S²]⟩ · β b`, the sphereDisk `(2,3)` pairing is
left-non-degenerate. This is exactly the `nondeg` field
`PoincareLefschetzWuAssembly.LefschetzWuDatum.ofRelFund23` expects (once the intertwining lands),
mirroring the cylinder. -/
theorem sphereDiskNondeg23_of_intertwining
    (D : RelFundClassDatum (m := 3) (X := TopCat.of SphereDisk) sphereDiskBoundarySet)
    (α : Cohomology (TopCat.of SphereDisk) 2 ≃ₗ[ZMod 2] Cohomology (TopCat.of TwoSphere) (0 + 2))
    (β : RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3 ≃ₗ[ZMod 2] ZMod 2)
    (hcompat : ∀ (a : Cohomology (TopCat.of SphereDisk) 2)
        (b : RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3),
        D.mu (relCupH23 (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet) a b)
          = surfaceFundamentalFunctional (M := TwoSphere) (α a) * β b) :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet)).compr₂ D.mu) :=
  sphereProd_nondeg23_of_intertwining D sphereBaseB α β
    (fun a b => by rw [hcompat a b, sphereBaseB_apply]) sphereBaseB_injective

end

end SKEFTHawking.SphereProdP23Nondeg
