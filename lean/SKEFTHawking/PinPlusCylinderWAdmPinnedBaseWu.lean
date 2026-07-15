/-
# Phase 5q.H W-A arm 4 — the spin-collapse reduction of the cylinder `hwu` and the sharp
# suspension residual

The `hwu` residual of `CylinderWAdmPinned M` is (`…Triage.hwu_iff_wuFormula`) the cylinder Wu formula
`v₂(W) = v₁(W)²` for `W = M × [0,1]`. The FULL `M`-intrinsic reduction (`v₂(W), v₁(W)² ←` `M`'s own
Wu/`w₂` data) needs a Steenrod-square SUSPENSION naturality — `Sq` commuting with the pair-suspension
isos `Hᵏ(W,∂W) ≅ Hᵏ⁻¹(M)`. This module does the part of that reduction that is **honestly provable now**
and names the residual sharply.

## Two routes triaged; the sharp wall

* **Route (b) — pair-restriction naturality — is DEAD for the cylinder.** `relToAbs = j*` (the
  `Hⁿ(W,∂W) → Hⁿ(W)` leg of the pair LES) is the **zero** map in the relevant degrees `n = 3,4,5`:
  each boundary slice `M × {0} ↪ W` is a homotopy equivalence, so `i* : Hⁿ(W) → Hⁿ(∂W)` is injective
  (the diagonal), forcing `im j* = ker i* = 0`. Hence the pair-restriction naturality
  `SingularRelativeSteenrodSq2.relToAbs_relSq2` (`j*(relSq² x) = Sq²(j* x)`) is **vacuous** on the
  cylinder (`0 = Sq² 0`), and cannot determine `relSq²` from the absolute `Sq²`. The whole content
  lives on the connecting/suspension leg — route (a), a Künneth/Cartan-level foundation not built here.

* **Route (a) residual is isolated to a single vanishing.** Rather than force the suspension iso, this
  module reduces the class-level Wu formula `v₂(W) = v₁(W)²` to the **vanishing of the two relative
  Steenrod–Kronecker functionals** `⟨relSq¹ ·, [W,∂W]⟩` and `⟨relSq² ·, [W,∂W]⟩` — the honest
  spin-type input. Under the (still-missing) pair-suspension iso these are exactly `⟨Sq¹·, [M]⟩` and
  `⟨Sq² ·, [M]⟩`, whose vanishing is `v₁(M) = 0` / `v₂(M) = 0`. So the residual is named precisely:
  `μ ∘ relSq¹ = 0 ⟺ v₁(M) = 0` and `μ ∘ relSq² = 0 ⟺ v₂(M) = 0` (the suspension compatibility of
  `⟨Sq ·, [·]⟩`), NOT faked.

## What this module banks (all kernel-pure, no `sorry`/axiom)

* **§1 — Lefschetz-dual algebra (general, any datum).** `wuClass_eq_zero_iff` — a Wu class vanishes iff
  its defining Wu functional vanishes (Lefschetz-dual of `0` is `0`, from the perfect pairing).
* **§2 — the spin collapse (general 5-pair).** `wuW2_eq_zero_of_wuFunctionals_zero` — if BOTH Wu
  functionals vanish then `wuW2 P₁₄ P₂₃ = 0` (both `v₁`, `v₂` vanish, so `v₂ = 0 = 0² = v₁²`).
* **§3 — the honest cylinder Steenrod–Kronecker functionals.** `cylinder_wuFunctional14_eq` /
  `cylinder_wuFunctional23_eq`: the cylinder Wu functionals ARE `μ ∘ relSq¹` / `μ ∘ relSq²` (the pins
  are wired to the substrate by construction) — so §2's hypotheses are the honest spin condition.
* **§4 — the constructor refinement.** `CylinderWAdmPinned.ofClosedPDInteriorSpin` swaps the W-level Wu
  formula `hwu` for the two functional-vanishing hypotheses (the `M`-intrinsic-reducible spin input).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusCylinderWAdmPinnedTriage

open scoped Manifold
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.SingularGoodCompactCompactExcision

namespace SKEFTHawking.PinPlusCylinderWAdmPinned

noncomputable section

/-! ## §1. Lefschetz-dual algebra: a Wu class vanishes iff its Wu functional vanishes -/

variable {X : TopCat} {S : Set X} {k nk n : ℕ}

/-- **The Lefschetz-dual of the zero functional is zero.** For any Poincaré–Lefschetz Wu datum, the
Wu class `v_k = wuClass P` is the perfect-pairing dual of the Wu functional `x ↦ ⟨Sq^k x, [W,∂W]⟩`;
since the pairing is bijective (and linear), `v_k = 0` exactly when that functional is `0`. -/
theorem wuClass_eq_zero_iff (P : LefschetzWuDatum X S k nk n) :
    wuClass P = 0 ↔ wuFunctional P = 0 := by
  have hkey : pairing P (wuClass P) = wuFunctional P :=
    (Equiv.ofBijective _ (pairing_bijective P)).apply_symm_apply (wuFunctional P)
  constructor
  · intro h
    rw [← hkey, h, map_zero]
  · intro h
    apply (pairing_bijective P).injective
    rw [hkey, h, map_zero]

/-- A vanishing Wu functional forces a vanishing Wu class (the ⟸ direction of `wuClass_eq_zero_iff`). -/
theorem wuClass_eq_zero_of_wuFunctional_zero (P : LefschetzWuDatum X S k nk n)
    (h : wuFunctional P = 0) : wuClass P = 0 :=
  (wuClass_eq_zero_iff P).mpr h

/-! ## §2. The spin collapse: both Wu functionals vanish ⟹ `wuW2 = 0` -/

/-- **The spin collapse of the `n = 5` Wu obstruction.** If both Lefschetz–Wu functionals vanish —
`⟨Sq¹ ·, [W,∂W]⟩ = 0` on `H⁴(W,∂W)` and `⟨Sq² ·, [W,∂W]⟩ = 0` on `H³(W,∂W)` — then `wuW2 P₁₄ P₂₃ = 0`.
Both Wu classes vanish (`§1`), so `w₂(W) = v₂ + v₁² = 0 + 0² = 0`. This is the honest general form of
the cylinder Wu formula's spin case: it does NOT need the value of `v₁²` — the two vanishings alone
close it. -/
theorem wuW2_eq_zero_of_wuFunctionals_zero (P₁₄ : LefschetzWuDatum X S 1 4 5)
    (P₂₃ : LefschetzWuDatum X S 2 3 5)
    (h14 : wuFunctional P₁₄ = 0) (h23 : wuFunctional P₂₃ = 0) :
    wuW2 P₁₄ P₂₃ = 0 := by
  have hv1 : wuClassW1 P₁₄ = 0 := wuClass_eq_zero_of_wuFunctional_zero P₁₄ h14
  have hv2 : wuClassW2 P₂₃ = 0 := wuClass_eq_zero_of_wuFunctional_zero P₂₃ h23
  rw [PoincareLefschetzWu5.wuW2_eq, hv1, hv2]
  simp

end

/-! ## §3–4. The honest cylinder Steenrod–Kronecker functionals and the spin constructor -/

section Cylinder

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

noncomputable section

omit [Nonempty M] in
/-- **The cylinder `(2,3)` Wu functional IS the honest Steenrod–Kronecker functional** `⟨relSq² ·,
[W,∂W]⟩ = μ ∘ relSq²`. The pins are wired to the substrate by construction (`cylinderP23.sqOp =
relSq2`, `cylinderP23.mu = (cylinderDatum hcls).mu`), so no free-`sqOp` gaming. Its vanishing is the
`M`-intrinsic-reducible `v₂(M) = 0` (via the pair-suspension iso, the named residual). -/
theorem cylinder_wuFunctional23_eq
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2)))
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of (cylW M)) 2))
    (findimRel : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3))
    (nondeg : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 2)
           = Module.finrank (ZMod 2)
             (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3)) :
    wuFunctional (cylinderP23 hcls findimAbs findimRel nondeg dimeq)
      = (cylinderDatum hcls).mu.comp relSq2 := rfl

omit [Nonempty M] in
/-- **The cylinder `(1,4)` Wu functional IS the honest Steenrod–Kronecker functional** `⟨relSq¹ ·,
[W,∂W]⟩ = μ ∘ relSq¹`. -/
theorem cylinder_wuFunctional14_eq
    (hcls : HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))
      (cylGen (M := M) (m' := 2)))
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1))
    (findimRel : FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4))
    (nondeg : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum hcls).mu))
    (dimeq : Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1)
           = Module.finrank (ZMod 2)
             (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4)) :
    wuFunctional (cylinderP14 hcls findimAbs findimRel nondeg dimeq)
      = (cylinderDatum hcls).mu.comp (relSq1 (n := 3)) := rfl

/-- **The spin-input `CylinderWAdmPinned` constructor.** Identical to `…Triage.ofClosedPDInterior`
except the W-level Wu formula `hwu : wuW2 P₁₄ P₂₃ = 0` is replaced by the two **Steenrod–Kronecker
functional vanishings** `hwf14`/`hwf23` (`⟨relSq¹ ·, [W,∂W]⟩ = 0` and `⟨relSq² ·, [W,∂W]⟩ = 0`, by
§3 the honest `μ ∘ relSq¹`/`μ ∘ relSq²`). This is the `M`-intrinsic-reducible spin input: under the
pair-suspension iso `Hᵏ(W,∂W) ≅ Hᵏ⁻¹(M)` these are `v₁(M) = 0` and `v₂(M) = 0`. The `hwu` field is
discharged by `wuW2_eq_zero_of_wuFunctionals_zero`. -/
def CylinderWAdmPinned.ofClosedPDInteriorSpin [PreconnectedSpace M]
    (findimM1 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1))
    (findimM2 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (nondeg14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu))
    (nondeg23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu))
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3))
    (hdetU : determinedByPoints (X := cylInteriorTop M) (2 + 1 + 2)
      (slabInInterior M))
    (hwf14 : wuFunctional
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs14 findimM1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base hM4 hM3)) nondeg14
        (cylinder_dimeq14_of_basePD hM3 basePD)) = 0)
    (hwf23 : wuFunctional
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M)) (cylinder_findimAbs23 findimM2)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base hM3 hM2)) nondeg23
        (cylinder_dimeq23_holds hM2)) = 0) :
    CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDInterior findimM1 findimM2 hM2 hM3 hM4 nondeg14 nondeg23 basePD hdetU
    (wuW2_eq_zero_of_wuFunctionals_zero _ _ hwf14 hwf23)

end

end Cylinder

end SKEFTHawking.PinPlusCylinderWAdmPinned
