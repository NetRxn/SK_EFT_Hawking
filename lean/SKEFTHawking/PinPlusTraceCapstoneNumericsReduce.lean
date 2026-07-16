/-
# Phase 5q.H close-out — THE CLASS-DRIVEN NUMERICS REDUCE: the Betti equalities fall to two-sided
# Lefschetz nondegeneracy; the Wu vanishing falls to per-class vanishing.

The MV'd supply row (`PinPlusTraceCapstoneSupplyMV.lean`) still carries five numeric residuals:
the two Betti equalities `dimeq14`/`dimeq23`, the two Lefschetz nondegeneracies
`nondeg14`/`nondeg23`, and the Wu vanishing `hwu`. This module converts the numeric content into
pure duality/spin content:

* **`finrank_eq_of_binondeg`** — a bilinear pairing of finite-dimensional spaces over a field
  that is nondegenerate ON BOTH SIDES forces equal dimensions (each side injects into the other's
  dual). Clean linear algebra, the engine of the reduction.
* **`dimeq14_of_binondeg` / `dimeq23_of_binondeg`** — at any pair `(X, S)` with a degree-5
  functional `μ`: the `(1,4)` (resp. `(2,3)`) Betti equality follows from the Lefschetz pairing's
  two-sided nondegeneracy + the finite-dimensionalities. So `dimeq14`/`dimeq23` are NOT independent
  atoms: the honest Poincaré–Lefschetz content is the TWO-SIDED nondegeneracy (of which the
  supply's `nondeg14`/`nondeg23` are the left halves), and the Betti equalities are its
  corollaries. Instantiated at the capstone by `capstone_dimeq14_of_flip`/`capstone_dimeq23_of_flip`
  — plug-in suppliers for the supply row's `dimeq` fields (findims read off the MV cover row).
* **`wuW2_eq_zero_of_wuClasses`** — the Wu vanishing `w₂(W) = v₂ + v₁² = 0` follows from the
  per-class vanishings `v₁ = 0` and `v₂ = 0` (the orientable + spin route the pin⁺ physics
  supplies; via the banked characterisation `wuW2_eq_zero_iff`). The `hwu` supplier for the spin
  sector — the deep residual becomes the two Wu-class vanishings on the trace, the shape the
  σ-cert transport arc (the ends' `PinPlusCertK` across the cover glue) must deliver.

**What this changes in the row's shape:** with these suppliers, an instantiator holding two-sided
nondegeneracy discharges `dimeq14`/`dimeq23` outright (no Betti computation), and an instantiator
holding the per-class Wu vanishings discharges `hwu`. The genuinely open numerics residual
narrows to: the two-sided nondegeneracy pair + the two Wu-class vanishings — all four pure
duality/spin statements on the constructed carrier.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneCohomologyMV
import SKEFTHawking.PinPlusTraceCapstoneMembraneWeld

open scoped Manifold
open Topology
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusKTSurgeryTrace
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCohomologyMV

namespace SKEFTHawking.PinPlusTraceCapstoneNumericsReduce

noncomputable section

/-! ## §1. The engine: two-sided nondegeneracy forces equal dimensions. -/

/-- **A two-sided-nondegenerate pairing of finite-dimensional spaces forces equal dimensions** —
each side injects into the other's dual, and a finite-dimensional space has the dimension of its
dual. The Betti-equality engine. -/
theorem finrank_eq_of_binondeg {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (B : V →ₗ[K] W →ₗ[K] K) (hl : Function.Injective ⇑B)
    (hr : Function.Injective ⇑B.flip) :
    Module.finrank K V = Module.finrank K W := by
  refine le_antisymm ?_ ?_
  · calc Module.finrank K V ≤ Module.finrank K (W →ₗ[K] K) :=
          LinearMap.finrank_le_finrank_of_injective hl
      _ = Module.finrank K W := Subspace.dual_finrank_eq
  · calc Module.finrank K W ≤ Module.finrank K (V →ₗ[K] K) :=
          LinearMap.finrank_le_finrank_of_injective hr
      _ = Module.finrank K V := Subspace.dual_finrank_eq

/-! ## §2. The Betti equalities from two-sided Lefschetz nondegeneracy. -/

variable {X : TopCat} {S : Set ↑X}

/-- **The `(1,4)` Betti equality from two-sided nondegeneracy**: if the `(1,4)` Lefschetz pairing
`(a, b) ↦ μ(a ∪ b)` is injective on both sides and both cohomologies are finite-dimensional, then
`dim H¹(X) = dim H⁴(X,S)`. The supply row's `dimeq14` field is NOT an independent numeric atom —
it is the corollary of the honest two-sided duality. -/
theorem dimeq14_of_binondeg (mu : RelativeCohomology S 5 →ₗ[ZMod 2] ZMod 2)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X 1))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S 4))
    (hl : Function.Injective ⇑((relCupH14 (X := X) (S := S)).compr₂ mu))
    (hr : Function.Injective ⇑((relCupH14 (X := X) (S := S)).compr₂ mu).flip) :
    Module.finrank (ZMod 2) (Cohomology X 1)
      = Module.finrank (ZMod 2) (RelativeCohomology S 4) :=
  haveI := findimAbs
  haveI := findimRel
  finrank_eq_of_binondeg ((relCupH14 (X := X) (S := S)).compr₂ mu) hl hr

/-- **The `(2,3)` Betti equality from two-sided nondegeneracy**: `dim H²(X) = dim H³(X,S)` from
the two-sided injectivity of the `(2,3)` Lefschetz pairing. -/
theorem dimeq23_of_binondeg (mu : RelativeCohomology S 5 →ₗ[ZMod 2] ZMod 2)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X 2))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S 3))
    (hl : Function.Injective ⇑((relCupH23 (X := X) (S := S)).compr₂ mu))
    (hr : Function.Injective ⇑((relCupH23 (X := X) (S := S)).compr₂ mu).flip) :
    Module.finrank (ZMod 2) (Cohomology X 2)
      = Module.finrank (ZMod 2) (RelativeCohomology S 3) :=
  haveI := findimAbs
  haveI := findimRel
  finrank_eq_of_binondeg ((relCupH23 (X := X) (S := S)).compr₂ mu) hl hr

/-! ## §3. The Wu vanishing from per-class vanishing (the spin-sector supplier). -/

/-- **The Wu vanishing from per-class vanishing**: `w₂(W) = v₂ + v₁² = 0` as soon as `v₁ = 0` and
`v₂ = 0` — the orientable + spin route the pin⁺ physics supplies (via the banked characterisation
`wuW2_eq_zero_iff : w₂ = 0 ↔ v₂ = v₁²`). The `hwu` supplier: the deep spin residual becomes the
two Wu-class vanishings on the trace. -/
theorem wuW2_eq_zero_of_wuClasses (P14 : LefschetzWuDatum X S 1 4 5)
    (P23 : LefschetzWuDatum X S 2 3 5) (h1 : wuClassW1 P14 = 0)
    (h2 : wuClassW2 P23 = 0) : wuW2 P14 P23 = 0 := by
  rw [wuW2_eq_zero_iff, h1, h2]
  simp

/-! ## §3b. The Wu vanishings from the honest Steenrod–Kronecker functional vanishings.

The Wu-class vanishings of §3 are themselves the Lefschetz-dual shadows of the two
**Steenrod–Kronecker functional vanishings** `⟨relSq¹ ·, [W,∂W]⟩ = 0` and `⟨relSq² ·, [W,∂W]⟩ = 0` —
the honest spin content the σ-cert transport (the ends' `PinPlusCertK` across the cover glue) must
deliver. This block routes `hwu` all the way down to those two functional vanishings: no Betti
computation, no `sqOp` gaming (the pins are `relSq¹`/`relSq²` wired concrete by `ofRelFund14`/`23`),
just the honest degree-`(1,4)`/`(2,3)` Wu functionals of the trace pair. Same spin collapse the
cylinder narrowed to (`PinPlusCylinderWAdmPinned.…ofClosedPDInteriorSpin`), now on the 5-dim trace. -/

/-- **A vanishing Wu functional forces a vanishing Wu class** — the Lefschetz-dual of `0` is `0`
(the perfect pairing `pairing P` is bijective and linear, so `wuClass P = pairing P⁻¹(wuFunctional P)`
lands on `0` exactly when the functional does). Generic over the datum. -/
theorem wuClass_eq_zero_of_wuFunctional {k nk n : ℕ} (P : LefschetzWuDatum X S k nk n)
    (h : wuFunctional P = 0) : wuClass P = 0 := by
  have hkey : pairing P (wuClass P) = wuFunctional P :=
    (Equiv.ofBijective _ (pairing_bijective P)).apply_symm_apply (wuFunctional P)
  apply (pairing_bijective P).injective
  rw [hkey, h, map_zero]

/-- **The spin collapse of the trace's `w₂(W)`** — if BOTH Lefschetz–Wu functionals of the trace
pair vanish (`⟨relSq¹ ·, [W,∂W]⟩ = 0` on `H⁴(W,∂W)` and `⟨relSq² ·, [W,∂W]⟩ = 0` on `H³(W,∂W)`) then
`wuW2 P₁₄ P₂₃ = 0`: both Wu classes vanish (`wuClass_eq_zero_of_wuFunctional`), so
`w₂(W) = v₂ + v₁² = 0 + 0² = 0`. Does NOT need the value of `v₁²` — the two vanishings close it. -/
theorem wuW2_eq_zero_of_wuFunctionals (P14 : LefschetzWuDatum X S 1 4 5)
    (P23 : LefschetzWuDatum X S 2 3 5) (h14 : wuFunctional P14 = 0) (h23 : wuFunctional P23 = 0) :
    wuW2 P14 P23 = 0 :=
  wuW2_eq_zero_of_wuClasses P14 P23 (wuClass_eq_zero_of_wuFunctional P14 h14)
    (wuClass_eq_zero_of_wuFunctional P23 h23)

/-- **Verification — no `sqOp` gaming (`(1,4)` leg).** The `(1,4)` Wu functional of the datum
assembled by `ofRelFund14` IS the honest Steenrod–Kronecker functional `μ ∘ relSq¹ = ⟨relSq¹ ·,
[W,∂W]⟩` (the `sqOp` pin is `relSq1` wired concrete, `mu` is the relative fundamental-class
functional). So `h14`'s hypothesis is the genuine `v₁(W)`-vanishing spin input, not a free pin. -/
theorem wuFunctional_ofRelFund14 (D : RelFundClassDatum (m := 3) S)
    (fa : FiniteDimensional (ZMod 2) (Cohomology X 1))
    (fr : FiniteDimensional (ZMod 2) (RelativeCohomology S 4))
    (nd : Function.Injective ⇑((relCupH14 (X := X) (S := S)).compr₂ D.mu))
    (de : Module.finrank (ZMod 2) (Cohomology X 1)
        = Module.finrank (ZMod 2) (RelativeCohomology S 4)) :
    wuFunctional (LefschetzWuDatum.ofRelFund14 D fa fr nd de) = D.mu.comp (relSq1 (n := 3)) := rfl

/-- **Verification — no `sqOp` gaming (`(2,3)` leg).** The `(2,3)` Wu functional of the `ofRelFund23`
datum IS `μ ∘ relSq² = ⟨relSq² ·, [W,∂W]⟩` (the `sqOp` pin is `relSq2` concrete). So `h23`'s
hypothesis is the genuine `v₂(W)`-vanishing spin input. -/
theorem wuFunctional_ofRelFund23 (D : RelFundClassDatum (m := 3) S)
    (fa : FiniteDimensional (ZMod 2) (Cohomology X 2))
    (fr : FiniteDimensional (ZMod 2) (RelativeCohomology S 3))
    (nd : Function.Injective ⇑((relCupH23 (X := X) (S := S)).compr₂ D.mu))
    (de : Module.finrank (ZMod 2) (Cohomology X 2)
        = Module.finrank (ZMod 2) (RelativeCohomology S 3)) :
    wuFunctional (LefschetzWuDatum.ofRelFund23 D fa fr nd de) = D.mu.comp relSq2 := rfl

/-! ## §4. The capstone-shaped plug-in suppliers for the supply row's `dimeq` fields. -/

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The capstone `dimeq14` supplier**: on the constructed capstone, the `(1,4)` Betti equality
falls to the flip (right-side) nondegeneracy on top of the supply row's own `nondeg14`, with the
finite-dimensionalities read off the MV cover row. Plug-in shape for
`CapstoneAmbientSupplyWeldedMV.dimeq14`. -/
theorem capstone_dimeq14_of_flip
    (hasClass :
      letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
      HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    (mv : CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d)
    (hl : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum.mu))
    (hr : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum.mu).flip) :
    Module.finrank (ZMod 2)
        (Cohomology (TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 1)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 4) :=
  dimeq14_of_binondeg
    (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d
      hasClass).toRelFundClassDatum.mu
    (CapstoneCohomologyMVDatum.toFindimAbs14 s t S hS φ hφ hφinj cd hseam d mv)
    (CapstoneCohomologyMVDatum.toFindimRel14 s t S hS φ hφ hφinj cd hseam d mv)
    hl hr

/-- **The capstone `dimeq23` supplier**: the `(2,3)` Betti equality from the flip nondegeneracy,
findims off the MV cover row. Plug-in shape for `CapstoneAmbientSupplyWeldedMV.dimeq23`. -/
theorem capstone_dimeq23_of_flip
    (hasClass :
      letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
      HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    (mv : CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d)
    (hl : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum.mu))
    (hr : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum.mu).flip) :
    Module.finrank (ZMod 2)
        (Cohomology (TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 2)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3) :=
  dimeq23_of_binondeg
    (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d
      hasClass).toRelFundClassDatum.mu
    (CapstoneCohomologyMVDatum.toFindimAbs23 s t S hS φ hφ hφinj cd hseam d mv)
    (CapstoneCohomologyMVDatum.toFindimRel23 s t S hS φ hφ hφinj cd hseam d mv)
    hl hr

/-- **The capstone `hwu` supplier from the two Steenrod–Kronecker functional vanishings** — the
σ-cert-transport-shaped plug-in for `CapstoneAmbientSupplyWeldedMV.hwu`. On the constructed capstone
the Wu obstruction `w₂(W) = 0` falls to the honest spin content: the vanishing of the two
Lefschetz–Wu functionals `⟨relSq¹ ·, [W,∂W]⟩` and `⟨relSq² ·, [W,∂W]⟩` of the 5-dim trace pair
`(W, ∂W)` (`hwf14`/`hwf23` — the shape the ends' `PinPlusCertK` transport across the cover glue must
deliver), the finite-dimensionalities read off the MV cover row. No Betti computation and no `sqOp`
gaming: the pins are the CONCRETE `relSq¹`/`relSq²` wired by `ofRelFund14`/`23` (`hwf14`/`hwf23` are
literally `μ ∘ relSq¹ = 0`/`μ ∘ relSq² = 0`, see `wuFunctional_ofRelFund14`/`23`), so these are the
genuine `v₁(W) = 0` / `v₂(W) = 0` spin inputs. This is the 5-dim trace analogue of the cylinder's
`PinPlusCylinderWAdmPinned.CylinderWAdmPinned.ofClosedPDInteriorSpin`. -/
theorem capstone_hwu_of_steenrodKronecker
    (hasClass :
      letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
      HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    (mv : CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d)
    (nondeg14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum.mu))
    (dimeq14 : Module.finrank (ZMod 2)
        (Cohomology (TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 1)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 4))
    (nondeg23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum.mu))
    (dimeq23 : Module.finrank (ZMod 2)
        (Cohomology (TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 2)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W) 3))
    (hwf14 : wuFunctional
      (LefschetzWuDatum.ofRelFund14
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d hasClass).toRelFundClassDatum
        (CapstoneCohomologyMVDatum.toFindimAbs14 s t S hS φ hφ hφinj cd hseam d mv)
        (CapstoneCohomologyMVDatum.toFindimRel14 s t S hS φ hφ hφinj cd hseam d mv)
        nondeg14 dimeq14) = 0)
    (hwf23 : wuFunctional
      (LefschetzWuDatum.ofRelFund23
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d hasClass).toRelFundClassDatum
        (CapstoneCohomologyMVDatum.toFindimAbs23 s t S hS φ hφ hφinj cd hseam d mv)
        (CapstoneCohomologyMVDatum.toFindimRel23 s t S hS φ hφ hφinj cd hseam d mv)
        nondeg23 dimeq23) = 0) :
    wuW2
      (LefschetzWuDatum.ofRelFund14
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d hasClass).toRelFundClassDatum
        (CapstoneCohomologyMVDatum.toFindimAbs14 s t S hS φ hφ hφinj cd hseam d mv)
        (CapstoneCohomologyMVDatum.toFindimRel14 s t S hS φ hφ hφinj cd hseam d mv)
        nondeg14 dimeq14)
      (LefschetzWuDatum.ofRelFund23
        (TraceRelFundLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d hasClass).toRelFundClassDatum
        (CapstoneCohomologyMVDatum.toFindimAbs23 s t S hS φ hφ hφinj cd hseam d mv)
        (CapstoneCohomologyMVDatum.toFindimRel23 s t S hS φ hφ hφinj cd hseam d mv)
        nondeg23 dimeq23) = 0 :=
  wuW2_eq_zero_of_wuFunctionals _ _ hwf14 hwf23

end

end SKEFTHawking.PinPlusTraceCapstoneNumericsReduce
