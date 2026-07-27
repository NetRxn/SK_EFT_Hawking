/-
# Phase 5q.H close-out (#211) — THE FINAL `hBbord` P23 WIRING (K3-independent atom)

The last K3-independent atom of the 8-atom headline row
`PinPlusKTSphereProdCohomology.kt_equiv_zmod16_of_residuals_freezeAtoms_ofReducedAtoms`: the pinned
`(2,3)` Poincaré–Lefschetz datum + the middle-Wu vanishing `v₂ = 0`, both on the FIXED carrier
`W = SphereDisk = S²×D³` with boundary `∂W = sphereDiskBoundarySet ≃ S²×S²`.

Every piece is banked; this module ASSEMBLES them (kernel-pure, no `sorry`/axiom/`native_decide`/
`maxHeartbeats`):

* `sphereDiskPin23 : LefschetzWuPinned23 sphereDiskP23` — the concrete `(2,3)` datum
  (`SphereProdP23NondegClose.sphereDiskP23`, UNCONDITIONAL `ofRelFund23`-assembled) is substrate-pinned,
  via the generic non-vacuity engine `PinPlusWAdmPinned.ofRelFund23_pinned` fed the SAME four
  PL-duality numerics that assembled `sphereDiskP23` (`findimAbs`, `findimRel`, `nondeg`, `dimeq`).
* `sphereDiskWuZero : wuClass sphereDiskP23 = 0` — the middle Wu class vanishes, via the UNCONDITIONAL
  `SphereProdBoundaryCupSquare.sphereDiskWuClass23_eq_zero` (its `BoundaryCupSquareVanishes` feeder
  discharged in that module) fed `sphereDiskP23` and the pin's `sqOp = relSq2` certificate.

Together with the banked concrete coboundary bordism `sphereProdCoboundaryBordism`
(`PinPlusKTSphereProdReassoc`, `W := SphereDisk`, `J6 = (𝓡 4).prod (𝓡∂ 1)`), these discharge the
`(P23, pin23, hv2)` triple of `PinPlusKTSphereProdCohomology.sphereProdCoboundaryWAdm_of_reducedAtoms`.
The remaining reduced atoms (`hasClass = HasRelFundClass`, the two homology subsingletons) are the
OTHER lane (`PinPlusKTSphereProdHomologyRoots` / the rel-fund-class wall) — not this module's.
-/
import Mathlib
import SKEFTHawking.SphereProdP23NondegClose
import SKEFTHawking.SphereProdBoundaryCupSquare
import SKEFTHawking.PinPlusWAdmPinnedCore
import SKEFTHawking.PinPlusKTSphereProdCohomology
import SKEFTHawking.PinPlusKTSphereProdReassoc
import SKEFTHawking.PinPlusKTSphereProdRelFund
import SKEFTHawking.PinPlusKTSphereProdHomologyRoots
import SKEFTHawking.SphereProdHThreeMod2

open scoped Manifold
open SKEFTHawking.SphereProdP23NondegClose
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusKTSphereProdCohomology
open SKEFTHawking.PinPlusKTSphereProdBordism
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.BordismTheory
open SKEFTHawking.TangentialDataBordism
-- Mirror the consumer's `§4` open block so the K3-assembly residual names (`residualProv`,
-- `pinPlusCharPairData`, `charPairBrown`, `KRSResidualRow`, `SpinPresentationRow`, `spinForgetPhi`,
-- `ktKernelRep`, …) resolve identically to `PinPlusKTSphereProdCohomology`.
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairEmptySourceRealization
open SKEFTHawking.PinPlusKTSphereProdWAdm
open SKEFTHawking.PinPlusKTAssemblyResiduals
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTBinderDischarge
open SKEFTHawking.PinPlusKTCollapseDischarge
open SKEFTHawking.PinPlusKTFreezeDischarge
open SKEFTHawking.T2TangentialBordism

-- The `J6`-chart on `SphereDisk` (the `((𝓡 4).prod (𝓡∂ 1))` model-space atlas) is registered `local`
-- in `PinPlusKTSphereProdReassoc`; the `((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk` spelling of the
-- reduced-atoms hypotheses needs it as the `[ChartedSpace HC SphereDisk]` instance (precedent:
-- `SphereProdP23NondegClose.lean`).
attribute [local instance] SKEFTHawking.SpinSigmaRoute.chartW6

namespace SKEFTHawking.PinPlusKTSphereProdP23Close

noncomputable section

/-! ## §1. The two SphereDisk-concrete P23 facts. -/

/-- **`sphereDiskPin23`** — the concrete `S²×D³` `(2,3)` Lefschetz–Wu datum `sphereDiskP23` is
substrate-pinned (`μ` a genuine relative fundamental-class functional, `cup = relCupH23`,
`sqOp = relSq2`). Directly `ofRelFund23_pinned` at the SAME four numerics that assembled
`sphereDiskP23` — `sphereDiskP23` IS `ofRelFund23 sphereDiskRelFundDatum …`. -/
theorem sphereDiskPin23 : LefschetzWuPinned23 sphereDiskP23 :=
  ofRelFund23_pinned sphereDiskRelFundDatum
    SphereProdP23.sphereDisk_findimAbs23 SphereProdP23.sphereDisk_findimRel23
    sphereDiskNondeg23 sphereDiskDimeq23

/-- **`sphereDiskWuZero`** — the middle Wu class of the concrete `(2,3)` datum vanishes:
`wuClass sphereDiskP23 = 0`. Via the UNCONDITIONAL Wu-vanishing (boundary cup-square discharged),
fed the pin's `sqOp = relSq2` certificate. This is the geometric spin condition `v₂ = 0`. -/
theorem sphereDiskWuZero : wuClass sphereDiskP23 = 0 :=
  SphereProdBoundaryCupSquare.sphereDiskWuClass23_eq_zero sphereDiskP23 sphereDiskPin23.sqPin

/-! ## §2. Feeding the triple into the consumer — the P23 atom of `hBbord` closes. -/

/-- **The SphereDisk `(2,3)` triple transported to any spelling of the boundary set that is
propositionally `sphereDiskBoundarySet`.** The consumer states its `P23` on
`((𝓡 4).prod (𝓡∂ 1)).boundary b.W`; for the concrete coboundary bordism this is
`sphereDisk_boundary_eq`-equal to `sphereDiskBoundarySet`. A `subst`-based bridge keeps the datum, its
pin, and its Wu vanishing mutually consistent (robust against fragile dependent `▸` on the datum). -/
theorem sphereDiskP23Triple_of_boundary_eq {S : Set ↑(TopCat.of SphereDisk)}
    (hS : S = sphereDiskBoundarySet) :
    ∃ P23 : LefschetzWuDatum (TopCat.of SphereDisk) S 2 3 5,
      LefschetzWuPinned23 P23 ∧ wuClass P23 = 0 := by
  subst hS
  exact ⟨sphereDiskP23, sphereDiskPin23, sphereDiskWuZero⟩

/-- **THE P23-ATOM DISCHARGE.** `SphereProdCoboundaryWAdm` for the concrete `S²×S²` source
`⟨sphereProdSM4 0, str⟩`, with the whole `(P23, pin23, hv2)` triple of
`sphereProdCoboundaryWAdm_of_reducedAtoms` discharged by the banked concrete coboundary bordism
`sphereProdCoboundaryBordism 0` (`W = SphereDisk`, `J6 = (𝓡 4).prod (𝓡∂ 1)`) fed
`sphereDiskP23`/`sphereDiskPin23`/`sphereDiskWuZero`. The remaining hypotheses are exactly the NON-P23
reduced atoms — the class-existence witness `hasClass` and the two homology subsingletons (the
`PinPlusKTSphereProdHomologyRoots` / rel-fund-class lane) — so the K3-independent P23 half of `hBbord`
is closed. -/
theorem sphereProdCoboundaryWAdm_of_homologyAtoms {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (str : (spinEmptyData prov).Mfd (sphereProdSM4 k))
    (hasClass : letI := sphereDisk_t2Space.t1Space
      HasRelFundClass (X := TopCat.of SphereDisk)
        (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk)
        (interiorGenFamily (W := SphereDisk) ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    (hS1 : Subsingleton (Homology (TopCat.of SphereDisk) 1))
    (hS2 : Subsingleton (RelativeHomology (X := TopCat.of SphereDisk)
      (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk) 4)) :
    SphereProdCoboundaryWAdm prov ⟨sphereProdSM4 k, str⟩ := by
  haveI : Subsingleton (Homology (TopCat.of (sphereProdCoboundaryBordism k).W) 1) := hS1
  haveI : Subsingleton (RelativeHomology (X := TopCat.of (sphereProdCoboundaryBordism k).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (sphereProdCoboundaryBordism k).W) 4) := hS2
  obtain ⟨P23, pin23, hv2⟩ := sphereDiskP23Triple_of_boundary_eq
    (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (sphereProdCoboundaryBordism k).W) sphereDisk_boundary_eq
  exact sphereProdCoboundaryWAdm_of_reducedAtoms prov ⟨sphereProdSM4 k, str⟩
    (sphereProdCoboundaryBordism k) sphereDisk_t2Space hasClass P23 pin23 hv2

/-- **`hBbord` for the concrete `S²×S²` slot — the P23 triple GONE.** The empty-membrane collapse
(`hBbord_of_coboundary`) composed with the P23-atom discharge: the Freeze-B geometric witness
`IsDataBordant` for the concrete distinguished source `⟨sphereProdSM4 0, str⟩` follows from ONLY the
non-P23 reduced atoms (`hasClass` + the two homology subsingletons). The whole `(P23, pin23, hv2)`
triple — and the concrete coboundary bordism `b` and its `T2Space` — are discharged internally. -/
theorem isDataBordant_empty_ofHomologyAtoms {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (str : (spinEmptyData prov).Mfd (sphereProdSM4 k))
    (hasClass : letI := sphereDisk_t2Space.t1Space
      HasRelFundClass (X := TopCat.of SphereDisk)
        (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk)
        (interiorGenFamily (W := SphereDisk) ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    (hS1 : Subsingleton (Homology (TopCat.of SphereDisk) 1))
    (hS2 : Subsingleton (RelativeHomology (X := TopCat.of SphereDisk)
      (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk) 4)) :
    IsDataBordant (spinEmptyData prov) ⟨sphereProdSM4 k, str⟩
      ⟨emptySM, (spinEmptyData prov).emptyStr⟩ :=
  hBbord_of_coboundary prov ⟨sphereProdSM4 k, str⟩
    (sphereProdCoboundaryWAdm_of_homologyAtoms prov str hasClass hS1 hS2)

/-! ## §2b. FULLY-DISCHARGED geometric coboundary — every non-P23 atom is a PROVED sister node. -/

/-- **`SphereProdCoboundaryWAdm` for the concrete `S²×S²` slot from `str` ALONE.** All three
non-P23 reduced atoms are now proved sister nodes, so the WHOLE geometric coboundary content is
discharged: `hasClass` = `PinPlusKTSphereProdRelFund.hasRelFundClass_sphereDisk` (UNCONDITIONAL),
Root 1 = the `PinPlusKTSphereProdHomologyRoots` `Subsingleton (Homology (TopCat.of SphereDisk) 1)`
instance, Root 2 = the `SphereProdHThreeMod2` `rootTwo_subsingleton` instance transported across
`sphereDisk_boundary_eq`. The only surviving obligation for `hBbord` at this slot is the
row-realization (the distinguished slot IS `⟨sphereProdSM4 0, str⟩`). -/
theorem sphereProdCoboundaryWAdm_sphereDisk {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (str : (spinEmptyData prov).Mfd (sphereProdSM4 k)) :
    SphereProdCoboundaryWAdm prov ⟨sphereProdSM4 k, str⟩ :=
  sphereProdCoboundaryWAdm_of_homologyAtoms prov str
    PinPlusKTSphereProdRelFund.hasRelFundClass_sphereDisk
    inferInstance
    (sphereDisk_boundary_eq ▸ SphereProdHThreeMod2.rootTwo_subsingleton)

/-- **`hBbord` for the concrete `S²×S²` slot, geometric content fully discharged.** Same as
`isDataBordant_empty_ofHomologyAtoms` but with every geometric atom supplied by its proved sister
node — the Freeze-B witness follows from `str` alone. -/
theorem isDataBordant_empty_sphereDisk {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (str : (spinEmptyData prov).Mfd (sphereProdSM4 k)) :
    IsDataBordant (spinEmptyData prov) ⟨sphereProdSM4 k, str⟩
      ⟨emptySM, (spinEmptyData prov).emptyStr⟩ :=
  hBbord_of_coboundary prov ⟨sphereProdSM4 k, str⟩
    (sphereProdCoboundaryWAdm_sphereDisk prov str)

/-! ## §3. The K3-assembly headline variants — the P23 triple GONE from the `≃+ ZMod 16` / Rokhlin-16
rows. Every consumer shape is fixed EXCEPT the row-realization `hrow` (the distinguished slot IS the
concrete `S²×S²`, `⟨sphereProdSM4 0, str⟩`) + the two NON-P23 homology atoms. -/

/-- **THE REDUCED-ATOMS WIRING, P23 DISCHARGED** — `kt_equiv_zmod16_of_residuals_freezeAtoms` with the
Freeze-B coboundary atom supplied by the P23-atom discharge. Drops the whole `(b, hWT2, P23, pin23,
hv2)` block, retaining ONLY: the row-realization `hrow : row.R.s2s2 = ⟨sphereProdSM4 0, str⟩` and the
two NON-P23 homology atoms (`hasClass` + subsingletons). Every other shape (`H`, `row`, `hCob`/`hBase`,
`hcolD`, `hker`, `hΦg`) is the fixed residual. -/
theorem kt_equiv_zmod16_of_residuals_freezeAtoms_ofHomologyAtoms
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (str : (spinEmptyData residualProv).Mfd (sphereProdSM4 0))
    (hrow : row.R.s2s2 = ⟨sphereProdSM4 0, str⟩)
    (hasClass : letI := sphereDisk_t2Space.t1Space
      HasRelFundClass (X := TopCat.of SphereDisk)
        (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk)
        (interiorGenFamily (W := SphereDisk) ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    (hS1 : Subsingleton (Homology (TopCat.of SphereDisk) 1))
    (hS2 : Subsingleton (RelativeHomology (X := TopCat.of SphereDisk)
      (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk) 4))
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (hrow ▸ sphereProdCoboundaryWAdm_of_homologyAtoms residualProv str hasClass hS1 hS2)
    hcolD hker hΦg

/-- **The Rokhlin-16 twin of the P23-discharged wiring** — `Nat.card Ω₄^{Pin⁺} = 16` from the row with
Freeze B at the P23-atom-discharged coboundary atom. Pure transport; introduces no new residual. -/
theorem rokhlin_sixteen_of_residuals_freezeAtoms_ofHomologyAtoms
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (str : (spinEmptyData residualProv).Mfd (sphereProdSM4 0))
    (hrow : row.R.s2s2 = ⟨sphereProdSM4 0, str⟩)
    (hasClass : letI := sphereDisk_t2Space.t1Space
      HasRelFundClass (X := TopCat.of SphereDisk)
        (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk)
        (interiorGenFamily (W := SphereDisk) ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    (hS1 : Subsingleton (Homology (TopCat.of SphereDisk) 1))
    (hS2 : Subsingleton (RelativeHomology (X := TopCat.of SphereDisk)
      (((𝓡 4).prod (𝓡∂ 1)).boundary SphereDisk) 4))
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (hrow ▸ sphereProdCoboundaryWAdm_of_homologyAtoms residualProv str hasClass hS1 hS2)
    hcolD hker hΦg

/-! ## §4. FULLY-DISCHARGED headline rows — no geometric coboundary atom remains, only the
row-realization `hrow` + the fixed K3-assembly residual. -/

/-- **THE HEADLINE — KT ≅ ℤ/16 with the ENTIRE geometric coboundary content discharged.** The whole
`(b, hWT2, hasClass, subsingletons, P23, pin23, hv2)` block is gone: every geometric `S²×D³`
obligation is a proved sister node (`sphereProdCoboundaryWAdm_sphereDisk`). The only geometric-side
input left is the row-realization `hrow : row.R.s2s2 = ⟨sphereProdSM4 0, str⟩`; the rest (`H`, `row`,
`hCob`/`hBase`, `hcolD`, `hker`, `hΦg`) is the fixed K3-assembly residual. -/
theorem kt_equiv_zmod16_of_residuals_freezeAtoms_sphereDisk
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (str : (spinEmptyData residualProv).Mfd (sphereProdSM4 0))
    (hrow : row.R.s2s2 = ⟨sphereProdSM4 0, str⟩)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (hrow ▸ sphereProdCoboundaryWAdm_sphereDisk residualProv str) hcolD hker hΦg

/-- **The Rokhlin-16 twin, entire geometric coboundary content discharged.** -/
theorem rokhlin_sixteen_of_residuals_freezeAtoms_sphereDisk
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (str : (spinEmptyData residualProv).Mfd (sphereProdSM4 0))
    (hrow : row.R.s2s2 = ⟨sphereProdSM4 0, str⟩)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (hrow ▸ sphereProdCoboundaryWAdm_sphereDisk residualProv str) hcolD hker hΦg

/-! ## §5. The geometric interface at its terminal grain — the `(str, hrow)` row-realization couple
folded to the SINGLE distinguished-slot base pin. The discharged coboundary lane
(`sphereProdCoboundaryWAdm_sphereDisk`) is uniform in the tangential-structure component of the slot,
so the row-realization needs only that the distinguished slot's MANIFOLD is `sphereProdSM4 0`; the
structure component is carried, not constrained. This maximally collapses the geometric side; the
remaining row-cluster `{row, hCob, hBase}` is the settled E1-surgery floor
(`docs/dev-loops/SETTLED_FORKS.md` `freeze-atoms-not-composable-from-sigma-trace`), NOT this lane. -/

/-- **`SphereProdCoboundaryWAdm` for any distinguished slot whose MANIFOLD is the concrete `S²×S²`.**
The banked discharge `sphereProdCoboundaryWAdm_sphereDisk` is uniform in the tangential-structure
component of the slot, so it applies to ANY `p : StrMfd (spinEmptyData prov)` with `p.1 = sphereProdSM4 0`
— the structure `p.2` is carried, not constrained. Destructure `p` + `subst` the base equality lands the
concrete slot `⟨sphereProdSM4 0, p.2⟩`, where the sister-node discharge fires. -/
theorem sphereProdCoboundaryWAdm_sphereDisk_ofBase {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (spinEmptyData prov)) (hp : p.1 = sphereProdSM4 k) :
    SphereProdCoboundaryWAdm prov p := by
  obtain ⟨M, s⟩ := p
  subst hp
  exact sphereProdCoboundaryWAdm_sphereDisk prov s

/-- **THE HEADLINE, geometric interface at terminal grain** (`≃+ ZMod 16`) — as
`kt_equiv_zmod16_of_residuals_freezeAtoms_sphereDisk`, but the `(str, hrow)` row-realization couple is
collapsed to the SINGLE distinguished-slot base pin `hs2s2 : (row.R.s2s2).1 = sphereProdSM4 0`. The free
tangential-structure binder `str` is eliminated (it is exactly `(row.R.s2s2).2`, carried through the
uniform discharge) and the `StrMfd` equality `hrow` is weakened to its manifold component — a strictly
smaller geometric hypothesis. The whole geometric coboundary content is discharged internally; the
surviving residual is EXACTLY the settled E1-surgery floor `{row` (the open `SpinSigmaAtoms` bundle)`,
hCob, hBase}` (`freeze-atoms-not-composable-from-sigma-trace`) plus the fixed K3-assembly residual
`{H, hcolD, hker, hΦg}`. -/
theorem kt_equiv_zmod16_of_residuals_freezeAtoms_sphereDiskPinned
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hs2s2 : (row.R.s2s2).1 = sphereProdSM4 0)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (sphereProdCoboundaryWAdm_sphereDisk_ofBase residualProv row.R.s2s2 hs2s2) hcolD hker hΦg

/-- **The Rokhlin-16 twin, geometric interface at terminal grain.** As
`rokhlin_sixteen_of_residuals_freezeAtoms_sphereDisk` but with `(str, hrow)` collapsed to the single
distinguished-slot base pin `hs2s2 : (row.R.s2s2).1 = sphereProdSM4 0`. Pure transport; no new residual. -/
theorem rokhlin_sixteen_of_residuals_freezeAtoms_sphereDiskPinned
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hs2s2 : (row.R.s2s2).1 = sphereProdSM4 0)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (sphereProdCoboundaryWAdm_sphereDisk_ofBase residualProv row.R.s2s2 hs2s2) hcolD hker hΦg

end

/-! ## §6. THE SMOOTH-CATEGORY INSTANTIATION — the Freeze-B geometric lane at `k = ⊤`.

Roadmap §2 leg 2 is a hard constraint: the literature-grade `Ω₄^{Pin⁺} ≅ ℤ/16` is a SMOOTH-category
statement. At `k = 0` the `IsManifold` binder is *free* (`PinPlusRegularityFence.isManifoldZero_free`)
and the honest group is topological Pin⁺ bordism `≅ ℤ/2 ⊕ ℤ/8` — the wrong group — so a `k = 0`
discharge does not serve the goal, and kernel fork `k0-to-k1-transport-refuted` forbids lifting one.

The whole `S²×D³` coboundary lane above is now stated `k`-generically, so it **re-declares** at
`k = ⊤` rather than transporting. Nothing in it was weakened to get there: every input is a fact about
the fixed topological space `SphereDisk` (its mod-2/integral (co)homology, its Lefschetz–Wu tower, its
Hausdorffness, its boundary) and the `k`-generic bordism object `sphereProdCoboundaryBordism k`
(`PinPlusKTSphereProdReassoc`, whose `isManifold_R4`/`isManifold_J6` fields hold at every `k`). The
regularity enters ONLY through that bordism object's smoothness fields, which the banked atlas
supplies at `⊤`.

Consequence: the Freeze-B geometric content of the assembly row is discharged in the SMOOTH category,
not merely in `C⁰`. -/

/-- **The `S²×D³` coboundary `WAdmPinned` atom, in the SMOOTH category** — the `k = ⊤` instantiation
of `sphereProdCoboundaryWAdm_sphereDisk`. Every geometric obligation (the bordism object, its `T2`,
the relative fundamental class, the two homology subsingletons, the `(2,3)` Lefschetz–Wu datum, its
pin, and `v₂ = 0`) is a proved sister node at this regularity, exactly as at `k = 0`. -/
theorem sphereProdCoboundaryWAdm_sphereDisk_smooth
    (str : (spinEmptyData (residualProvK ⊤)).Mfd (sphereProdSM4 ⊤)) :
    SphereProdCoboundaryWAdm (residualProvK ⊤) ⟨sphereProdSM4 ⊤, str⟩ :=
  sphereProdCoboundaryWAdm_sphereDisk (residualProvK ⊤) str

/-- **`hBbord` in the SMOOTH category** — the Freeze-B geometric witness
`IsDataBordant (spinEmptyData (residualProvK ⊤)) ⟨S²×S², str⟩ ∅` at `k = ⊤`, from `str` alone. This is
the smooth-carrier form of `isDataBordant_empty_sphereDisk`; the `S²×S² = ∂(S²×D³)` content of the
assembly row now holds where the `IsManifold` binder is a genuine `C^∞`-atlas obligation. -/
theorem isDataBordant_empty_sphereDisk_smooth
    (str : (spinEmptyData (residualProvK ⊤)).Mfd (sphereProdSM4 ⊤)) :
    IsDataBordant (spinEmptyData (residualProvK ⊤)) ⟨sphereProdSM4 ⊤, str⟩
      ⟨emptySM, (spinEmptyData (residualProvK ⊤)).emptyStr⟩ :=
  isDataBordant_empty_sphereDisk (residualProvK ⊤) str

/-- **Conservativity certificate** — the `k`-generic lane specialises to the `k = 0` theorem of record
on the nose (`rfl`), so generalising the binders changed no `C⁰` statement. Mirrors the
`residualProv = residualProvK 0` certificate of the regularity lift. -/
theorem sphereProdCoboundaryWAdm_sphereDisk_zero_eq
    (str : (spinEmptyData residualProv).Mfd (sphereProdSM4 0)) :
    sphereProdCoboundaryWAdm_sphereDisk residualProv str =
      sphereProdCoboundaryWAdm_sphereDisk (residualProvK 0) str :=
  rfl

/-! ## §7. THE `hB`-FREE ASSEMBLY AT EVERY REGULARITY — Freeze B leaves the row.

`SpinSigmaPresentation.sphereProductBounds_of_bordant` (`SphereProductBounding`) is generic in the
tangential datum `{ξ : TangentialData X k I}`, and §6 made the coboundary discharge `k`-generic. So the
two compose at ANY `k`: the Freeze-B hypothesis `hB : row.R.SphereProductBounds` is no longer an input
to the assembly — it is PRODUCED from the geometry, leaving only the slot pin
`hs2s2 : (row.R.s2s2).1 = sphereProdSM4 k` (a row-realization equation on the manifold component, not a
geometric obligation; the tangential-structure component is carried).

This is the `k`-generic analogue of the `k = 0` `…_freezeAtoms_sphereDiskPinned` chain, built on the
regularity-generic backbone `kt_equiv_zmod16_of_residuals_ofKRS` rather than on the `residualProv`-pinned
`freezeAtoms` family.

**How it compares to `kt_equiv_zmod16_of_residuals_smooth` (stated precisely — the hypothesis COUNT is
the same, eight; the improvement is on two axes, not in arity):**
* `hB : row.R.SphereProductBounds` (a geometric/algebraic obligation — the distinguished class bounds)
  is replaced by `hs2s2 : (row.R.s2s2).1 = sphereProdSM4 k`, a **row-realization equation on the
  manifold component only** (the tangential-structure component is carried, not constrained). Same
  trade the banked `k = 0` `…_sphereDiskPinned` makes.
* `H` is taken at `KernelReducesToSpin prov` rather than the `AmbientSurgeryDatum` ∀-`p` row. Per
  `PinPlusKTAssemblyResiduals` §R, the row IMPLIES `KernelReducesToSpin`
  (`kernelReducesToSpin_of_ambientDatumSupply`), so this binder is **strictly weaker** and the
  statement correspondingly stronger.

No claim is made that the row shrank; it did not. -/

/-- **THE `k`-GENERIC ASSEMBLY WITH FREEZE B DISCHARGED.** `Ω₄^{Pin⁺} ≃+ ZMod 16` on the faithful
tethered carrier at ANY smoothness exponent `k`, with `hB : row.R.SphereProductBounds` **eliminated** —
supplied internally by the `S²×D³` coboundary geometry (`sphereProdCoboundaryWAdm_sphereDisk_ofBase`
→ `hBbord_of_coboundary` → `sphereProductBounds_of_bordant`). The surviving row is
`{hKRS, row, hA, hcol, hker, hcyc, h2}` plus the slot pin `hs2s2`. -/
theorem kt_equiv_zmod16_ofKRS_sphereDiskPinned {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hKRS : KernelReducesToSpin prov)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts)
    (hs2s2 : (row.R.s2s2).1 = sphereProdSM4 k)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hker : KerPhiSubDoubles prov)
    (hcyc : SpinImageCyclic prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_ofKRS prov hKRS row hA
    (row.R.sphereProductBounds_of_bordant
      (hBbord_of_coboundary prov row.R.s2s2
        (sphereProdCoboundaryWAdm_sphereDisk_ofBase prov row.R.s2s2 hs2s2)))
    hcol hker hcyc h2

/-- **THE SMOOTH-CATEGORY HEADLINE WITH FREEZE B DISCHARGED** (`k = ⊤`). The `C^∞` instantiation of
the above: `Ω₄^{Pin⁺} ≃+ ZMod 16` on the smooth faithful carrier from a row whose Freeze-B atom is
supplied by geometry rather than assumed. Same conclusion and same carrier as
`kt_equiv_zmod16_of_residuals_smooth`, and the SAME number of binders (eight) — the improvement is
that two of them are weaker (see §7: `hB` → the row-realization pin `hs2s2`; the `AmbientSurgeryDatum`
∀-`p` row → the `KernelReducesToSpin` Prop it implies). -/
theorem kt_equiv_zmod16_smooth_sphereDiskPinned
    (hKRS : KernelReducesToSpin (residualProvK ⊤))
    (row : SpinPresentationRow (residualProvK ⊤))
    (hA : row.R.RealizesSphereProducts)
    (hs2s2 : (row.R.s2s2).1 = sphereProdSM4 ⊤)
    (hcol : RankZeroCollapsesToEmptySurf (residualProvK ⊤))
    (hker : KerPhiSubDoubles (residualProvK ⊤))
    (hcyc : SpinImageCyclic (residualProvK ⊤))
    (h2 : ktKernelRep (residualProvK ⊤) + ktKernelRep (residualProvK ⊤) = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData (residualProvK ⊤)) ≃+ ZMod 16) :=
  kt_equiv_zmod16_ofKRS_sphereDiskPinned (residualProvK ⊤) hKRS row hA hs2s2 hcol hker hcyc h2

/-- **W-E, SMOOTH, WITH FREEZE B DISCHARGED** — `Nat.card Ω₄^{Pin⁺} = 16` on the smooth carrier from
the `hB`-free row. Pure transport across the additive equivalence; no new residual atom. -/
theorem rokhlin_sixteen_smooth_sphereDiskPinned
    (hKRS : KernelReducesToSpin (residualProvK ⊤))
    (row : SpinPresentationRow (residualProvK ⊤))
    (hA : row.R.RealizesSphereProducts)
    (hs2s2 : (row.R.s2s2).1 = sphereProdSM4 ⊤)
    (hcol : RankZeroCollapsesToEmptySurf (residualProvK ⊤))
    (hker : KerPhiSubDoubles (residualProvK ⊤))
    (hcyc : SpinImageCyclic (residualProvK ⊤))
    (h2 : ktKernelRep (residualProvK ⊤) + ktKernelRep (residualProvK ⊤) = 0) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData (residualProvK ⊤))) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_smooth_sphereDiskPinned hKRS row hA hs2s2 hcol hker hcyc h2
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end SKEFTHawking.PinPlusKTSphereProdP23Close
