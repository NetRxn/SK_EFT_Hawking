/-
# Phase 5q.H close-out (#206) — THE S²×D³ ADMISSIBILITY TOWER: the coboundary `WAdmPinned` SHARPENED.

This module attacks the sole `hBbord` residual isolated by #203
(`PinPlusKTSphereProdBordism.SphereProdCoboundaryWAdm`): a T2 `S²×D³`-type coboundary `b : p.1 ↝ ∅`
with `Nonempty (WAdmPinned b)`, the substrate-pinned Lefschetz–Wu `w₂(W) = 0` tower on the
5-manifold-with-boundary `W = S²×D³`.

## The sharpening (what lands GREEN here).

`WAdmPinned b` bundles TWO pinned Lefschetz–Wu data — the `(1,4)` leg (`v₁ ∈ H¹(W)`) and the
`(2,3)` leg (`v₂ ∈ H²(W)`) — plus admissibility `wuW2 = 0`. For `W = S²×D³ ≃ S²` the `(1,4)` leg is
DEGENERATE: `H¹(S²×D³;ℤ/2) = 0` and (rel-Poincaré–Lefschetz) `H⁴(W,∂W;ℤ/2) ≅ H₁(W;ℤ/2) = 0`. This
module PROVES that under those two subsingleton facts the whole `(1,4)` leg is FREE — every one of
`LefschetzWuDatum.ofRelFund14`'s four inputs (`findimAbs`, `findimRel`, `nondeg`, `dimeq`) is
discharged by subsingleton-ness, and `ofRelFund14_pinned` supplies the pin gratis — and that the Wu
admissibility `wuW2 P14 P23 = 0` COLLAPSES to `v₂ = 0` (the `(1,4)` contribution `v₁² = 0` because
`v₁ = 0`).

So the whole `WAdmPinned b` for the `S²×D³` shape reduces to the SHARP residual:

* one relative fundamental-class datum `RelFundClassDatum (∂W)` (the `[W,∂W] ∈ H₅(W,∂W;ℤ/2)`
  restricting to the interior generator — the accepted `ofRelFund` per-object shape),
* two subsingleton facts `H¹(W) = 0`, `H⁴(W,∂W) = 0` (the `S²×D³ ≃ S²` mod-2 cohomology + rel-PD),
* the `(2,3)` Poincaré–Lefschetz duality inputs (`H²(W) ≅ H³(W,∂W)` a perfect cup pairing), and
* `v₂(W) = 0` (`S²×D³` is spin).

`wadmPinned_ofRelFund_degenerate14` assembles `WAdmPinned b` from exactly these named inputs (the
accepted `ofRelFund*` / `cylinderP*_pinned` pattern — atoms as explicit arguments, NO minted
completeness `Prop`, NO consumed assembly output); `sphereProdCoboundaryWAdm_of_degenerate14` narrows
`SphereProdCoboundaryWAdm` to a T2 coboundary carrying exactly that data. The `(1,4)` leg is no longer
an atom — the residual is the `(2,3)` half + the relative fundamental class + `v₂ = 0`.

**Circularity audit (by proof inspection)**: `wadmPinned_ofRelFund_degenerate14` is pure term/tactic
wiring of `LefschetzWuDatum.ofRelFund14`/`.ofRelFund23` + `ofRelFund*_pinned` + the subsingleton
discharges into the `WAdmPinned` structure. NO `k₀`/`KTNonSplit`-strength fact, NO `÷32`, NO output of
the `kt_equiv_zmod16` assembly is consumed; the residual inputs are genuine load-bearing cohomological
statements (the `(2,3)` rel-PD perfect pairing + `v₂ = 0`), not fabricated grades. CLEAN.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`. No new leaf `Prop` needing gate review is minted.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSphereProdBordism

open scoped Manifold
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairEmptySourceRealization
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTAssemblyResiduals
open SKEFTHawking.PinPlusKTBinderDischarge
open SKEFTHawking.PinPlusKTCollapseDischarge
open SKEFTHawking.PinPlusKTFreezeDischarge
open SKEFTHawking.PinPlusKTSphereProdBordism

namespace SKEFTHawking.PinPlusKTSphereProdWAdm

/-! ## §0. Subsingleton discharges of the `ofRelFund14` inputs (the degenerate `(1,4)` leg). -/

section Degenerate

variable {X : TopCat} {S : Set X}

/-- A subsingleton `ZMod 2`-module is finite-dimensional. -/
theorem findim_of_subsingleton {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Subsingleton M] :
    FiniteDimensional (ZMod 2) M := by
  have : Finite M := inferInstance
  exact Module.Finite.of_finite

/-- **The pinned `(1,4)` Lefschetz–Wu datum for the degenerate leg.** When `H¹(W;ℤ/2) = 0` and
`H⁴(W,∂W;ℤ/2) = 0` (both subsingleton — the `S²×D³ ≃ S²` mod-2 cohomology + rel-Poincaré–Lefschetz),
every one of `ofRelFund14`'s four inputs is FREE: `findimAbs`/`findimRel` from subsingleton-finiteness,
`nondeg` because a map out of a subsingleton domain is injective, `dimeq` because both finranks are `0`.
So the `(1,4)` leg is assembled from the relative fundamental-class datum alone. -/
noncomputable def degenerateP14 (D : RelFundClassDatum (m := 3) S)
    [Subsingleton (Cohomology X 1)] [Subsingleton (RelativeCohomology S 4)] :
    LefschetzWuDatum X S 1 4 5 :=
  LefschetzWuDatum.ofRelFund14 D findim_of_subsingleton findim_of_subsingleton
    (fun a b _ => Subsingleton.elim a b)
    (by rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton])

/-- The degenerate `(1,4)` datum is substrate-PINNED (`μ = D.mu`, `cup = relCupH14`, `sqOp = relSq1`),
via `ofRelFund14_pinned` — no extra input beyond the two subsingleton facts. -/
theorem degenerateP14_pinned (D : RelFundClassDatum (m := 3) S)
    [Subsingleton (Cohomology X 1)] [Subsingleton (RelativeCohomology S 4)] :
    LefschetzWuPinned14 (degenerateP14 D) :=
  ofRelFund14_pinned D findim_of_subsingleton findim_of_subsingleton
    (fun a b _ => Subsingleton.elim a b)
    (by rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton])

/-- **The Wu admissibility COLLAPSES to `v₂ = 0` on the degenerate `(1,4)` leg.** When `H¹(W;ℤ/2) = 0`
the first Wu class `v₁ = wuClass P14 = 0`, so `v₁² = 0` and `w₂(W) = v₂ + v₁² = v₂ = wuClass P23`.
Hence `wuW2 P14 P23 = wuClass P23`: the whole `(1,4)` contribution to admissibility vanishes. -/
theorem wuW2_degenerate14_eq (P14 : LefschetzWuDatum X S 1 4 5) (P23 : LefschetzWuDatum X S 2 3 5)
    [Subsingleton (Cohomology X 1)] : wuW2 P14 P23 = wuClass P23 := by
  have h1 : wuClassW1 P14 = 0 := Subsingleton.elim _ _
  rw [wuW2, h1, map_zero, add_zero]
  rfl

end Degenerate

/-! ## §1. The builder — `WAdmPinned b` from the sharpened residual (degenerate `(1,4)` + `(2,3)` + `v₂ = 0`). -/

section Builder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **`WAdmPinned b` from the sharpened cohomological residual.** For any coboundary bordism `b`, given
* the relative fundamental-class datum `D` (the `[W,∂W] ∈ H₅(W,∂W;ℤ/2)` — accepted `ofRelFund` shape),
* the two subsingleton facts `H¹(W;ℤ/2) = 0`, `H⁴(W,∂W;ℤ/2) = 0` (degenerate `(1,4)` leg),
* the `(2,3)` Poincaré–Lefschetz duality inputs (`findimAbs23`/`findimRel23`/`nondeg23`/`dimeq23` — a
  perfect cup pairing `H²(W) ≅ H³(W,∂W)`), and
* `v₂(W) = 0` (`hv2`; `S²×D³` is spin),

the substrate-pinned Lefschetz–Wu tower `WAdmPinned b` is assembled. The `(1,4)` pin is free
(`degenerateP14_pinned`), the `(2,3)` leg is supplied as a pinned datum, and admissibility `wuW2 = 0`
collapses to `hv2` via `wuW2_degenerate14_eq`. Atoms as explicit arguments — the accepted
`ofRelFund*`/`cylinderP*_pinned` pattern; NO minted completeness `Prop`. -/
noncomputable def wadmDatum_degenerate14
    {s t : SingularManifold.{0} PUnit.{1} k I} (b : Bordism.{0} (I.prod (𝓡∂ 1)) s t)
    (D : RelFundClassDatum (X := TopCat.of b.W) (m := 3) ((I.prod (𝓡∂ 1)).boundary b.W))
    [Subsingleton (Cohomology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (hv2 : wuClass P23 = 0) :
    WAdm b where
  P14 := degenerateP14 D
  P23 := P23
  hwu := by rw [wuW2_degenerate14_eq]; exact hv2

/-- **`WAdmPinned b` from the sharpened cohomological residual** — the pinned tower over
`wadmDatum_degenerate14`. The `(1,4)` pin is free (`degenerateP14_pinned`); the `(2,3)` pin `pin23`
is the caller's genuine Poincaré–Lefschetz datum. -/
noncomputable def wadmPinned_degenerate14
    {s t : SingularManifold.{0} PUnit.{1} k I} (b : Bordism.{0} (I.prod (𝓡∂ 1)) s t)
    (D : RelFundClassDatum (X := TopCat.of b.W) (m := 3) ((I.prod (𝓡∂ 1)).boundary b.W))
    [Subsingleton (Cohomology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeCohomology (X := TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23)
    (hv2 : wuClass P23 = 0) :
    WAdmPinned b where
  wadm := wadmDatum_degenerate14 b D P23 hv2
  pin14 := degenerateP14_pinned D
  pin23 := pin23

end Builder

/-! ## §2. The coboundary wiring — `SphereProdCoboundaryWAdm` (hence `hBbord`) from the sharpened residual. -/

section Wiring

/-- **`SphereProdCoboundaryWAdm` from the sharpened residual.** The #203 atom
`SphereProdCoboundaryWAdm prov p` (a T2 coboundary `b : p.1 ↝ ∅` with `Nonempty (WAdmPinned b)`) is
inhabited by ANY T2 coboundary `b` carrying: the relative fundamental-class datum `D`, the two
subsingleton facts (degenerate `(1,4)` leg), a pinned `(2,3)` Poincaré–Lefschetz datum `P23`, and
`v₂(W) = 0`. The whole `(1,4)` half is discharged for free — the residual is the `(2,3)` half + the
relative fundamental class + `v₂ = 0`. -/
theorem sphereProdCoboundaryWAdm_of_degenerate14 {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k) (p : StrMfd (spinEmptyData prov))
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 (emptySM (X := PUnit) (k := k) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (D : RelFundClassDatum (X := TopCat.of b.W) (m := 3) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W))
    [Subsingleton (Cohomology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0) :
    SphereProdCoboundaryWAdm prov p :=
  ⟨b, hWT2, ⟨wadmPinned_degenerate14 b D P23 pin23 hv2⟩⟩

/-- **`hBbord` from the sharpened residual** — the empty-membrane collapse (`hBbord_of_coboundary`,
#203) composed with the sharpened coboundary atom. Directly discharges the `hBbord` obligation
`IsDataBordant (spinEmptyData prov) p ∅` from the `(2,3)` half + relative fundamental class + `v₂ = 0`
(the `(1,4)` half free). -/
theorem isDataBordant_empty_of_degenerate14 {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k) (p : StrMfd (spinEmptyData prov))
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 (emptySM (X := PUnit) (k := k) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (D : RelFundClassDatum (X := TopCat.of b.W) (m := 3) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W))
    [Subsingleton (Cohomology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0) :
    IsDataBordant (spinEmptyData prov) p ⟨emptySM, (spinEmptyData prov).emptyStr⟩ :=
  hBbord_of_coboundary prov p (sphereProdCoboundaryWAdm_of_degenerate14 prov p b hWT2 D P23 pin23 hv2)

/-- **THE DEGENERATE-`(1,4)` WIRING** (`kt_equiv_zmod16_of_residuals_freezeAtoms_ofDegenerate14`) — the
finest-grain KT ≅ ℤ/16 assembly with the Freeze-B geometric hypothesis at the distinguished slot
`row.R.s2s2` given by the SHARPENED residual instead of `SphereProdCoboundaryWAdm`: a T2 coboundary
`b` with relative fundamental class `D`, the two subsingletons (degenerate `(1,4)` leg), a pinned
`(2,3)` Poincaré–Lefschetz datum `P23`, and `v₂ = 0`. Every OTHER consumer shape (`H`, `row`,
`hCob`/`hBase`, `hcolD`, `hker`, `hΦg`) is fixed. This is the honest headline: the whole
`S²×S² = ∂(S²×D³)` bordism content is discharged EXCEPT the `(2,3)` Poincaré–Lefschetz half + the
relative fundamental class + `v₂ = 0`; the `(1,4)` Wu leg is no longer an atom. -/
theorem kt_equiv_zmod16_of_residuals_freezeAtoms_ofDegenerate14
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) row.R.s2s2.1 (emptySM (X := PUnit) (k := 0) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (D : RelFundClassDatum (X := TopCat.of b.W) (m := 3) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W))
    [Subsingleton (Cohomology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (sphereProdCoboundaryWAdm_of_degenerate14 residualProv row.R.s2s2 b hWT2 D P23 pin23 hv2)
    hcolD hker hΦg

/-- **The Rokhlin-16 twin of the degenerate-`(1,4)` wiring** — `Nat.card Ω₄^{Pin⁺} = 16` from the row
with Freeze B at the sharpened residual. Pure transport; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_freezeAtoms_ofDegenerate14
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) row.R.s2s2.1 (emptySM (X := PUnit) (k := 0) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (D : RelFundClassDatum (X := TopCat.of b.W) (m := 3) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W))
    [Subsingleton (Cohomology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (sphereProdCoboundaryWAdm_of_degenerate14 residualProv row.R.s2s2 b hWT2 D P23 pin23 hv2)
    hcolD hker hΦg

end Wiring

end SKEFTHawking.PinPlusKTSphereProdWAdm
