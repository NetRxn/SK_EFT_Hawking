/-
# Phase 5q.H — THE FREEZE DISCHARGE (block #200): assembly hypotheses 3–4 at their terminal atoms

This module attacks the third and fourth hypotheses of the current sharpest end-to-end assembly
`PinPlusKTCollapseDischarge.kt_equiv_zmod16_of_residuals_collapseDatum` (the collapse-datum 7-row
`{H, row, hA, hB, hcolD, hker, hΦg}`):

  3. `hA : row.R.RealizesSphereProducts` — Freeze A (Benedetti arXiv:1907.10297 Prop 20.16 /
     Lemma 20.17: `n·H` handle-trading realization).
  4. `hB : row.R.SphereProductBounds` — Freeze B (`[S²×S²] = 0`, `S²×S² = ∂(S²×D³)`).

## Triage verdict (kernel-checked): genuine discharge of BOTH is BLOCKED at the manifold-surgery
foundation on the E1 intersection-form axis; the honest form is the finest-grain terminal atoms,
wired onto the collapse-datum 7-row.

### hA — the Freeze-A terminal pair `{HandleTradeCobordism, HyperbolicBase}`.
`realizesSphereProducts_of_cobordism_and_base` reduces `RealizesSphereProducts` to the raw single
handle-trace cobordism `HandleTradeCobordism` (the residual manifold `p'` + ONE structured cobordism
`p ↝ (S²×S²) ⊔ p'`, Benedetti Prop 20.16) plus the rank-0 nullbordism `HyperbolicBase` (Thm 20.14).

* **`HandleTradeCobordism` — genuine discharge NOT composable from the banked Lane-B trace
  machinery.** Lane B (`AmbientSurgeryDatum`, `PinPlusKTSurgeryTrace`) performs AMBIENT surgery on
  the CHARACTERISTIC SURFACE `Σ`, lowering the isotropic enhancement rank `p.2.n` by exactly 2
  (`ambientSurgeryDatum_pos_rank` FORCES `0 < p.2.n`). `HandleTradeCobordism` instead trades one
  E1 intersection-form hyperbolic pair `H` for `[S²×S²]` — surgery on the 4-manifold's E1 2-cycles
  (`R.rank p = b₂`). These are DIFFERENT geometric axes. The consumer module
  (`PinPlusKTSurgeryTraceConsumers` §3) confirms this: `handleTradeCobordism_residual_is_traceBor`
  is `rfl` (a documentation identity restating the def), and `spinTraceBordism` STILL requires the
  E1 handle-attaching map / smoothness / boundary data as INPUTS — the exact manifold-surgery
  foundation Mathlib lacks. So the recorded "HandleTradeCobordism ⟸ trace bordism + ξ.Bor" does
  NOT compose: it names the residual, it does not construct the E1 handle-trace bordism.
* **`HyperbolicBase` — genuine discharge BLOCKED, and NOT fakeable from #199's
  `RankZeroCollapseDatum`.** `HyperbolicBase` (rank-0 `b₂` ⟹ null-bordant on `spinEmptyData`) needs
  surgery on the E1 2-cycles to a homotopy `S⁴` then the `D⁵` cap. #199's `RankZeroCollapseDatum` is
  on a DIFFERENT carrier (`pinPlusCharPairData`, not `spinEmptyData`), its "rank 0" is the
  enhancement rank `p.2.n = 0` (NOT `b₂`), and its target is an empty-SURFACE structure (NOT the
  empty manifold `0`). The bounding-datum cores are therefore NOT shared; wiring one to the other
  would be exactly the prohibited "fake from the other's Prop-shape". Left as the named atom.

### hB — the Freeze-B bordism form `IsDataBordant … s2s2 ∅`.
`sphereProductBounds_of_bordant` reduces `SphereProductBounds` (`[s2s2] = 0`, algebraic) to the
strictly-finer GEOMETRIC witness `IsDataBordant (spinEmptyData prov) row.R.s2s2 ⟨emptySM, emptyStr⟩`
(the distinguished slot bounds). Genuine discharge is BLOCKED: the concrete route
(`sphereProductBounds_of_package`, `S²×S² = ∂(S²×D³)`) fires only when the slot IS the concrete
`S²×S²` AND the frozen closed-ball collar atlas (`SphereDiskSmoothData`) is supplied — the
Mathlib-absent `D³`/`Dⁿ` manifold instance + change-of-model transport. The genuine `row.R.s2s2` is
an ABSTRACT slot (only `II ≅ H` pinned), so neither the concrete-manifold identification nor the
atlas is available; the §6 `revStr`-fixed alternative needs carrier torsion-freeness (downstream of
the iso — circular). So hB reduces to the single geometric bordism atom, no more.

## What lands GREEN here (honest reductions on the collapse-datum 7-row — NO new leaf `Prop`).
`kt_equiv_zmod16_of_residuals_freezeA` (hA → `{hCob, hBase}`), `…_freezeB` (hB → the bordism atom
`hBbord`), and `…_freezeAtoms` (BOTH, the full finest-grain assembly), each with its Rokhlin-16 twin.
This is the collapse-datum analogue of #195 (which reduced hA off the OLDER 8-row
`kt_equiv_zmod16_of_residuals`); the new content is the reduction rebased on the current sharpest
7-row AND the previously-undone Freeze-B push to its bordism form.

**Circularity audit (by proof inspection)**: every theorem is pure term-mode wiring that composes an
EXISTING reduction lemma (`realizesSphereProducts_of_cobordism_and_base` /
`sphereProductBounds_of_bordant`, both circularity-clean geometry) into the base assembly
`kt_equiv_zmod16_of_residuals_collapseDatum` (itself #199-audited clean). NO `k₀`/`KTNonSplit`-strength
fact, NO `÷32`, NO output of the assembly is consumed. CLEAN.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`. No new leaf `Prop` is minted — nothing here needs gate review.
-/
import Mathlib
import SKEFTHawking.PinPlusKTCollapseDischarge
import SKEFTHawking.HandleTradeSurgery
import SKEFTHawking.SphereProductBounding

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTAssemblyResiduals
open SKEFTHawking.PinPlusKTBinderDischarge
open SKEFTHawking.PinPlusKTCollapseDischarge

namespace SKEFTHawking.PinPlusKTFreezeDischarge

/-! ## §1. Freeze A → the terminal pair `{HandleTradeCobordism, HyperbolicBase}`. -/

/-- **THE FREEZE-A WIRING** (`kt_equiv_zmod16_of_residuals_freezeA`) — the same end-to-end conclusion
as `kt_equiv_zmod16_of_residuals_collapseDatum`, but with the Freeze-A hypothesis
`hA : row.R.RealizesSphereProducts` REPLACED by its terminal pair: the raw single handle-trace
cobordism `hCob : row.R.HandleTradeCobordism` (Benedetti Prop 20.16 / Lemma 20.17) and the rank-0
nullbordism `hBase : row.R.HyperbolicBase` (Thm 20.14). Pure wiring:
`realizesSphereProducts_of_cobordism_and_base` reassembles `hA`, then the collapse-datum assembly of
record fires. This rebases #195's Freeze-A reduction onto the current sharpest 7-row. -/
theorem kt_equiv_zmod16_of_residuals_freezeA
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hB : row.R.SphereProductBounds)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_collapseDatum H row
    (row.R.realizesSphereProducts_of_cobordism_and_base hCob hBase) hB hcolD hker hΦg

/-- **The Rokhlin-16 twin of the Freeze-A wiring** (`rokhlin_sixteen_of_residuals_freezeA`):
`Nat.card Ω₄^{Pin⁺} = 16` from the SAME row with `hA` at its terminal pair. Pure transport of
`Nat.card (ZMod 16) = 16` across the additive equivalence; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_freezeA
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hB : row.R.SphereProductBounds)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_collapseDatum H row
    (row.R.realizesSphereProducts_of_cobordism_and_base hCob hBase) hB hcolD hker hΦg

/-! ## §2. Freeze B → the geometric bordism atom `IsDataBordant … s2s2 ∅`. -/

/-- **THE FREEZE-B WIRING** (`kt_equiv_zmod16_of_residuals_freezeB`) — the same end-to-end conclusion,
but with the Freeze-B hypothesis `hB : row.R.SphereProductBounds` (`[s2s2] = 0`, algebraic) REPLACED
by the strictly-finer GEOMETRIC witness `hBbord : IsDataBordant (spinEmptyData residualProv) row.R.s2s2
⟨emptySM, (spinEmptyData residualProv).emptyStr⟩` (the distinguished `S²×S²` slot bounds — the
`S²×S² = ∂(S²×D³)` content). `sphereProductBounds_of_bordant` collapses the single cobordism under the
quotient (`Quot.sound`). This is the Freeze-B push #195 explicitly left undone (it kept `hB` at the
named-freeze grain). -/
theorem kt_equiv_zmod16_of_residuals_freezeB
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts)
    (hBbord : IsDataBordant (spinEmptyData residualProv) row.R.s2s2
        ⟨emptySM, (spinEmptyData residualProv).emptyStr⟩)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_collapseDatum H row
    hA (row.R.sphereProductBounds_of_bordant hBbord) hcolD hker hΦg

/-- **The Rokhlin-16 twin of the Freeze-B wiring** (`rokhlin_sixteen_of_residuals_freezeB`):
`Nat.card Ω₄^{Pin⁺} = 16` from the SAME row with `hB` at its geometric bordism form. Pure transport
across the additive equivalence; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_freezeB
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts)
    (hBbord : IsDataBordant (spinEmptyData residualProv) row.R.s2s2
        ⟨emptySM, (spinEmptyData residualProv).emptyStr⟩)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_collapseDatum H row
    hA (row.R.sphereProductBounds_of_bordant hBbord) hcolD hker hΦg

/-! ## §3. The full finest-grain assembly — BOTH Freeze A and Freeze B at their terminal atoms. -/

/-- **THE FINEST-GRAIN ASSEMBLY** (`kt_equiv_zmod16_of_residuals_freezeAtoms`) — the collapse-datum
7-row with BOTH Freeze hypotheses reduced to their terminal geometric atoms simultaneously:
`hA → {hCob, hBase}` and `hB → hBbord`. Every remaining geometric hypothesis of the end-to-end
`Ω₄^{Pin⁺} ≃+ ZMod 16` now sits at its finest manifold-surgery grain — the exact objects a future
E1-axis surgery foundation must build: one raw handle-trace cobordism, one rank-0 nullbordism, one
`S²×S²` bounding bordism, the per-object rank-0 collapse datum (`hcolD`), plus the algebraic
`{H, row, hker, hΦg}`. -/
theorem kt_equiv_zmod16_of_residuals_freezeAtoms
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBbord : IsDataBordant (spinEmptyData residualProv) row.R.s2s2
        ⟨emptySM, (spinEmptyData residualProv).emptyStr⟩)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_collapseDatum H row
    (row.R.realizesSphereProducts_of_cobordism_and_base hCob hBase)
    (row.R.sphereProductBounds_of_bordant hBbord) hcolD hker hΦg

/-- **The Rokhlin-16 twin of the finest-grain assembly** (`rokhlin_sixteen_of_residuals_freezeAtoms`):
`Nat.card Ω₄^{Pin⁺} = 16` from the row with BOTH Freeze hypotheses at their terminal atoms. Pure
transport across the additive equivalence; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_freezeAtoms
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBbord : IsDataBordant (spinEmptyData residualProv) row.R.s2s2
        ⟨emptySM, (spinEmptyData residualProv).emptyStr⟩)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_collapseDatum H row
    (row.R.realizesSphereProducts_of_cobordism_and_base hCob hBase)
    (row.R.sphereProductBounds_of_bordant hBbord) hcolD hker hΦg

end SKEFTHawking.PinPlusKTFreezeDischarge
