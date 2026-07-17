/-
# Phase 5q.H — THE W-D BINDER DISCHARGE (block #197): hypotheses 7–8 (`hcyc` + `h2`)

This module attacks the two historically-frozen W-D binders of the end-to-end assembly
`PinPlusKTAssemblyResiduals.kt_equiv_zmod16_of_residuals`:

  7. `hcyc : SpinImageCyclic residualProv`
  8. `h2   : ktKernelRep residualProv + ktKernelRep residualProv = 0` (the 2-torsion of `k₀`).

## Triage verdict (per hypothesis)

* **`h2` — NOT an independent binder.** Downstream of the generator image `hΦg : Φ[g] = k₀` it is
  FREE: `PinPlusKTSpinPresentationRow.h2_of_generatorImage` derives `k₀ + k₀ = 0` from `hΦg` alone
  (via `spinForgetPhi_add_self` = the structure-TIED empty-Σ 2-torsion, NOT universal
  `revStr`-triviality — so it does NOT reproduce the no-go
  `dataBordism_two_torsion_of_revStr_trivial`). Standalone (without `hΦg`) it reduces to the sharp
  Kummer conjunct `EmptySigmaRepresentable residualProv (ktKernelRep residualProv)` via the banked
  `emptySigmaRepresentable_two_torsion` (`kt_equiv_zmod16_of_residuals_kummerRep` below).
* **`hcyc` — reduced-to-atom `hΦg`.** In the assembly `SpinImageCyclic`'s ONLY role is to help derive
  `hΦg` (`spinForgetPhi_g_eq_ktKernelRep_of_cyclic`); its own honest discharge is the (unbuilt)
  spin-specialization map `Φ` (`spinImageCyclic_of_presentation`). Both consumers of `{hcyc, h2}` in
  the assembly — the dC leaf and the dA leaf — actually need only `hΦg`
  (`nonempty_ktSpinPresentationDatum_of_row_of_collapse`, `nonempty_dualSpinForwardDatum_of_spinForgetPhi`).

## Net reduction

`kt_equiv_zmod16_of_residuals_phig` REPLACES the pair `{hcyc, h2}` with the SINGLE geometric atom
`hΦg` (the K3 generator maps to the kernel representative) — an 8→7 row-shrink, and the removed pair
collapses to one equation. `hΦg` is the exact KT §5 content; it is UPSTREAM of `KTNonSplit`
(`ktNonSplit_of_dualSpinForwardDatum` derives `KTNonSplit` from the dA datum built on `hΦg`), so
taking `hΦg` as an atom consumes NEITHER `KTNonSplit` NOR the ÷32 conclusion — the circularity the
round-11/round-12 gates fenced.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`. Pure statement-level wiring — every discharge lemma exists.
-/
import Mathlib
import SKEFTHawking.PinPlusKTAssemblyResiduals
import SKEFTHawking.PinPlusKTSpinForgetPhi
import SKEFTHawking.PinPlusKTKernelSector
import SKEFTHawking.PinPlusKTKernelSpinRoute

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
open SKEFTHawking.PinPlusTraceLeafGate
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusKTLeafGate
open SKEFTHawking.PinPlusKTAssemblyResiduals

namespace SKEFTHawking.PinPlusKTBinderDischarge

/-! ## §1. THE `hΦg` REDUCTION — `{hcyc, h2}` ⟶ the single generator-image atom -/

/-- **THE BINDER DISCHARGE** (`kt_equiv_zmod16_of_residuals_phig`) — the same end-to-end conclusion as
`kt_equiv_zmod16_of_residuals`, but with the pair of W-D binders `{hcyc : SpinImageCyclic, h2 : 2·k₀ =
0}` REPLACED by the single geometric atom `hΦg : spinForgetPhi[g] = k₀` (the K3 generator maps to the
kernel representative). This is the honest finest-grain form of hypotheses 7–8: both consumers of the
pair in the assembly need only `hΦg`.

* the dC leaf (`nonempty_ktSpinPresentationDatum_of_row_of_collapse`) already consumes `hΦg` directly;
* the dA leaf here uses `nonempty_dualSpinForwardDatum_of_spinForgetPhi` (which takes `hΦg` + `hfwd`,
  NOT `hcyc`/`h2` — those two entered the assembly ONLY through deriving `hΦg`).

Circularity audit: `hΦg` is UPSTREAM of `KTNonSplit` (the dA datum built on it yields `KTNonSplit` via
`ktNonSplit_of_dualSpinForwardDatum`), and it asserts nothing about `k₀ ≠ 0` or the ÷32 conclusion, so
it consumes neither — the fence `geometric-phi-does-not-close-hfwd-fakeability` is respected. -/
theorem kt_equiv_zmod16_of_residuals_phig
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) := by
  have hKRS : KernelReducesToSpin residualProv := kernelReducesToSpin_of_residualRow H
  have hfwd : ∀ x, spinForgetPhi residualProv x = 0 → (32 : ℤ) ∣ row.R.sig x :=
    spinForgetPhi_hfwd_of_ker_sub_doubles residualProv row.R row.hdvd hker
  obtain ⟨dC⟩ := nonempty_ktSpinPresentationDatum_of_row_of_collapse row hA hB hΦg hcol
  obtain ⟨dA⟩ :=
    nonempty_dualSpinForwardDatum_of_spinForgetPhi residualProv row.R row.g row.hg hΦg hfwd
  exact kt_equiv_zmod16_of_two_leaves hKRS dC dA

/-- **The Rokhlin-16 twin of the `hΦg` reduction** (`rokhlin_sixteen_of_residuals_phig`): the order-16
statement `Nat.card Ω₄^{Pin⁺} = 16` from the SAME reduced row (the `{hcyc, h2}` pair replaced by the
generator image `hΦg`). Pure transport of `Nat.card (ZMod 16) = 16` across the additive equivalence;
introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_phig
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_residuals_phig H row hA hB hcol hker hΦg
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-! ## §2. THE `h2` STANDALONE REDUCTION — `h2` ⟶ the sharp Kummer conjunct -/

/-- **`h2` reduced to the Kummer first-conjunct** (`kt_equiv_zmod16_of_residuals_kummerRep`): the same
conclusion as `kt_equiv_zmod16_of_residuals`, keeping `hcyc`, but with the 2-torsion binder `h2 : 2·k₀
= 0` REPLACED by the sharp geometric atom `hk : EmptySigmaRepresentable residualProv (ktKernelRep
residualProv)` — i.e. `k₀ = 8·[ℝP⁴]` is Pin⁺-bordant to a rank-0 (spin) representative, the Kummer
witness's FIRST conjunct (`KummerWitness.1`). This documents the honest standalone form of hypothesis
8: `h2` is not free-standing content — it follows from `hk` via the banked structural spin-sector
2-torsion `emptySigmaRepresentable_two_torsion`, consuming NO `KTNonSplit` (the LOWER `k₀ ≠ 0` bit) and
NO ÷32 conclusion (this is the ÷32-UPPER `σ(2·K3) = 32`, free from the sector). -/
theorem kt_equiv_zmod16_of_residuals_kummerRep
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (hk : EmptySigmaRepresentable residualProv (ktKernelRep residualProv)) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals H row hA hB hcol hker hcyc
    (emptySigmaRepresentable_two_torsion residualProv _ hk)

end SKEFTHawking.PinPlusKTBinderDischarge
