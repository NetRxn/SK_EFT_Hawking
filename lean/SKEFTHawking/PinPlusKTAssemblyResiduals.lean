/-
# Phase 5q.H — THE ASSEMBLY WIRING (block #193): the end-to-end conditional `kt_equiv_zmod16`

This module lands the ONE theorem that makes the phase's ENTIRE remaining geometric obligation
visible as a single conditional: `kt_equiv_zmod16_of_residuals`, whose CONCLUSION is the final
target shape (`Ω₄^{Pin⁺} ≃+ ZMod 16` on the faithful tethered carrier — the same conclusion type as
`PinPlusKTLeafGate.kt_equiv_zmod16_of_two_leaves`) and whose HYPOTHESIS LIST is exactly the CURRENT
residual atoms — the deepest already-gated reductions of each of the three leaves {KRS, dC, dA}.

The gate round 12 (`PinPlusResidualGate`) verified the assembly seams of
`kt_equiv_zmod16_of_two_leaves`: it consumes `{hKRS, dC, dA}` with no ungated seam. This module
composes the deepest suppliers of those three inputs into a single statement, over a CONCRETE
provider `residualProv` produced UNCONDITIONALLY by `nonempty_charPairWProviderPerOp` (the provider
is discharged, never hypothesized — round-7 gate `PASSED` the carrier; the provider inhabits with no
open residual).

## The three leaves, deepest current form (provenance per hypothesis in the theorem docstring)
* **KRS leaf** ← `kernelReducesToSpin_of_residualRow` (module `PinPlusTraceCapstoneResidualRow`,
  gate round 12 §4/§5): the ∀-`p` `KRSResidualRow` supply. Kept as the ∀-`p` row (round-12 spec 3),
  never weakened to a per-instance.
* **dC leaf** ← `nonempty_ktSpinPresentationDatum_of_row_of_collapse` (module
  `PinPlusKTSectorGeometricReduce`, round-9 freeze / gate round 12 §3): the collapse atom
  `RankZeroCollapsesToEmptySurf` = the per-structure bounding datum, plus the presentation row's
  freezes and the derived generator image.
* **dA leaf** ← the HONEST hfwd route `PinPlusTraceLeafGate.spinForgetPhi_hfwd_of_ker_sub_doubles`
  on the geometric `Φ = spinForgetPhi` (module `PinPlusKTKerPhiDoubles` /
  `PinPlusKTSpinPresentationRow`): the kernel characterization `KerPhiSubDoubles` (= `ker Φ ⊆
  doubles`), NOT `hfwd`/`KTNonSplit`-strength directly (round-11 fork
  `geometric-phi-does-not-close-hfwd-fakeability`). The dA datum is built through the genuine
  `spinForgetPhi` whose ambient is the tethered witness — NOT the free-`amb` `DualSpinConstruction`
  (round-12 fork `dual-spin-opened-construction-conclusion-fakeable`, spec 1).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`. Pure statement-level wiring — every discharge lemma exists.
-/
import Mathlib
import SKEFTHawking.PinPlusKTLeafGate
import SKEFTHawking.PinPlusKTSpinPresentationRow
import SKEFTHawking.PinPlusKTKerPhiDoubles
import SKEFTHawking.PinPlusKTSectorGeometricReduce
import SKEFTHawking.PinPlusTraceLeafGate
import SKEFTHawking.PinPlusTraceCapstoneResidualRow
import SKEFTHawking.PinPlusCylComponentClsIdentDisc

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusTraceLeafGate
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusKTLeafGate

namespace SKEFTHawking.PinPlusKTAssemblyResiduals

/-- **THE CANONICAL char-pair `W`-provider** — the UNCONDITIONAL provider, produced by
`nonempty_charPairWProviderPerOp` (round-7 gate `PASSED` the carrier; the provider inhabits with no
open residual). Fixing this concrete provider is how the assembly INSTANTIATES the provider rather
than hypothesizing it: the phase's remaining obligation is the residual atoms below, NOT the
provider. -/
noncomputable def residualProv : CharPairWProviderPerOp (𝓡 4) 0 :=
  (SKEFTHawking.PinPlusCylComponentClsIdentDisc.nonempty_charPairWProviderPerOp
    (I := 𝓡 4) (k := 0)).some

/-- **THE END-TO-END CONDITIONAL** — `Ω₄^{Pin⁺} ≃+ ZMod 16` on the faithful tethered carrier from the
CURRENT residual atoms. This is the single authoritative statement of everything that remains open in
Phase 5q.H: discharge these hypotheses and the Kirby–Taylor `Ω₄^{Pin⁺} ≅ ℤ/16` lands unconditionally.
Same conclusion type as `kt_equiv_zmod16_of_two_leaves`; the provider is instantiated, not assumed.

Residual atoms (deepest already-gated reduction of each leaf):
* `H` — **[KRS leaf | gate round 12 §4/§5 · `PinPlusTraceCapstoneResidualRow`]** the ∀-`p`
  `KRSResidualRow` supply (one residual row per non-spin Brown-0 representative of positive
  enhancement rank). Discharges `KernelReducesToSpin` via `kernelReducesToSpin_of_residualRow`;
  kept as the ∀-`p` row (round-12 spec 3), never a per-instance.
* `row` — **[presentation infra | `PinPlusKTSpinPresentationRow`]** the `Ω₄^{Spin} ≅ ℤ`
  σ-presentation row (`R`, Rokhlin `hdvd`, the K3 generator `g` with `b₂ = 22` / `hk3`).
* `hA`, `hB` — **[Freeze-A/B | `PinPlusKTSpinPresentationRow`]** the `n·H` handle-trade realization
  and the `S²×S²` bound on `row.R`.
* `hcol` — **[dC leaf | round-9 freeze / gate round 12 §3 · `PinPlusKTSectorGeometricReduce`]** the
  concrete collapse atom `RankZeroCollapsesToEmptySurf` (every rank-0 structure is one-step tethered
  bordant to an empty-Σ structure — the per-structure bounding datum), the honest dC overhang.
* `hker` — **[dA leaf | round-11 fork `geometric-phi-does-not-close-hfwd-fakeability` ·
  `PinPlusKTKerPhiDoubles`]** the kernel characterization `KerPhiSubDoubles` (`ker Φ ⊆ doubles`),
  the gate-blessed hfwd target — taken INSTEAD of `hfwd`/`KTNonSplit`-strength (which the fork
  showed are interderivable given the row).
* `hcyc` — **[dA leaf | `PinPlusKTKernelSpinRoute`]** `SpinImageCyclic` (the spin image is cyclic),
  the ÷32-upper input the derived generator image `hΦg` consumes.
* `h2` — **[dA leaf | KT Lemma 5.3 ÷32-upper]** `2·k₀ = 0` (the kernel representative is 2-torsion).

The dA datum is built through the genuine geometric `Φ = spinForgetPhi` (ambient = the tethered
witness), NOT the free-`amb` `DualSpinConstruction` (round-12 fork
`dual-spin-opened-construction-conclusion-fakeable`, spec 1). -/
theorem kt_equiv_zmod16_of_residuals
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) := by
  -- KRS leaf: the ∀-`p` residual row supply discharges the deep KT §5 kernel-null binder.
  have hKRS : KernelReducesToSpin residualProv := kernelReducesToSpin_of_residualRow H
  -- dA's honest `hfwd` (KT Lemma 5.3 "only if"): FREE on doubles from Rokhlin, given `ker Φ ⊆ doubles`.
  have hfwd : ∀ x, spinForgetPhi residualProv x = 0 → (32 : ℤ) ∣ row.R.sig x :=
    spinForgetPhi_hfwd_of_ker_sub_doubles residualProv row.R row.hdvd hker
  -- the generator image `Φ[g] = k₀`, derived (non-circular: no `k₀`/`KTNonSplit` facts).
  have hΦg :
      spinForgetPhi residualProv (DataBordismGrp.mk (spinEmptyData residualProv) row.g)
        = ktKernelRep residualProv :=
    spinForgetPhi_g_eq_ktKernelRep_of_cyclic residualProv row.R row.g row.hg hfwd hcyc h2
  -- dC leaf: the presentation row + the concrete collapse atom yield `KTSpinPresentationDatum`.
  obtain ⟨dC⟩ := nonempty_ktSpinPresentationDatum_of_row_of_collapse row hA hB hΦg hcol
  -- dA leaf: the row + honest hfwd + cyclic image + 2-torsion yield `DualSpinForwardDatum`.
  obtain ⟨dA⟩ := nonempty_dualSpinForwardDatum_of_row row hfwd hcyc h2
  -- the gate-certified assembly of record fires with the three real leaf inputs.
  exact kt_equiv_zmod16_of_two_leaves hKRS dC dA

/-! ## W-E — the Rokhlin-16 corollary (pure wiring from the equivalence). -/

/-- **W-E — THE ROKHLIN-16 COROLLARY** (`rokhlin_sixteen_of_residuals`): from the SAME residual row
that discharges the assembly, the faithful Pin⁺ bordism carrier has EXACTLY 16 elements —
`Nat.card Ω₄^{Pin⁺} = 16`. This is the project's recorded Rokhlin-16 target form (the order-16
statement, paralleling `PinPlusKTExtension.kt_card_eq_16`): the ABK/Brown grade takes 16 values,
so the signature of a closed spin representative is well-defined mod 16 — Rokhlin's theorem in Pin⁺
bordism form. PURE statement-level wiring from `kt_equiv_zmod16_of_residuals` (transport of
`Nat.card (ZMod 16) = 16` back across the additive equivalence); it introduces NO new residual atom.
The `= 16` (not `≤ 16`) is the non-vacuous form: it forces `Finite` on the carrier. -/
theorem rokhlin_sixteen_of_residuals
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_residuals H row hA hB hcol hker hcyc h2
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end SKEFTHawking.PinPlusKTAssemblyResiduals
