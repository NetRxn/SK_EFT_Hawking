/-
# Phase 5q.H — THE dC COLLAPSE ATOM DISCHARGE (block #199): assembly hypothesis 5 (`hcol`)

This module attacks the fifth hypothesis of the end-to-end assembly
`PinPlusKTBinderDischarge.kt_equiv_zmod16_of_residuals_phig` (the 7-row):

  5. `hcol : RankZeroCollapsesToEmptySurf residualProv` — the dC leaf's collapse atom (every rank-0
     structure is one-step tethered bordant to an empty-Σ structure).

## Triage verdict (kernel-checked): genuine discharge is BLOCKED; the honest form is the per-object
`RankZeroCollapseDatum` supply.

* **No in-tree tether discharges `hcol` unconditionally.** The round-9 sphere-overhang freeze
  (`PinPlusKTSectorGeometricReduce` §1) and the round-12 gate spec 4 (`PinPlusResidualGate`, item 2)
  both stand: a discharge of `RankZeroCollapsesToEmptySurf` "must still supply the genuine
  terminal-KRS bounding datum". Every tethered op on representatives PRESERVES the surface (`revStr`,
  `cylBor`) or RAISES rank (`sumStr`/`addBor`); the only "→ empty" op is the rank-0 doubling
  (`σ ⊔ σ ~ ∅`), never a single `σ ~ (empty-Σ)`.
* **The rank-lowering trace does NOT supply the rank-0 collapse.** `AmbientSurgeryDatum prov p`
  (`PinPlusKTSurgeryTrace`) is the KRS lane's per-`p` surgery step, but it FORCES `0 < p.2.n`
  (`ambientSurgeryDatum_pos_rank`: a nonzero isotropic surgery circle `x : Fin p.2.n → ℤ/2` cannot
  live at rank 0) and drops rank by EXACTLY 2. It therefore STOPS at the rank-0 fibre; the terminal
  rank-0 → empty-SURFACE collapse (killing a nonempty trivial-`H¹` characteristic sphere) is a
  genuinely different construction — the "one more surgery" the round-9 gate named.

## What lands GREEN here (the honest reduction — NOT a discharge).

`RankZeroCollapseDatum prov p` — the terminal-step per-object collapse datum, STRUCTURALLY parallel to
`AmbientSurgeryDatum` (the gate-blessed rank-lowering shape) but at the rank-0 fibre: it packages the
empty-Σ target `p'`, the emptiness witness, and the honest collapse bordism `(b, hT2, hBor)` — the
genuine tethered membrane `CharPairBorRealizedTethered b p.2 p'.2` (the terminal-KRS bounding datum
"`Σ` bounds", realized by `emptySourceRealizationTied`, NOT the empty-structure fake). This is a
PER-OBJECT Type-valued datum, NOT a completeness Prop: quantified `∀`-`p` (over the rank-0 sector) it
supplies exactly `RankZeroCollapsesToEmptySurf`, EXACTLY as `ktSurgeryReduces_of_ambientDatumSupply`
reduces `KTSurgeryReduces` to the `∀`-`p` `AmbientSurgeryDatum` supply. It is the sharpest-possible
geometric statement of hypothesis 5: the collapse residual is now a named per-object bounding datum,
not an unstructured `∀∃` collapse-Prop.

`kt_equiv_zmod16_of_residuals_collapseDatum` REPLACES `hcol` with the datum supply — a 7-row still,
but with the completeness-adjacent `hcol` reduced to the finest-grain per-object atom.

**Circularity audit (by proof inspection)**: the reduction consumes ONLY the datum's bordism + tether
fields (pure geometry) and the banked `⟨b, hT2, hBor⟩ : IsT2DataBordant` packaging — NO `k₀`/
`KTNonSplit`-strength fact, NO `÷32` conclusion, NO output of the assembly. The base
`kt_equiv_zmod16_of_residuals_phig` is itself circularity-clean (#197 audit). CLEAN.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTBinderDischarge
import SKEFTHawking.PinPlusKTSurgeryTrace

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
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
open SKEFTHawking.PinPlusKTStepGate
open SKEFTHawking.PinPlusTraceLeafGate
open SKEFTHawking.PinPlusKTLeafGate

namespace SKEFTHawking.PinPlusKTCollapseDischarge

variable {k : WithTop ℕ∞}

variable {prov : CharPairWProviderPerOp (𝓡 4) k}

/-! ## §1. The terminal-step per-object collapse datum -/

/-- **THE RANK-0 COLLAPSE DATUM at `p`** — the terminal-step per-object bounding datum, the honest
finest-grain form of the dC overhang. Structurally parallel to `AmbientSurgeryDatum` (the gate-blessed
rank-lowering shape), but at the rank-0 fibre: instead of a surgery circle it packages the whole
membrane-kill collapse of the (trivial-`H¹`, possibly nonempty) characteristic sphere.

* `p'` / `hemp` — the surgered representative with a LITERALLY-empty characteristic surface `Σ' = ∅`.
* `b` / `hT2` / `hBor` — the collapse-trace bordism `W` from `p.1` to `p'.1` carrying a GENUINE tether
  `CharPairBorRealizedTethered b p.2 p'.2` (the terminal-KRS bounding datum "`Σ` bounds"; the membrane
  `Q` with `∂Q = Σ ⊔ ∅`, realized by `emptySourceRealizationTied`) — NOT the empty-structure fake
  (round-9 spec item 1 / round-12 §3 `rankZeroCollapse_target_in_sector`).

The disk / framing / bounding data underlying the collapse is GEOMETRIC INPUT — named here as the
existence of this datum (its discharge = the terminal-KRS bounding datum's construction, round-9
freeze), not proven from scratch. -/
structure RankZeroCollapseDatum (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) where
  /-- the surgered representative (terminal KT §5 step output). -/
  p' : StrMfd (pinPlusCharPairData prov).toTangentialData
  /-- **THE COLLAPSE**: the surgered representative's characteristic surface is LITERALLY empty. -/
  hemp : IsEmpty p'.2.surf.M
  /-- the collapse-trace bordism `W` from `p` to `p'`. -/
  b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 p'.1
  /-- its carrier is Hausdorff. -/
  hT2 : T2Space b.W
  /-- **THE GENUINE TETHER**: the collapse-trace membrane realizes `[p] = [p']` as a Pin⁺ bordism. -/
  hBor : Nonempty ((pinPlusCharPairData prov).Bor b p.2 p'.2)

/-! ## §2. The per-object bordism + the target-sector honesty -/

/-- **The datum realizes the one-step collapse bordism** `IsT2DataBordant p p'` — the thin
specialization of the `⟨b, hT2, hBor⟩` packaging (as in `mk_eq_of_tethered`) to the collapse datum's
carrier. This is the exact witness shape `RankZeroCollapsesToEmptySurf` demands at `p`. -/
theorem RankZeroCollapseDatum.isT2DataBordant
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData} (d : RankZeroCollapseDatum prov p) :
    IsT2DataBordant (pinPlusCharPairData prov) p d.p' :=
  ⟨d.b, d.hT2, d.hBor⟩

/-- **The collapse target is in the genuine spin sector** — `IsEmpty p'.2.surf.M ⟹ IsSpinSectorStr`
(the round-12 §3 anti-laundering fact re-exposed at the datum): the datum's empty-surface target lands
in the honest rank-0 sector through the `basis` linear equiv, so no hidden-positive-rank `p'` fakes the
overhang. -/
theorem RankZeroCollapseDatum.target_spinSector
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData} (d : RankZeroCollapseDatum prov p) :
    IsSpinSectorStr prov d.p' :=
  haveI := d.hemp
  spinSector_of_isEmpty_surf prov d.p' d.hemp

/-! ## §3. The datum-supply reduction -/

/-- **THE HONEST REDUCTION** — a `∀`-`p` (over the rank-0 sector) supply of the per-object collapse
datum discharges `RankZeroCollapsesToEmptySurf`. EXACTLY the `ktSurgeryReduces_of_ambientDatumSupply`
pattern (∀-`p` `AmbientSurgeryDatum` ⟹ `KTSurgeryReduces`), at the terminal rank-0 fibre. The datum is
a PER-OBJECT Type-valued shape, NOT a completeness Prop; the `∀` lives only in the supply hypothesis.
Circularity-clean: consumes only the datum's geometry, no `k₀`/`KTNonSplit`/`÷32`. -/
theorem rankZeroCollapsesToEmptySurf_of_datumSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      IsSpinSectorStr prov p → RankZeroCollapseDatum prov p) :
    RankZeroCollapsesToEmptySurf prov := by
  intro p hp
  exact ⟨(H p hp).p', (H p hp).hemp, (H p hp).isT2DataBordant⟩

/-! ## §4. The assembly wiring — `hcol` reduced to the collapse-datum supply -/

/-- **THE COLLAPSE-DATUM WIRING** (`kt_equiv_zmod16_of_residuals_collapseDatum`) — the same end-to-end
conclusion as `kt_equiv_zmod16_of_residuals_phig`, but with the collapse atom
`hcol : RankZeroCollapsesToEmptySurf` REPLACED by the finest-grain per-object supply
`hcolD : ∀ rank-0 p, RankZeroCollapseDatum residualProv p` (the terminal-KRS bounding datum, named).
A 7-row still, with the completeness-adjacent `hcol` reduced to its sharpest geometric form. -/
theorem kt_equiv_zmod16_of_residuals_collapseDatum
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_phig H row hA hB
    (rankZeroCollapsesToEmptySurf_of_datumSupply hcolD) hker hΦg

/-- **The Rokhlin-16 twin of the collapse-datum wiring**
(`rokhlin_sixteen_of_residuals_collapseDatum`): the order-16 statement
`Nat.card Ω₄^{Pin⁺} = 16` from the SAME reduced row (`hcol` replaced by the collapse-datum supply).
Pure transport of `Nat.card (ZMod 16) = 16` across the additive equivalence; introduces no new
residual atom. -/
theorem rokhlin_sixteen_of_residuals_collapseDatum
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_phig H row hA hB
    (rankZeroCollapsesToEmptySurf_of_datumSupply hcolD) hker hΦg

/-! ## §5. THE SECTOR-DIRECT WIRING — the weakest honest form of the collapse hypothesis.

The 2026-07-20 vetted hcolD route dossier's demand-narrowing (lead-verified against
`nonempty_ktSpinPresentationDatum_of_row` and `rankZeroClassCollapse_of_sectorIsGeometric`): the dC
leaf consumes ONLY the class-level `SectorIsGeometric` — the one-step `RankZeroCollapseDatum` /
`RankZeroCollapsesToEmptySurf` forms are STRICTLY STRONGER than the assembly needs. Because
`T2DataBordismGrp` is a `Quot` (its relation's equivalence closure supplies transitivity for free),
`SectorIsGeometric` is dischargeable by a STAGED sequence of tethered bordisms — no combined
single-trace `W` is required. These variants expose the headline at that weakest hypothesis. -/

/-- **THE SECTOR-DIRECT WIRING** — the same end-to-end conclusion as
`kt_equiv_zmod16_of_residuals_phig`, with the collapse hypothesis at its WEAKEST honest form:
the class-level `hsec : SectorIsGeometric` (each rank-0 broad-sector class admits SOME empty-Σ
representative — staged bordisms suffice), in place of the one-step `hcol`/`hcolD`. -/
theorem kt_equiv_zmod16_of_residuals_sector
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hsec : SectorIsGeometric residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) := by
  have hKRS : KernelReducesToSpin residualProv := kernelReducesToSpin_of_residualRow H
  have hfwd : ∀ x, spinForgetPhi residualProv x = 0 → (32 : ℤ) ∣ row.R.sig x :=
    spinForgetPhi_hfwd_of_ker_sub_doubles residualProv row.R row.hdvd hker
  obtain ⟨dC⟩ := nonempty_ktSpinPresentationDatum_of_row row hA hB hΦg hsec
  obtain ⟨dA⟩ :=
    nonempty_dualSpinForwardDatum_of_spinForgetPhi residualProv row.R row.g row.hg hΦg hfwd
  exact kt_equiv_zmod16_of_two_leaves hKRS dC dA

/-- **The Rokhlin-16 twin of the sector-direct wiring**: `Nat.card Ω₄^{Pin⁺} = 16` from the same
weakest-hypothesis row. Pure transport; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_sector
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hsec : SectorIsGeometric residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_residuals_sector H row hA hB hsec hker hΦg
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end SKEFTHawking.PinPlusKTCollapseDischarge
