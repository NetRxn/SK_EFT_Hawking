/-
# Phase 5q.H close-out (block #195) — THE ROW INHABITATION: assembly hypotheses 2–4 shrunk to atoms

The end-to-end conditional `PinPlusKTAssemblyResiduals.kt_equiv_zmod16_of_residuals` carries an
8-hypothesis row; this module discharges the shape of **hypotheses 2–4** — `row`, `hA`, `hB` — by
re-expressing them at the FINEST-GRAIN named E1 / Freeze atoms, so the assembly's remaining geometry
becomes an explicit, honestly-named atom set rather than three coarse bundles. Pure statement-level
wiring — every discharge lemma already exists; NO new leaf `Prop` is minted, so nothing here needs
gate review.

## Triage inventory (open vs banked, per row field)

* **`row : SpinPresentationRow residualProv`** — NOT concretely inhabitable in-tree. It reduces
  (`PinPlusKTSpinSigmaAtom.spinPresentationRow_of_atoms`) to `{a, hdvd, g, hrank, hk3}`:
  - `a : SpinSigmaAtoms residualProv` — the disclosed **E1 atom bundle** (`fc`/`B`/`wu`/`pd`/`sig` as
    TOTAL functions on every `StrMfd (spinEmptyData residualProv)`). This is the ONE genuinely
    manifold-surgery-blocked residual (the whole spin intersection-form theory for every closed spin
    4-manifold); it is a NAMED atom, not fakeable. Its `even_unimod` obligation is DISCHARGED inside
    `spinSigmaPresentation_of_atoms` (`isEvenUnimodular_of_intPD`); its s2s2 hyperbolic pin reduces
    to the EZ cross value + a change-of-basis congruence (`SphereProdGramPinReduce`, #167); a
    concrete carrier element exists (`PinPlusKTSpinSigmaStockElement.sphere4Element`, #161).
  - `hdvd : ∀ x, 16 ∣ a.sig x` — Rokhlin `16 ∣ σ` (the E2 stack), consumed, not re-derived.
  - `g`/`hrank`/`hk3` — the K3 generator data (`b₂ = 22`, form `IntCongr` to `k3Form`); `σ[g] = −16`
    is DERIVED (`SpinPresentationRow.hg`), never assumed. Genuinely disclosed (no in-tree K3).
* **`hA : row.R.RealizesSphereProducts`** — Freeze A. Reduces
  (`PinPlusKTFreezeAssembly` / `HandleTradeSurgery.realizesSphereProducts_of_cobordism_and_base`) to
  the terminal pair `{HandleTradeCobordism, HyperbolicBase}` — the single raw handle-trace cobordism
  (Benedetti Prop 20.16 / Lemma 20.17) + the rank-0 nullbordism. Both are `Prop`s, manifold-surgery
  blocked; every lattice/count step around them is already kernel-pure.
* **`hB : row.R.SphereProductBounds`** — Freeze B (`mk s2s2 = 0`). Reduces
  (`SphereProductBounding.sphereProductBounds_of_bordant`) to the S²×S² nullbordism atom
  `IsDataBordant … s2s2 ∅`. Fully DISCHARGED (kernel-pure, no hypothesis) only on the concrete toy
  `trivialSpherePresentation` (`S²×S² = ∂(S²×D³)`, #35); on the genuine `spinEmptyData` carrier the
  distinguished `a.s2s2` element's bounding is the residual.

## What this module ships (all kernel-pure wiring, no new atom)
* `kt_equiv_zmod16_of_atom_residuals` / `rokhlin_sixteen_of_atom_residuals` — the assembly with
  `row` expanded to the E1 atom bundle `{a, hdvd, g, hrank, hk3}` (hA/hB kept on the built
  presentation). The row's single `R` field is replaced by the disclosed E1 bundle.
* `kt_equiv_zmod16_of_terminal_atoms` / `rokhlin_sixteen_of_terminal_atoms` — additionally with hA
  reduced to the terminal Freeze-A pair `{HandleTradeCobordism, HyperbolicBase}`. This is the
  finest-grain honest reduction of assembly hypotheses 2–4: the residual geometry is exactly
  {E1 disclosed bundle, Rokhlin, K3 generator data, one handle-trade cobordism, the rank-0 base,
  the S²×S² Freeze-B bound}.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTAssemblyResiduals
import SKEFTHawking.PinPlusKTSpinSigmaAtom
import SKEFTHawking.PinPlusKTFreezeAssembly
import SKEFTHawking.PinPlusKTSpinSigmaStockElement
import SKEFTHawking.SphereProductBounding

open scoped Manifold
open SKEFTHawking.SingularCohomologyInt
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
open SKEFTHawking.PinPlusKTSpinSigmaAtom
open SKEFTHawking.PinPlusKTAssemblyResiduals

namespace SKEFTHawking.PinPlusKTSpinRowInhabit

/-! ## §1. The assembly with `row` expanded to the disclosed E1 atom bundle. -/

/-- **THE END-TO-END CONDITIONAL, row expanded to E1 atoms** (`kt_equiv_zmod16_of_atom_residuals`):
`Ω₄^{Pin⁺} ≃+ ZMod 16` on the faithful tethered carrier, with the bundled `SpinPresentationRow` of
`kt_equiv_zmod16_of_residuals` replaced by its content — the disclosed E1 atom bundle
`a : SpinSigmaAtoms residualProv`, the Rokhlin residual `hdvd`, and the K3 generator data
`g`/`hrank`/`hk3`. `hA`/`hB` are the sphere-product freezes on the built presentation
`spinSigmaPresentation_of_atoms a`. Pure wiring: reassembles the row via
`spinPresentationRow_of_atoms` and fires the gate-certified assembly of record. Same conclusion type
as `kt_equiv_zmod16_of_residuals`. -/
theorem kt_equiv_zmod16_of_atom_residuals
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (a : SpinSigmaAtoms residualProv)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData residualProv))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form)
    (hA : (spinSigmaPresentation_of_atoms a).RealizesSphereProducts)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals H (spinPresentationRow_of_atoms a hdvd g hrank hk3)
    hA hB hcol hker hcyc h2

/-- **W-E corollary from the E1 atoms** (`rokhlin_sixteen_of_atom_residuals`):
`Nat.card Ω₄^{Pin⁺} = 16` from the same E1-atom row. Pure transport of `Nat.card (ZMod 16) = 16`
across the additive equivalence; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_atom_residuals
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (a : SpinSigmaAtoms residualProv)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData residualProv))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form)
    (hA : (spinSigmaPresentation_of_atoms a).RealizesSphereProducts)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_atom_residuals H a hdvd g hrank hk3 hA hB hcol hker hcyc h2
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-! ## §2. The finest-grain reduction — Freeze A threaded to its terminal pair. -/

/-- **THE END-TO-END CONDITIONAL, Freeze A at its terminal grain**
(`kt_equiv_zmod16_of_terminal_atoms`): as `kt_equiv_zmod16_of_atom_residuals`, but with `hA`
(`RealizesSphereProducts`) further reduced to its terminal Freeze-A pair — the raw handle-trace
cobordism `HandleTradeCobordism` (Benedetti Prop 20.16 / Lemma 20.17) and the rank-0 nullbordism
`HyperbolicBase` (Thm 20.14) — via
`SpinSigmaPresentation.realizesSphereProducts_of_cobordism_and_base`. This is the finest-grain honest
reduction of assembly hypotheses 2–4: the residual geometry is exactly {E1 disclosed bundle `a`,
Rokhlin `hdvd`, K3 generator data `g`/`hrank`/`hk3`, one handle-trade cobordism `hCob`, the rank-0
base `hBase`, the Freeze-B bound `hB`}. `hB` is kept at the named-freeze grain; its terminal
bordism form (`sphereProductBounds_of_bordant`, `S²×S² = ∂(S²×D³)`) is available where the S²×S²
nullbordism is in hand. -/
theorem kt_equiv_zmod16_of_terminal_atoms
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (a : SpinSigmaAtoms residualProv)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData residualProv))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form)
    (hCob : (spinSigmaPresentation_of_atoms a).HandleTradeCobordism)
    (hBase : (spinSigmaPresentation_of_atoms a).HyperbolicBase)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_atom_residuals H a hdvd g hrank hk3
    (SpinSigmaPresentation.realizesSphereProducts_of_cobordism_and_base _ hCob hBase)
    hB hcol hker hcyc h2

/-- **W-E corollary from the terminal atoms** (`rokhlin_sixteen_of_terminal_atoms`):
`Nat.card Ω₄^{Pin⁺} = 16` from the finest-grain atom set. Pure transport across the equivalence. -/
theorem rokhlin_sixteen_of_terminal_atoms
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (a : SpinSigmaAtoms residualProv)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (g : StrMfd (spinEmptyData residualProv))
    (hrank : (a.B g).rank = 22)
    (hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank)
        (interMatrix (a.fc g) (a.B g))) k3Form)
    (hCob : (spinSigmaPresentation_of_atoms a).HandleTradeCobordism)
    (hBase : (spinSigmaPresentation_of_atoms a).HyperbolicBase)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_terminal_atoms H a hdvd g hrank hk3 hCob hBase hB
    hcol hker hcyc h2
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-! ## §3. The K3 generator data packaged as the named `K3RealizingElement` carrier. -/

open SKEFTHawking.PinPlusKTSpinSigmaStock

/-- **THE END-TO-END CONDITIONAL, K3 residual as the named element** (`kt_equiv_zmod16_of_k3_element`):
as `kt_equiv_zmod16_of_atom_residuals`, but the loose K3 generator data `g`/`hrank`/`hk3` is packaged
into the single named residual carrier `K3RealizingElement a` (#161 Stock) — the honest atom for the
`σ = −16` generator (there is NO in-tree K3 manifold; the element is never inhabited, only disclosed).
This exhibits the phase's K3 residual as exactly a `K3RealizingElement residualProv` relative to the
E1 bundle, reusing the banked `K3RealizingElement.presentationRow` builder. -/
theorem kt_equiv_zmod16_of_k3_element
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (a : SpinSigmaAtoms residualProv)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (k : K3RealizingElement a)
    (hA : (spinSigmaPresentation_of_atoms a).RealizesSphereProducts)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals H (K3RealizingElement.presentationRow a hdvd k)
    hA hB hcol hker hcyc h2

/-- **W-E corollary from the K3 element** (`rokhlin_sixteen_of_k3_element`):
`Nat.card Ω₄^{Pin⁺} = 16` with the K3 residual packaged as `K3RealizingElement a`. -/
theorem rokhlin_sixteen_of_k3_element
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (a : SpinSigmaAtoms residualProv)
    (hdvd : ∀ x, (16 : ℤ) ∣ a.sig x)
    (k : K3RealizingElement a)
    (hA : (spinSigmaPresentation_of_atoms a).RealizesSphereProducts)
    (hB : (spinSigmaPresentation_of_atoms a).SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf residualProv)
    (hker : KerPhiSubDoubles residualProv)
    (hcyc : SpinImageCyclic residualProv)
    (h2 : ktKernelRep residualProv + ktKernelRep residualProv = 0) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_k3_element H a hdvd k hA hB hcol hker hcyc h2
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

end SKEFTHawking.PinPlusKTSpinRowInhabit
