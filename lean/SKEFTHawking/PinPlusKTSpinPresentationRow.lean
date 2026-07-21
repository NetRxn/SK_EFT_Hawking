/-
# Phase 5q.H close-out (Lane C0) — THE (R, g, hg) PRESENTATION ROW on the geometric-Φ source

**The shared σ-presentation row BOTH KT §5 leaves consume off the geometric `Φ`'s source
(`spinEmptyData prov`).** The round-11 binding spec (item 3) requires the presentation row to LAND
— as one named object — before any dA/dC progress claim, so that the two consumption sites
(`nonempty_ktSpinPresentationDatum_of_spinForgetPhi` / dC, `nonempty_dualSpinForwardDatum_of_cyclic`
/ dA) see ONE complete row rather than four scattered hypotheses.

## What the row is — and its honest atom line

`SpinPresentationRow prov` bundles the σ-presentation content of `Ω₄^{Spin}` on the empty-Σ
carrier:

* `R : SpinSigmaPresentation (spinEmptyData prov)` — the σ-presentation (signature hom + the E1
  intersection-form data). This is the ONE genuinely manifold-surgery-blocked field: a consistent
  intersection-form presentation for the WHOLE empty-Σ carrier needs the E1 `interMatrix` substrate
  wired to `CharPairStrBundled`, which is a separate deep build (flagged terminal in
  `PinPlusKTFreezeAssembly`). It is carried as a typed atom — NOT faked with a lattice-only object
  dressed as a manifold.
* `g`, `hrank`, `hk3` — the K3 generator, HONESTLY as "a `StrMfd (spinEmptyData prov)` whose E1
  presentation form is `IntCongr` to `k3Form`" (the DR's minimal irreducible geometric residual:
  *some E1 Gram matrix realizes the rank-22 K3 lattice `2·(−E8)⊕3·H`*). The signature identity
  `σ[g] = −16` is then DERIVED, not assumed (`SpinPresentationRow.hg`, via the banked
  `k3Form_latticeSig = −16` machinery `sig_neg16_of_form_congr_k3`) — no hand-built K3 manifold and
  no lattice-object-as-manifold fake (preemptive-strengthening: no defining-the-conclusion).
* `hdvd : ∀ x, 16 ∣ R.sig x` — Rokhlin `16 ∣ σ` (the E2 stack / `CharSurfaceRokhlinAssembly`),
  carried at the per-carrier residual grain the σ-engine consumes.

## What lands GREEN here (reductions, not atoms)

* `SpinPresentationRow.hg` — `σ[g] = −16` DERIVED from `hk3` + the banked K3 lattice signature.
* `dataBordismGrp_equiv_int_of_row` — the N1a headline `Ω₄^{Spin} ≅ ℤ` on the empty-Σ carrier,
  assembled from the row + the terminal Freeze-A atoms (`HandleTradeCobordism`, `HyperbolicBase`)
  + Freeze B (the assembly of record `dataBordismGrp_equiv_int_of_cobordism_and_base`).
* `h2_of_hΦg` — the companion `2·k₀ = 0` (the ÷32-upper) BANKED **from the generator image**
  `hΦg : Φ[g] = k₀`: `Φ[g]` is 2-torsion for free (`spinForgetPhi_add_self`, the empty-Σ sector
  2-torsion), so `k₀ + k₀ = 0` needs no independent Kummer/Enriques atom once `hΦg` is in hand.
* `nonempty_dualSpinForwardDatum_of_row` (dA) and `nonempty_ktSpinPresentationDatum_of_row`
  (+ `…_of_kernelCard`, the G9-4 route) (dC) — the row feeds each leaf's consumption site directly.

## Fences honored (the 18-fork fence)

`geometric-phi-does-not-close-hfwd-fakeability` (FRESH): the row NEVER discharges `hfwd` or
`SpinImageCyclic` — both stay as gated INPUTS to the dA wiring; nothing here touches the
`ker Φ ⊆ doubles` target. `enriques-datum-refuted-as-shaped`: no `EnriquesDatum` is constructed or
consumed (`h2` is banked from `hΦg`, not from a Kummer/Enriques carrier). The routes-apex fork
(KT §5 only) and the thin-carrier forks are respected: the row subtypes the FULL twice-gated bundle
via `spinEmptyData`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinForgetPhi
import SKEFTHawking.SpinSigmaGenerator
import SKEFTHawking.PinPlusKTFreezeAssembly

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTStepGate
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusKTSpinForgetPhi

namespace SKEFTHawking.PinPlusKTSpinPresentationRow

variable {k : WithTop ℕ∞}

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The presentation row -/

/-- **The (R, g, hg) presentation row on the empty-Σ carrier** — the σ-presentation content BOTH
KT §5 leaves consume off the geometric `Φ`'s source `spinEmptyData prov`, packaged as ONE named
object. `R` is the manifold-surgery-blocked σ-presentation atom; `g`/`hrank`/`hk3` are the K3
generator, HONESTLY as "an empty-Σ `StrMfd` whose E1 presentation form is `IntCongr` to `k3Form`"
(the DR's minimal irreducible geometric residual), so `σ[g] = −16` is DERIVED, not assumed;
`hdvd` is Rokhlin `16 ∣ σ`. -/
structure SpinPresentationRow where
  /-- the `Ω₄^{Spin} ≅ ℤ` σ-presentation (signature hom + the E1 intersection-form data). -/
  R : SpinSigmaPresentation (spinEmptyData prov)
  /-- Rokhlin `16 ∣ σ` (the E2 stack / `CharSurfaceRokhlinAssembly`), per-carrier residual. -/
  hdvd : ∀ x, (16 : ℤ) ∣ R.sig x
  /-- the K3 generator — an empty-Σ structured manifold. -/
  g : StrMfd (spinEmptyData prov)
  /-- `b₂(g) = 22` (the K3 rank). -/
  hrank : R.rank g = 22
  /-- the E1 presentation form of `g` realizes the K3 lattice `k3Form` (`2·(−E8)⊕3·H`). -/
  hk3 : IntCongr (Matrix.reindex (finCongr hrank) (finCongr hrank) (R.form g)) k3Form

variable {prov}

/-- **`hg` DERIVED** — `σ[g] = −16` from the K3 form-congruence field `hk3` + the banked K3 lattice
signature (`k3Form_latticeSig = −16`, `latticeSig`-congruence invariance). No hand-built K3, no
lattice-object-as-manifold fake: the signature identity is a consequence of the presentation. -/
theorem SpinPresentationRow.hg (row : SpinPresentationRow prov) :
    row.R.sig (DataBordismGrp.mk (spinEmptyData prov) row.g) = -16 :=
  sig_neg16_of_form_congr_k3 row.R row.g row.hrank row.hk3

/-! ## §2. The N1a headline from the row + the terminal Freeze-A atoms -/

/-- **`Ω₄^{Spin} ≅ ℤ` on the empty-Σ carrier, from the row** (the N1a headline): the row's
σ-presentation + K3 generator + Rokhlin, together with the terminal Freeze-A atoms
(`HandleTradeCobordism`, `HyperbolicBase`) and Freeze B (`SphereProductBounds`), assemble the
normalized-signature iso `σ = −16·e`, `e[g] = 1` (the assembly of record
`dataBordismGrp_equiv_int_of_cobordism_and_base`). The two Freeze-A atoms are the ONLY open
geometric input (manifold-surgery-blocked; carried as hypotheses, NOT discharged). -/
theorem dataBordismGrp_equiv_int_of_row (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hB : row.R.SphereProductBounds) :
    ∃ e : DataBordismGrp (spinEmptyData prov) ≃+ ℤ,
      (∀ x, row.R.sig x = -16 * e x) ∧ e (DataBordismGrp.mk (spinEmptyData prov) row.g) = 1 :=
  row.R.dataBordismGrp_equiv_int_of_cobordism_and_base hCob hBase hB row.g row.hg row.hdvd

/-! ## §3. `h2` (the ÷32-upper) banked from the generator image -/

/-- **`h2 = 2·k₀ = 0` BANKED from the generator image `hΦg`** (the ÷32-upper, FREE): once
`Φ[g] = k₀` is in hand, `k₀ + k₀ = 0` needs no independent Kummer/Enriques atom — `Φ[g]` is
2-torsion for free (`spinForgetPhi_add_self`, the empty-Σ sector 2-torsion), so rewriting along
`hΦg` gives it. (On the dA route `hΦg` is itself derived from `h2`, so there `h2` stays an input;
this lemma banks it wherever `hΦg` is supplied independently — e.g. the dC route.) -/
theorem h2_of_generatorImage (row : SpinPresentationRow prov)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g) = ktKernelRep prov) :
    ktKernelRep prov + ktKernelRep prov = 0 := by
  rw [← hΦg]
  exact spinForgetPhi_add_self prov (DataBordismGrp.mk (spinEmptyData prov) row.g)

/-! ## §4. The dA / dC consumption sites, fed by the row -/

/-- **dA wiring — `DualSpinForwardDatum` from the row**: Direction A's leaf from
`{row, hfwd, SpinImageCyclic, 2·k₀ = 0}`. `hfwd` (the KT "only if", each instance a
`Div32BoundingDatum`) and `SpinImageCyclic` stay GATED inputs — NEVER discharged here
(fence `geometric-phi-does-not-close-hfwd-fakeability`); the row supplies `{R, g, hg}` and the
generator image `hΦg` is derived (`spinForgetPhi_g_eq_ktKernelRep_of_cyclic`). -/
theorem nonempty_dualSpinForwardDatum_of_row (row : SpinPresentationRow prov)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ row.R.sig x)
    (hcyc : SpinImageCyclic prov)
    (h2 : ktKernelRep prov + ktKernelRep prov = 0) :
    Nonempty (DualSpinForwardDatum prov (spinEmptyData prov)) :=
  nonempty_dualSpinForwardDatum_of_cyclic prov row.R row.g row.hg hfwd hcyc h2

/-- **dC wiring — `KTSpinPresentationDatum` from the row, overhang route**: Direction C's leaf from
`{row, hA, hB, hΦg, SectorIsGeometric}`. The G8-5 overhang `SectorIsGeometric` is CONSUMED AS A
HYPOTHESIS (round-9 gate), NOT discharged; the row supplies `{R, g, hg, hdvd}`. -/
theorem nonempty_ktSpinPresentationDatum_of_row (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g) = ktKernelRep prov)
    (hsec : SectorIsGeometric prov) :
    Nonempty (KTSpinPresentationDatum prov (spinEmptyData prov)) :=
  nonempty_ktSpinPresentationDatum_of_spinForgetPhi prov row.R hA hB row.g row.hg row.hdvd hΦg hsec

/-- **dC wiring, `KTKernelCard` route (avoids the overhang, G9-4)**: Direction C's leaf from
`{row, hA, hB, hΦg, KTKernelCard}` — `hΦrange` recovered from the kernel-cardinality bound, so no
`SectorIsGeometric` input. The row supplies `{R, g, hg, hdvd}`. -/
theorem nonempty_ktSpinPresentationDatum_of_row_of_kernelCard (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g) = ktKernelRep prov)
    (hcard : KTKernelCard prov) :
    Nonempty (KTSpinPresentationDatum prov (spinEmptyData prov)) :=
  nonempty_ktSpinPresentationDatum_of_spinForgetPhi_of_kernelCard prov row.R hA hB row.g row.hg
    row.hdvd hΦg hcard

end SKEFTHawking.PinPlusKTSpinPresentationRow
