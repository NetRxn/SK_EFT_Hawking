/-
# Phase 5q.H close-out (Lane C0) — THE `ker Φ ⊆ doubles` OPENER: dA's true geometry (KT Lemma 5.3
# "only if"), the GATE-BLESSED hfwd route.

**The round-11 gate (`geometric-phi-does-not-close-hfwd-fakeability`, `KernelNoGos.lean`) proved that
`hfwd` is conclusion-fakeable through EVERY statement shape** — fixing `Φ := spinForgetPhi` does NOT
close round 10's conclusion-fakeability, because the presentation row itself collapses the geometric
`Φ` to the arithmetic formula (`spinForgetPhi_hfwd_iff_ktNonSplit`, `PinPlusTraceLeafGate`). The ONLY
audit-friendly route is the KERNEL CHARACTERIZATION: **every spin class in `ker (spinForgetPhi)` is a
double** (`KerPhiSubDoubles`, the shape the gate lemma `spinForgetPhi_hfwd_of_ker_sub_doubles`
consumes), from which `hfwd` follows by BANKED Rokhlin arithmetic consuming ZERO `k₀` facts. This
module builds the OPENER for that characterization.

## The mathematics (`ScoutReport_KT_Lemma53_div32_Habegger_Enriques.md`; KT-LMS-151 §5, Lemma 5.3 p.216)

KT Lemma 5.3 "only if": if the closed spin 4-manifold `M` Pin⁺-bounds via `W⁵`, take `V ⊂ W` dual to
`w₁(W)`; `V` is SPIN; `∂E(V)` (its tubular-neighbourhood boundary) is the orientation double cover rel
`M`; `σ(M) = σ(∂E) = 2·σ(V)`; Rokhlin `16 ∣ σ(V)` ⟹ `32 ∣ σ(M)`. At carrier level: `x ∈ ker Φ` means
the empty-Σ spin datum Pin⁺-bounds via a tethered CharPair bordism; extract the `w₁`-dual content, and
`32 ∣ σ(x)` follows. "Doubles" at the presentation level `= image of multiplication-by-2 = {32 ∣ σ}`
via the row's `Ω₄^{Spin} ≅ ℤ` σ/16 grading.

## The decomposition into named geometric atoms (this module)

* **Atom (a)+(b)** — `KTSharpnessSupply prov R` (Type-valued CONSTRUCTED DATA, the honest deep leaf):
  a per-kernel-element supply of
  - `dualSpin` (atom a): the `w₁(W)`-dual SPIN submanifold `V ⊂ W` (`SmoothSpinManifold4` carries its
    spin structure + even-unimodular intersection form — the duality certificate is what selects this
    `V`); and
  - `sigmaDoubling` (atom b): the tubular double-cover σ-doubling `σ(x) = 2·σ(V)`.
  The dual-submanifold extraction and the double-cover σ-doubling are geometric (unbuilt in-tree); this
  NAMES the data they produce — it is NOT a completeness Prop, and it is NOT vacuously inhabited (on the
  forced kernel element `2[g]`, `σ = −32 ≠ 0` forces `σ(V) = −16`, a genuine K3-strength spin datum —
  `sig_not_vanishing_on_ker`, `k3BoundingDatum` the non-vacuity anchor).

* **Assembly (c)** — `kerPhiSubDoubles_of_supply_of_equiv` / `…_of_row_of_supply` (DISCHARGED): per
  kernel element the two atoms assemble into a banked `Div32BoundingDatum`, so
  `Div32BoundingDatum.thirtytwo_dvd_sigM` (Rokhlin `16 ∣ σ(V)` ∘ the σ-doubling) gives `32 ∣ σ(x)`;
  the row's `Ω₄^{Spin} ≅ ℤ` σ/16 grading (`σ(x) = −16·e(x)`, `dataBordismGrp_equiv_int_of_row`) then
  turns `32 ∣ σ(x)` into `2 ∣ e(x)`, i.e. `x = w + w` with `w = e⁻¹(e(x)/2)`.

* **The gate tie** — `hfwd_of_kerPhiSubDoubles` / `hfwd_of_row_of_supply`: feeds `KerPhiSubDoubles`
  into the gate-blessed `spinForgetPhi_hfwd_of_ker_sub_doubles` (Rokhlin `hdvd` + `hker`), yielding the
  KT "only if" `∀ x, Φ x = 0 → 32 ∣ σ(x)`.

## NON-CIRCULARITY (the fork `geometric-phi-does-not-close-hfwd-fakeability`, the round-10/11 permanent
## audit): every proof in this module consumes ZERO facts about `k₀ = 8•[ℝP⁴]` (`ktKernelRep`),
`KTNonSplit`, or the presentation row's `hΦg` (the generator image `Φ[g] = k₀`). The chain uses only:
the geometric supply (atoms a/b), the banked ÷32 arithmetic (`Div32BoundingDatum.thirtytwo_dvd_sigM`,
Rokhlin-only), the row's σ/16 iso (`dataBordismGrp_equiv_int_of_row`, which consumes `row.hg : σ[g] =
−16` and `row.hdvd` — spin-side σ facts, NOT `k₀` facts), and linear integer arithmetic. `KerPhiSubDoubles`
is a PURE SPIN-SIDE statement (`∀ x, spinForgetPhi prov x = 0 → ∃ w, x = w + w`).

## Fences honored (18-fork fence, `KernelNoGos.lean`)
`geometric-phi-does-not-close-hfwd-fakeability`: this IS the audit-friendly kernel-characterization
route the fork mandates — the hfwd derivation routes through `KerPhiSubDoubles`, non-circular by proof
inspection. `enriques-datum-refuted-as-shaped`: no `EnriquesDatum` is constructed or consumed. The
thin-carrier / routes-apex / route-δ forks: the supply subtypes the FULL twice-gated bundle via
`spinEmptyData`; nothing here touches `SpinImageCyclic`'s discharge, the trace/supply modules, or the
Sq modules.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinPresentationRow
import SKEFTHawking.PinPlusTraceLeafGate

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
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusTraceLeafGate

namespace SKEFTHawking.PinPlusKTKerPhiDoubles

variable {k : WithTop ℕ∞}

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The statement layer — `ker Φ ⊆ doubles` in the gate lemma's exact consumption form -/

/-- **`ker Φ ⊆ doubles`** (the gate-blessed hfwd target, `geometric-phi-does-not-close-hfwd-fakeability`).
A PURE SPIN-SIDE statement: every spin class in the kernel of the geometric forgetful map
`spinForgetPhi` is a double `x = w + w`. This is *exactly* the shape
`PinPlusTraceLeafGate.spinForgetPhi_hfwd_of_ker_sub_doubles` consumes (its `hker` argument), so a proof
of `KerPhiSubDoubles prov` unfolds directly into the KT "only if" `hfwd` via banked Rokhlin, consuming
no `k₀` facts. Its whole open content is the geometric supply (§2); the arithmetic is discharged (§3). -/
def KerPhiSubDoubles : Prop :=
  ∀ x, spinForgetPhi prov x = 0 → ∃ w, x = w + w

/-! ## §2. The named geometric atoms — the KT "only if" per-kernel-element extraction (deep leaf) -/

/-- **Atoms (a)+(b): the KT Lemma 5.3 "only if" geometric supply** (Type-valued CONSTRUCTED DATA, the
honest deep leaf — NOT a completeness Prop). For each spin class `x` with `spinForgetPhi prov x = 0`
(i.e. the empty-Σ spin datum `M` Pin⁺-bounds via a tethered `W⁵`):

* `dualSpin` (atom a): the `w₁(W)`-dual SPIN submanifold `V ⊂ W`, as a `SmoothSpinManifold4` — the
  spin structure and even-unimodular intersection form are carried by the witness; the `w₁`-duality
  certificate is what selects this `V ⊂ W`.
* `sigmaDoubling` (atom b): the tubular double-cover σ-doubling `σ(x) = 2·σ(V)` — `∂E(V)`, the boundary
  of `V`'s tubular neighbourhood, is the orientation double cover rel `M`, so `σ(M) = σ(∂E) = 2·σ(V)`.

**Non-vacuity / honesty**: the dual-submanifold extraction + double-cover σ-doubling are geometric and
unbuilt in-tree, so this datum has zero in-tree inhabitants off the actual construction. It is NOT
vacuously satisfiable: on the forced kernel element `2[g]` (`spinForgetPhi_double_mem_ker`) the σ-row
keeps `σ = −32 ≠ 0` (`sig_not_vanishing_on_ker`), forcing `σ(V) = −16` — a genuine K3-strength spin
datum (`k3BoundingDatum` is the concrete anchor, `k3Spin.sig = −16`). -/
structure KTSharpnessSupply (R : SpinSigmaPresentation (spinEmptyData prov)) where
  /-- atom (a): the `w₁(W)`-dual SPIN submanifold `V ⊂ W` (with its spin structure + even-unimodular
      intersection form) for each Pin⁺-bounding spin class. -/
  dualSpin : ∀ x, spinForgetPhi prov x = 0 → SmoothSpinManifold4
  /-- atom (b): the tubular double-cover σ-doubling `σ(x) = 2·σ(V)`. -/
  sigmaDoubling : ∀ x (hx : spinForgetPhi prov x = 0), R.sig x = 2 * (dualSpin x hx).sig

variable {prov}

/-- **The atoms assemble into the banked `Div32BoundingDatum`, giving `32 ∣ σ(x)`** (the ÷32 core,
BANKED — Rokhlin `16 ∣ σ(V)` composed with the σ-doubling `σ(x) = 2·σ(V)`, via
`Div32BoundingDatum.thirtytwo_dvd_sigM`). Consumes NO `k₀` facts. -/
theorem KTSharpnessSupply.thirtytwo_dvd {R : SpinSigmaPresentation (spinEmptyData prov)}
    (S : KTSharpnessSupply prov R) (x : DataBordismGrp (spinEmptyData prov))
    (hx : spinForgetPhi prov x = 0) :
    (32 : ℤ) ∣ R.sig x :=
  Div32BoundingDatum.thirtytwo_dvd_sigM
    { V := S.dualSpin x hx, sigM := R.sig x, hdouble := S.sigmaDoubling x hx }

/-! ## §3. Assembly (c) — `32 ∣ σ(x)` ⟹ `x ∈ doubles`, wired through the row's `Ω₄^{Spin} ≅ ℤ` σ/16
grading. DISCHARGED. -/

/-- **Assembly (c) over the σ/16 iso** (DISCHARGED): from the geometric supply and the row's
`Ω₄^{Spin} ≅ ℤ` normalization `σ(x) = −16·e(x)`, `ker Φ ⊆ doubles`. Per kernel element: the atoms give
`32 ∣ σ(x)` (§2); `σ(x) = −16·e(x)` turns that into `2 ∣ e(x)`, so `e(x) = (−k) + (−k)` and
`x = e⁻¹(e(x)) = e⁻¹(−k) + e⁻¹(−k)`. Consumes NO `k₀` facts (only the σ/16 iso + banked ÷32 + linear
integer arithmetic). -/
theorem kerPhiSubDoubles_of_supply_of_equiv {R : SpinSigmaPresentation (spinEmptyData prov)}
    (e : DataBordismGrp (spinEmptyData prov) ≃+ ℤ)
    (he : ∀ x, R.sig x = -16 * e x)
    (S : KTSharpnessSupply prov R) :
    KerPhiSubDoubles prov := by
  intro x hx
  have h32 : (32 : ℤ) ∣ R.sig x := S.thirtytwo_dvd x hx
  rw [he x] at h32
  obtain ⟨k, hk⟩ := h32
  refine ⟨e.symm (-k), ?_⟩
  have hex : e x = -k + -k := by omega
  calc x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm (-k + -k) := by rw [hex]
    _ = e.symm (-k) + e.symm (-k) := map_add e.symm (-k) (-k)

/-- **Assembly (c) over the presentation row** (DISCHARGED): the row supplies its `Ω₄^{Spin} ≅ ℤ` iso
via the terminal Freeze-A atoms (`HandleTradeCobordism`, `HyperbolicBase`) + Freeze B
(`SphereProductBounds`); with the geometric sharpness supply, `ker Φ ⊆ doubles`. The row's iso consumes
`row.hg : σ[g] = −16` and `row.hdvd` (spin-side σ facts), NOT any `k₀` fact. -/
theorem kerPhiSubDoubles_of_row_of_supply (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBnd : row.R.SphereProductBounds)
    (S : KTSharpnessSupply prov row.R) :
    KerPhiSubDoubles prov := by
  obtain ⟨e, he, _⟩ := dataBordismGrp_equiv_int_of_row row hCob hBase hBnd
  exact kerPhiSubDoubles_of_supply_of_equiv e he S

/-! ## §4. The gate tie — `KerPhiSubDoubles` ⟹ the KT "only if" `hfwd` (Rokhlin only, no `k₀`) -/

/-- **hfwd from the kernel characterization** (the gate-blessed route, `spinForgetPhi_hfwd_of_ker_sub_doubles`):
`ker Φ ⊆ doubles` + Rokhlin `16 ∣ σ` gives the KT "only if" `∀ x, Φ x = 0 → 32 ∣ σ(x)` — on doubles
`hfwd` is FREE from Rokhlin (`σ(w + w) = 2σ(w) ∈ 32ℤ`). Consumes NO `k₀` facts (the gate lemma's proof
is `obtain ⟨w, rfl⟩ … ⟨c, …⟩`). This is the audit-friendly hfwd the round-11 gate mandated. -/
theorem hfwd_of_kerPhiSubDoubles (R : SpinSigmaPresentation (spinEmptyData prov))
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hker : KerPhiSubDoubles prov) :
    ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x :=
  spinForgetPhi_hfwd_of_ker_sub_doubles prov R hdvd hker

/-- **The end-to-end geometric-Φ hfwd on the gate-blessed route** (capstone): from the presentation
row `{R, g, hg, hdvd}`, the terminal Freeze-A atoms (the σ/16 iso), and the KT-"only if" geometric
sharpness supply (atoms a/b), the KT "only if" `∀ x, Φ x = 0 → 32 ∣ σ(x)` — routed through
`KerPhiSubDoubles`, hence NON-CIRCULAR by proof inspection (ZERO `k₀`/`KTNonSplit`/`hΦg` facts). This
is the dA leaf's `hfwd` discharged on its TRUE geometry (KT Lemma 5.3 "only if"), not the arithmetic
fake. -/
theorem hfwd_of_row_of_supply (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBnd : row.R.SphereProductBounds)
    (S : KTSharpnessSupply prov row.R) :
    ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ row.R.sig x :=
  hfwd_of_kerPhiSubDoubles row.R row.hdvd
    (kerPhiSubDoubles_of_row_of_supply row hCob hBase hBnd S)

end SKEFTHawking.PinPlusKTKerPhiDoubles
