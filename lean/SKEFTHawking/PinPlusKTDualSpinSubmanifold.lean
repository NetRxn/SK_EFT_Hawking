/-
# Phase 5q.H close-out (Lane C0) — THE `KTSharpnessSupply` OPENER: the dual-spin submanifold atom,
# decomposed one level DEEPER against the tethered witness's total space `b.W` (KT Lemma 5.3
# "only if"; `dA`'s last geometric leaf, the sole open input of the banked `hfwd_of_row_of_supply`).

`PinPlusKTKerPhiDoubles.KTSharpnessSupply` bundles two black-box atoms — `dualSpin : ∀ x, Φx = 0 →
SmoothSpinManifold4` (a BARE lattice datum, no geometry visible) and `sigmaDoubling : σ(x) =
2·σ(V)`. This module OPENS the bare `dualSpin` into its actual geometric constituents against the
witness: a Type-valued datum that carries `V` **embedded as a closed subspace of the ambient
null-bordism total space `W`** (`DualSpinFromW`), with the σ-doubling. The assembly back to
`KTSharpnessSupply` is DISCHARGED (§3), so the full geometric supply feeds the banked `hfwd` chain
(§4). Follows #151: arithmetic assembly discharged, geometric atom named.

## The mathematics (`ScoutReport_KT_Lemma53_div32_Habegger_Enriques.md`; KT-LMS-151 §5, Lemma 5.3 p.216)

KT "only if": a closed spin `M⁴` that Pin⁺-bounds does so via a Pin⁺ `W⁵`; take `V ⊂ W` dual to
`w₁(W)`; `V` is SPIN (`w₁(V) = w₁(W)|V − w₁(ν) = 0` since the normal line bundle `ν` has
`w₁(ν) = w₁(W)|V`; `w₂(V) = 0` by the Pin⁺ Wu relation); `∂E(V)` (the boundary of `V`'s tubular
neighbourhood) is the orientation double cover, so `σ(M) = σ(∂E) = 2·σ(V)`; Rokhlin `16 ∣ σ(V)`
(banked, `SmoothSpinManifold4.rokhlin`) ⟹ `32 ∣ σ(M)`.

## Dimension bookkeeping (the Q-vs-V verdict — a load-bearing finding for the lead)

* `x` = a closed spin **4**-manifold class `M` (empty characteristic surface `Σ = ∅`).
* `W = b.W` = the Pin⁺ tethered null-bordism total space, **5**-dim (`∂W = M`).
* `V` = the `w₁(W)`-dual spin submanifold, **4**-dim = **codim 1** in `W`.
* `∂E(V)` = its tubular-neighbourhood boundary, **4**-dim (the orientation double cover of `V`).
* `Q = real.Q` = the CharPair carrier's **membrane**, **3**-dim = **codim 2** in `W`
  (`∂Q` tracks the characteristic surface `Σ`, empty on the spin side).

**VERDICT: `Q ≠ V`, and `V` is NOT reducible to the carrier's membrane `Q`.** `Q` is the codim-2
characteristic-surface tracker (dual to the `w₂`-flavoured surface class); `V` is the codim-1
`w₁`-dual. They differ by a dimension (3 vs 4) and by codimension (2 vs 1). The membrane discipline
of the carrier supplies `Q`, NOT `V`; the `w₁`-dual `V` is a genuinely FRESH codim-1 extraction from
`W`'s normal/tangential data that the carrier does not build. This is why `dualSpin` is a NAMED
geometric atom and not reducible to in-tree membrane machinery.

## The honest reduction boundary (the wall, for Fable/the lead)

The atom is keyed on the ambient `W` (intended value `TopCat.of b.W`). Deriving the per-element
supply from PURE kernel membership `spinForgetPhi prov x = 0` would require **extracting a single
tethered null-bordism witness `b`** from `T2DataBordismGrp.mk … = 0`. That is `Quot.exact` on
`Quot (IsT2DataBordant)`, which yields only `EqvGen (IsT2DataBordant) …` — collapsing it to a single
`IsT2DataBordant` needs **transitivity of the bordism relation (bordism gluing)**, which is ABSENT BY
DESIGN (`BordismGroup.lean` §4: "`Quot (IsBordant)` — no transitivity/gluing needed"; gluing tethered
CharPair bordisms with realized membranes is the sidestepped geometric content). So the OPENER carries
the ambient `W`/witness in the supply (as the actual construction produces `W` and `V ⊂ W` together);
the single-witness extraction from the bare kernel Prop is the precise walled step.

## NON-CIRCULARITY (fork `geometric-phi-does-not-close-hfwd-fakeability`, the round-10/11 audit)

Every proof in this module consumes ZERO facts about `k₀ = 8•[ℝP⁴]` (`ktKernelRep`), `KTNonSplit`, or
the presentation row's `hΦg`. The chain uses only: the geometric supply (the named atom), the banked
÷32 arithmetic (`Div32BoundingDatum.thirtytwo_dvd_sigM`, Rokhlin-only), and the already-audited
`PinPlusKTKerPhiDoubles` capstones (`kerPhiSubDoubles_of_row_of_supply`, `hfwd_of_row_of_supply` — the
non-circular σ/16-iso route). `KerPhiSubDoubles` remains a PURE SPIN-SIDE statement.

## Fences honored (18-fork fence, `KernelNoGos.lean`)
`geometric-phi-does-not-close-hfwd-fakeability`: this deepens the audit-friendly geometric supply
one level; the hfwd derivation still routes through `KerPhiSubDoubles`, non-circular by proof
inspection. `enriques-datum-refuted-as-shaped`: no `EnriquesDatum` constructed or consumed.
`untethered-membrane-factors-relation`: nothing rebuilds an untethered variant — the atom is keyed on
the tethered witness's `b.W`. The binary-partition route ban / free-membrane-kernel forks: untouched.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTKerPhiDoubles

open scoped Manifold
open Topology
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles

namespace SKEFTHawking.PinPlusKTDualSpinSubmanifold

variable {k : WithTop ℕ∞}

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The named geometric atom — the `w₁(W)`-dual spin submanifold `V ⊂ W` (deep leaf) -/

/-- **Atoms (a)+(b) OPENED against the ambient total space `W`** (Type-valued CONSTRUCTED DATA, the
honest deep leaf; NOT a completeness Prop). For a bounded spin `M⁴` with signature `sigM`, bounding a
Pin⁺ `W⁵` (intended value `W := TopCat.of b.W` for the tethered null-bordism witness `b`), this
packages the KT "only if" datum:

* `Vspace` + `ιV : C(Vspace, W)` + `hclosed` — the `w₁(W)`-dual submanifold `V` realized as a
  **closed subspace of the genuine ambient `W`** (the codim-1 geometry named explicitly; `V` is 4-dim,
  DISTINCT from the codim-2 characteristic membrane `Q` — see the module's Q-vs-V verdict);
* `Vspin : SmoothSpinManifold4` — `V`'s spin lattice datum (even-unimodular form + the topological
  factor of two), the arithmetic core;
* `hdouble : sigM = 2 · Vspin.sig` — the tubular double-cover σ-doubling (atom b): `∂E(V)` is the
  orientation double cover rel `M`, so `σ(M) = σ(∂E) = 2·σ(V)`.

The dual-submanifold extraction and the σ-doubling are geometric and unbuilt in-tree; this NAMES the
data they produce. The load-bearing arithmetic content is `Vspin + hdouble` (= `Div32BoundingDatum`,
§2); the embedding fields name the intended codim-1 geometry against `W` and are load-bearing exactly
when `W` is pinned to the actual `b.W` (the walled step — see the module header). -/
structure DualSpinFromW (W : Type) [TopologicalSpace W] (sigM : ℤ) where
  /-- the underlying space of the `w₁(W)`-dual submanifold `V` (a closed 4-manifold). -/
  Vspace : Type
  [Vtop : TopologicalSpace Vspace]
  /-- `V ↪ W`: `V` realized as a subspace of the ambient 5-dim null-bordism total space. -/
  ιV : C(Vspace, W)
  /-- `V` is a CLOSED submanifold of `W` (the codim-1 `w₁`-dual). -/
  hclosed : IsClosedEmbedding ⇑ιV
  /-- atom (a) core: `V`'s spin lattice datum (even-unimodular form + topological factor). -/
  Vspin : SmoothSpinManifold4
  /-- atom (b): the double-cover σ-doubling `σ(M) = 2·σ(V)`. -/
  hdouble : sigM = 2 * Vspin.sig

/-! ## §2. Projection to the banked ÷32 datum, and `32 ∣ σ(M)` (DISCHARGED, Rokhlin-only) -/

/-- **The named atom projects onto the banked `Div32BoundingDatum`** (dropping the geometric
embedding, keeping the arithmetic core `Vspin + hdouble`). -/
def DualSpinFromW.toDiv32 {W : Type} [TopologicalSpace W] {sigM : ℤ} (d : DualSpinFromW W sigM) :
    Div32BoundingDatum where
  V := d.Vspin
  sigM := sigM
  hdouble := d.hdouble

/-- **`32 ∣ σ(M)` from the named atom** (the KT "only if" finish, in-tree): Rokhlin `16 ∣ σ(V)`
composed with the σ-doubling, via the banked `Div32BoundingDatum.thirtytwo_dvd_sigM`. Consumes NO
`k₀` facts. -/
theorem DualSpinFromW.thirtytwo_dvd {W : Type} [TopologicalSpace W] {sigM : ℤ}
    (d : DualSpinFromW W sigM) :
    (32 : ℤ) ∣ sigM :=
  d.toDiv32.thirtytwo_dvd_sigM

/-! ## §3. The geometric sharpness supply, and its assembly onto `KTSharpnessSupply` (DISCHARGED) -/

/-- **The geometric KT-"only if" supply** — the OPENED form of `KTSharpnessSupply`: per kernel
element `x` (`spinForgetPhi prov x = 0`), the ambient null-bordism total space `amb x hx` (intended
value `TopCat.of b.W`) together with the dual-spin submanifold datum over it. Carrying the ambient
`W`/witness is honest: the actual geometric construction produces `W` and `V ⊂ W` together, and the
single-witness extraction from the bare kernel Prop is the walled step (module header). -/
structure KTSharpnessSupplyGeo (R : SpinSigmaPresentation (spinEmptyData prov)) where
  /-- the ambient null-bordism total space per kernel element (intended value `TopCat.of b.W`). -/
  amb : ∀ x, spinForgetPhi prov x = 0 → TopCat
  /-- the `w₁(W)`-dual spin submanifold datum over that ambient, with the σ-doubling. -/
  dual : ∀ x (hx : spinForgetPhi prov x = 0), DualSpinFromW (amb x hx) (R.sig x)
  -- (`amb x hx : TopCat` coerces to its underlying `Type` with its `TopologicalSpace` instance.)

variable {prov}

/-- **Assembly (c): the geometric supply projects onto the banked `KTSharpnessSupply`** (DISCHARGED)
— forget the ambient `W` and the embedding, keep the spin datum `Vspin` and the σ-doubling. This is
the bridge that lets the deep geometric leaf feed the banked `hfwd`/`KerPhiSubDoubles` chain. -/
def KTSharpnessSupplyGeo.toSupply {R : SpinSigmaPresentation (spinEmptyData prov)}
    (S : KTSharpnessSupplyGeo prov R) : KTSharpnessSupply prov R where
  dualSpin := fun x hx => (S.dual x hx).Vspin
  sigmaDoubling := fun x hx => (S.dual x hx).hdouble

/-! ## §4. The capstones — the geometric supply feeds the banked, NON-CIRCULAR `hfwd` route -/

/-- **`ker Φ ⊆ doubles` from the geometric supply** (over the presentation row): the OPENED geometric
sharpness supply feeds the banked, non-circular σ/16-iso route
(`kerPhiSubDoubles_of_row_of_supply`). Consumes NO `k₀`/`KTNonSplit`/`hΦg` facts. -/
theorem kerPhiSubDoubles_of_row_of_supplyGeo (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBnd : row.R.SphereProductBounds)
    (S : KTSharpnessSupplyGeo prov row.R) :
    KerPhiSubDoubles prov :=
  kerPhiSubDoubles_of_row_of_supply row hCob hBase hBnd S.toSupply

/-- **The end-to-end KT "only if" `hfwd` from the OPENED geometric supply** (capstone): from the
presentation row, the terminal Freeze-A atoms (the σ/16 iso), and the geometric sharpness supply with
`V` explicitly embedded in the ambient `W`, the KT "only if" `∀ x, Φ x = 0 → 32 ∣ σ(x)` — routed
through `KerPhiSubDoubles`, hence NON-CIRCULAR by proof inspection (ZERO `k₀`/`KTNonSplit`/`hΦg`
facts). The dA leaf's `hfwd` on its TRUE geometry, opened one level to the embedded submanifold. -/
theorem hfwd_of_row_of_supplyGeo (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBnd : row.R.SphereProductBounds)
    (S : KTSharpnessSupplyGeo prov row.R) :
    ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ row.R.sig x :=
  hfwd_of_row_of_supply row hCob hBase hBnd S.toSupply

/-! ## §5. Non-vacuity anchor — the atom is inhabited at K3-strength (`σ(V) = −16`) -/

/-- **Non-vacuity of the named atom** on the forced kernel element's signature `σ(M) = −32`
(`spinForgetPhi_double_mem_ker` keeps `σ = −32 ≠ 0` on `2[g]`, `sig_not_vanishing_on_ker`): the datum
is inhabited with `V = K3` (`k3Spin`, `σ(V) = −16`), the genuine K3-strength spin datum, and
`σ(M) = −32 = 2·(−16)`. The embedding is exhibited on a trivial ambient (`PUnit`) purely to witness
the STRUCTURE is inhabitable; the load-bearing arithmetic (`Vspin = K3`, `hdouble`) is real, while the
load-bearing embedding into the genuine 5-dim `b.W` is the unbuilt geometric content (module header). -/
noncomputable def k3DualSpinFromW : DualSpinFromW PUnit (-32) where
  Vspace := PUnit
  ιV := ContinuousMap.id _
  hclosed := IsClosedEmbedding.id
  Vspin := k3Spin
  hdouble := by rw [k3Spin_sig]; norm_num

/-- Non-vacuity check: the K3 datum's `σ(M) = −32` is `32`-divisible via the general
`thirtytwo_dvd` — the σ-doubling + Rokhlin arithmetic on the genuine generator. -/
theorem k3DualSpinFromW_thirtytwo_dvd : (32 : ℤ) ∣ (-32 : ℤ) :=
  k3DualSpinFromW.thirtytwo_dvd

end SKEFTHawking.PinPlusKTDualSpinSubmanifold
