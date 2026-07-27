/-
# Phase 5q.H — the `hker` lane's SINGLE-WITNESS extraction, discharged from bordism gluing

`PinPlusKTDualSpinSubmanifold`'s header records the `hker` lane's walled step precisely: deriving the
per-element geometric supply from PURE kernel membership `spinForgetPhi prov x = 0` requires
**extracting a single tethered null-bordism witness** from `T2DataBordismGrp.mk … = 0`. `Quot.eq` on
`Quot (IsT2DataBordant)` yields only `Relation.EqvGen (IsT2DataBordant) …`; collapsing that chain to
one witness needs transitivity of the bordism relation, i.e. **bordism gluing**, absent by design
(`BordismGroup.lean` §4).

`T2BordismGluing` closed the logical half of that and proved (`gluesT2_iff_singleWitness`) that the
single-witness extraction is *equivalent* to gluing, so the step cannot be dodged by any cleverer use
of the quotient. This module spends that result on the lane itself:

* `exists_tetheredNullWitness` — from `GluesT2 (pinPlusCharPairData prov)`, every kernel element of
  the geometric forgetful `Φ = spinForgetPhi` yields a representative `p` together with a SINGLE
  tethered null-bordism `b` of it, its Hausdorff total space `b.W` (the ambient `W⁵`), and the
  carrier's own **W-tethered** structure along `b`. That is verbatim the extraction the wall named.

## ⛔ SCOPE FENCE — what this module deliberately does NOT do (round-13 hit, recorded)

The obvious next step — feeding the extracted `b.W` into `KTSharpnessSupplyGeo`'s `amb` field and
supplying `DualSpinFromW b.W (R.sig x)` per kernel element (an ambient-pinned, or
ambient-*family*-pinned, dual-spin supply) — **is a settled-dead fork and was removed from this
module after being built**:

* `hker-ambient-pin-does-not-restore-geometry` — `PinPlusKTHkerAmbPinGate.
  dualSpinFamily_iff_pointwise_thirtytwo_dvd` proves that for ANY index type, ANY ambient assignment
  (explicitly including `fun x => b.W` of the genuine tethered witness) and ANY signature assignment,
  a family of `DualSpinFromW` data exists **iff** `32 ∣ σ` holds pointwise. The ambient is
  universally quantified, so pinning it to the honest `b.W` — which is exactly what the extraction
  below makes possible — buys nothing.
* `hker-opener-supplyGeo-is-non-reducing` — `PinPlusKTHkerAmbPinGate.
  nonempty_ktSharpnessSupplyGeo_iff_hfwd` proves the consumed supply is EQUIVALENT to the `hfwd`
  conclusion it feeds.

So a `KerPhiSubDoubles`-from-gluing capstone routed through `kerPhiSubDoubles_of_row_of_supplyGeo`
would be TRUE and worth **nothing**: its dual-spin hypothesis is equivalent to assuming its own
target. Per the registry's own consequence line, `hker` needs a NEW interface that carries the
submanifold and DERIVES its intersection lattice (the `SpinSigmaAtomPkg` pattern) plus the
`w₁`-duality tie. **The extraction below is orthogonal to that fork and survives it**: any such new
interface is still keyed on the ambient null-bordism total space, so it still needs a single witness
— which is what this module supplies, and nothing more.

Fence `untethered-membrane-factors-relation` honored: the witness is the carrier's own W-tethered
`CharPairBorRealizedTethered`, never an untethered variant.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no sorry/axiom/native_decide/maxHeartbeats.
-/
import Mathlib
import SKEFTHawking.T2BordismGluing
import SKEFTHawking.PinPlusKTSpinForgetPhi

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.T2BordismGluing

namespace SKEFTHawking.PinPlusHkerSingleWitness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **THE SINGLE-WITNESS EXTRACTION, discharged from gluing.** Every kernel element of the geometric
forgetful `Φ = spinForgetPhi` yields a representative `p` and a SINGLE tethered null-bordism `b` of
it, with a Hausdorff total space `b.W` — the ambient `W⁵` — and the carrier's own W-tethered
structure along `b`.

This is exactly the step `PinPlusKTDualSpinSubmanifold`'s header records as walled: from `Φ x = 0`
one otherwise gets only `Relation.EqvGen (IsT2DataBordant) …` via `Quot.eq`, and collapsing that
chain to one witness is bordism gluing. `T2BordismGluing.gluesT2_iff_singleWitness` shows that
dependence is an *equivalence*, so `GluesT2` is the whole content of the walled step rather than a
convenient sufficient condition.

⚠ See the module header: consuming this witness as an *ambient pin* on `KTSharpnessSupplyGeo` is the
settled-dead fork `hker-ambient-pin-does-not-restore-geometry`. This theorem supplies the witness; it
does not, and must not, be routed into that shape. -/
theorem exists_tetheredNullWitness (prov : CharPairWProviderPerOp I k)
    (hglue : GluesT2 (pinPlusCharPairData prov))
    (x : DataBordismGrp (spinEmptyData prov)) (hx : spinForgetPhi prov x = 0) :
    ∃ (p : StrMfd (spinEmptyData prov)) (b : Bordism (I.prod (𝓡∂ 1)) p.1 emptySM),
      x = DataBordismGrp.mk (spinEmptyData prov) p ∧ T2Space b.W ∧
        Nonempty (CharPairBorRealizedTethered b p.2.val charPairBundledEmpty) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨b, hT2, hstr⟩ :=
    nullBordism_of_class_eq_zero (pinPlusCharPairData prov) hglue ⟨p.1, p.2.val⟩ hx
  exact ⟨p, b, rfl, hT2, hstr⟩

end SKEFTHawking.PinPlusHkerSingleWitness
