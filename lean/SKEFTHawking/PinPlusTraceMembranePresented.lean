/-
# Phase 5q.H W-D arm 4 — THE MEMBRANE PRESENTATION (surgery-foundation wave-4 residual 3)

**Dimension discipline.** `W` = the 5-dimensional surgery trace bordism (`B ⊔_φ Ha`, the adjunction
space of `SingularSurgeryFoundation.lean`); `∂W = M ⊔ M′` are 4-manifolds; the surgered membrane
`Σ/Q` is 3-dimensional (`Q = Σ×[0,½] ∪ handle ∪ Σ′×[½,1]`, a dim-3 handle attachment); the handle
`Ha` models `D⁵` on `KTModel = E⁴ × H¹`, the attaching sphere `S ⊆ D⁵`. This file supplies the
*membrane presentation* datum on the trace pair `(W, ∂W)` — the counterpart of the W-admissibility
opener (`PinPlusTraceWAdmPinned.lean`, residual 2). Together the two named leaf rows are exactly what
the trace bordism `b = surgeryTraceBordism` needs to be a genuine TETHERED `Bor` witness.

**Why a named leaf row (§1–§2).** The consumer chain that turns the membrane content into a tethered
`Bor` datum is already complete and abstract: `borTetheredOfWeld` (the keystone-supplied tether,
`PinPlusKTSurgeryTraceConsumers.lean`) consumes `WAdmPinned b`, the Hausdorff carrier `hWT2`, the
DERIVED-basis realization `real : GeoRealizationTied … σ.basis τ.basis`, the membrane kernel data
(`htaylor`/`hlag`), the membrane weld (`weld : Weld HAQ HAW` + the two presentation homeomorphisms
`hQ`/`hW` + the pointwise glue `glueσ`/`glueτ`), and the charted-space certificate `chartQ`, and emits
`CharPairBorRealizedTethered b σ τ` — the tether's closed embedding supplied FREE by the weld keystone
(`Weld.isClosedEmbedding_carrierMap`). `TraceMembraneLeaves` bundles exactly that geometric input into
one named type; `toTethered` discharges the tethered datum from it. This is the "strictly-smaller row
of named geometric atoms" the residual-3 presentation reduces to — each field is a genuine geometric
atom (a realization, a weld, a homeomorphism, a charted-space instance, a glue equation), NOT a
completeness/bounding Prop.

**Fences respected.** `real` is typed `GeoRealizationTied … σ.basis τ.basis`, whose boundary bases are
DERIVED (`derivedEσ`/`derivedEτ`, `rfl`) from the carried cohomology bases — never free basis fields
(`realization-seam-basis-gauge-launders-e8`). The tether is the mandatory weld-supplied closed
embedding, consumed through `borTetheredOfWeld`; no untethered variant is rebuilt
(`untethered-membrane-factors-relation`). The membrane kernel `L` is the computed
`(real.toMembrane …).L = ker(bInc)` read through the derived bases, never a free field
(`free-membrane-kernel-kills-nonsplit`).

**The combined win-shape (§2–§3).** `traceTethered_of_leaves` takes the two named rows
(`TraceWAdmLeaves` for `WAdmPinned`, `TraceMembraneLeaves` for the membrane/weld/glue) and produces the
full `CharPairBorRealizedTethered`; `ambientSurgeryDatum_of_traceLeaves` / `dataBordant_of_traceLeaves`
wire it into the two KRS-supply consumers, so the trace's whole tethered-`Bor` obligation reduces to
exactly these two geometric leaf rows plus the algebraic surgery data.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSurgeryTraceConsumers
import SKEFTHawking.PinPlusTraceWAdmPinned

open scoped Manifold
open Topology
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.PinPlusKTSurgeryTrace
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers

namespace SKEFTHawking.PinPlusTraceMembranePresented

variable {k : WithTop ℕ∞}

/-! ## §1. The carrier-agnostic membrane-presentation leaf row and its tether discharge.

For ANY bordism `b : Bordism (I.prod (𝓡∂ 1)) s t` with structured ends `σ`/`τ`, the membrane
presentation bundles the geometric atoms `borTetheredOfWeld` consumes (everything except the
W-admissibility `WAdmPinned b`, which residual 2's `TraceWAdmLeaves` supplies). It is carrier-agnostic
— agnostic to the carrier's homeomorphism type — so it applies verbatim to the glued surgery-trace
carrier `W = B ⊔_φ Ha`. -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s t : SingularManifold.{0} PUnit.{1} k I}

/-- **The trace-pair membrane-presentation leaf row.** Bundles the geometric atoms the tethered
membrane datum needs on top of `WAdmPinned b` (residual 2): the Hausdorff carrier `hWT2`, the
DERIVED-basis realization `real` (its boundary bases pinned to `σ.basis`/`τ.basis` — the F2 fix), the
membrane kernel conditions `htaylor`/`hlag`, the membrane weld presentation
(`HAQ`/`HAW`/`weld`/`hQ`/`hW`), the pointwise glue `glueσ`/`glueτ` tying the membrane's boundary
inclusion through the weld to the bordism's boundary map, and the charted-space certificate `chartQ`
(`Q` charts over the 3-dim membrane model). Each field is a genuine geometric atom. -/
structure TraceMembraneLeaves (b : Bordism (I.prod (𝓡∂ 1)) s t)
    (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) where
  /-- **per-object certificate**: the trace carrier `W = b.W` is Hausdorff. -/
  hWT2 : T2Space b.W
  /-- The DERIVED-basis membrane realization `real : GeoRealizationTied … σ.basis τ.basis` — the
  boundary bases are the carried cohomology bases (`derivedEσ`/`derivedEτ`), not free fields. -/
  real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis
  /-- The membrane's computed kernel `L = ker(bInc)` is Taylor-leg-vanishing. -/
  htaylor : TaylorLegVanishes σ.q τ.q (real.toMembrane σ.q τ.q).L
  /-- The membrane's computed kernel `L` is jointly Lagrangian. -/
  hlag : JointLagrangian σ.q τ.q (real.toMembrane σ.q τ.q).L
  /-- the membrane presented as a handle attachment (the dim-3 `Q = B ⊔_φ Ha`). -/
  HAQ : HandleAttachment.{0, 0}
  /-- the bordism carrier presented as a handle attachment (the dim-5 `W = B ⊔_φ Ha`). -/
  HAW : HandleAttachment.{0, 0}
  /-- the membrane weld `Q ↪ W` — the two-region weld one dimension down. -/
  weld : HandleAttachment.Weld HAQ HAW
  /-- the membrane `Q` presented as `HAQ.carrier`. -/
  hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier
  /-- the bordism carrier `b.W` presented as `HAW.carrier`. -/
  hW : b.W ≃ₜ HAW.carrier
  /-- **glue (σ-end)**: the welded membrane boundary factors through `b.e ∘ Sum.inl ∘ σ.emb`. -/
  glueσ : ∀ x : ↑(sub real.U),
      hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.U x))))
        = b.e (Sum.inl (σ.emb (real.homσ x)))
  /-- **glue (τ-end)**: the welded membrane boundary factors through `b.e ∘ Sum.inr ∘ τ.emb`. -/
  glueτ : ∀ x : ↑(sub real.Uᶜ),
      hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ x))))
        = b.e (Sum.inr (τ.emb (real.homτ x)))
  /-- **manifold discipline**: `Q` charts over the 3-dim membrane model. -/
  chartQ : ChartedSpace MembraneModel ↑real.Q

/-- **The membrane leaf row discharges the tethered datum.** Feeding `TraceMembraneLeaves b σ τ`
together with a `WAdmPinned b` (residual 2's `TraceWAdmLeaves.toWAdmPinned`) through the
keystone-supplied `borTetheredOfWeld` produces the W-tethered characteristic-pair bordism datum. This
is the opener's headline: `CharPairBorRealizedTethered` on the trace is inhabited from — and only from
— the two named geometric leaf rows. -/
noncomputable def TraceMembraneLeaves.toTethered {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (wadmP : WAdmPinned b) (d : TraceMembraneLeaves b σ τ) :
    CharPairBorRealizedTethered b σ τ :=
  borTetheredOfWeld wadmP d.hWT2 d.real d.htaylor d.hlag d.weld d.hQ d.hW d.glueσ d.glueτ d.chartQ

end

/-! ## §2. The combined win-shape — the two named leaf rows produce the tethered witness. -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s t : SingularManifold.{0} PUnit.{1} k I}

/-- **The trace bordism IS a tethered `Bor` witness, modulo the two named leaf rows.** Given the
W-admissibility leaf row `wl : TraceWAdmLeaves b` (residual 2 — the Poincaré–Lefschetz atoms of the
trace pair) and the membrane-presentation leaf row `ml : TraceMembraneLeaves b σ τ` (residual 3 — the
realization/weld/glue atoms), the surgery-trace carrier carries a full `CharPairBorRealizedTethered b
σ τ`. This is the mission win-shape: the trace's tethered-`Bor` obligation bottoms out in exactly the
two geometric leaf rows — no completeness Prop between them. -/
noncomputable def traceTethered_of_leaves {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (wl : TraceWAdmLeaves b) (ml : TraceMembraneLeaves b σ τ) :
    CharPairBorRealizedTethered b σ τ :=
  ml.toTethered wl.toWAdmPinned

/-- **The two leaf rows force Brown-preservation through the membrane kernel** — the physics payload of
the membrane presentation. The membrane's Taylor-leg-vanishing + jointly-Lagrangian kernel `L`
(bundled in `ml` as `htaylor`/`hlag`) forces `brown(q_σ) = brown(q_τ)` via the anti-collapse engine
(`surgeryTrace_brown_eq_of_L` → `CharPairBorRealized.brown_eq`) — the KT surgery's mod-8 Brown/ABK
invariance read off the trace membrane, delivered directly by the two named leaf rows, INDEPENDENT of
the class-equality (`Quot.sound`) route. This is the falsifiable content the presentation buys: the
surgery step preserves the Brown grade. -/
theorem traceLeaves_brown_eq {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (wl : TraceWAdmLeaves b) (ml : TraceMembraneLeaves b σ τ) :
    σ.q.brown = τ.q.brown :=
  surgeryTrace_brown_eq_of_L (traceTethered_of_leaves wl ml)

end

/-! ## §3. The KRS-supply seam — wiring the two leaf rows into the trace consumers.

`I := 𝓡 4`, `k := 0` (the C⁰ collapse — all smoothness fields free). The two consumers
`ambientSurgeryDatum_of_traceWitness` (Consumer 1) and `dataBordant_of_traceBor` (Consumer 2) each
take the tethered membrane abstractly; feeding them `traceTethered_of_leaves` narrows their residual
from "produce a `CharPairBorRealizedTethered`" (a single unnamed obligation) to "produce the two named
geometric leaf rows" (transparent). -/

noncomputable section

variable {prov : CharPairWProviderPerOp (𝓡 4) k}
variable {p : StrMfd (pinPlusCharPairData prov).toTangentialData}

/-- **Consumer 1 via the two leaf rows.** Assembles `AmbientSurgeryDatum prov p` from the algebraic
surgery data (`x`/`hx0`/`hxq` + surgered `p'`/`hrank`), the Wave-3 trace bordism `b`, and the two
named geometric leaf rows: `wl : TraceWAdmLeaves b` (the trace-W admissibility) and
`ml : TraceMembraneLeaves b p'.2 p.2` (the membrane presentation). The datum's Hausdorff carrier and
the tether's Hausdorff carrier are the SAME leaf `ml.hWT2`. This is the sharpest KRS-supply shape: the
whole datum bottoms out in the wave-3 boundary inputs (in `b`) + the two leaf rows + the algebraic
data. -/
def ambientSurgeryDatum_of_traceLeaves
    (x : Fin p.2.n → ZMod 2) (hx0 : x ≠ 0) (hxq : p.2.q.q x = 0)
    (p' : StrMfd (pinPlusCharPairData prov).toTangentialData) (hrank : p'.2.n + 2 = p.2.n)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1)
    (wl : TraceWAdmLeaves b) (ml : TraceMembraneLeaves b p'.2 p.2) :
    AmbientSurgeryDatum prov p :=
  ambientSurgeryDatum_of_traceWitness x hx0 hxq p' hrank b ml.hWT2
    ⟨traceTethered_of_leaves wl ml⟩

/-- **Consumer 2 via the two leaf rows.** The raw single cobordism `b` carrying the tethered `Bor`
structure `traceTethered_of_leaves wl ml` (which IS the Pin⁺ carrier's `ξ.Bor`, definitionally
`CharPairBorRealizedTethered`) discharges `IsDataBordant` directly. Residual beyond the wave-3 trace
bordism `b`: exactly the two named leaf rows. -/
theorem dataBordant_of_traceLeaves
    {p q : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 q.1)
    (wl : TraceWAdmLeaves b) (ml : TraceMembraneLeaves b p.2 q.2) :
    IsDataBordant (pinPlusCharPairData prov).toTangentialData p q :=
  dataBordant_of_traceBor b ⟨traceTethered_of_leaves wl ml⟩

end

end SKEFTHawking.PinPlusTraceMembranePresented
