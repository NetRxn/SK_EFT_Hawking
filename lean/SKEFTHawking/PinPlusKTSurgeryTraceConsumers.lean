/-
# Phase 5q.H W-D — SURGERY WAVE 4: the consumer instantiations (the TETHERED TRACE)

Wave 3 (`SingularSurgeryManifold.lean`) delivered `surgeryTraceBordism : Bordism J s t` (the
manifold obstruction discharged; `e`/`he_boundary` honest boundary inputs). The Wave-4 KEYSTONE
(`SingularSurgeryWeld.lean`) delivered `HandleAttachment.Weld.isClosedEmbedding_carrierMap` — the
membrane-into-carrier closed embedding (the two-region weld one dimension down). This module wires
both into the two convergence consumers:

* **`PinPlusKTSurgeryTrace.AmbientSurgeryDatum`** — the ambient KT §5 surgery datum, whose `b` field
  is a `surgeryTraceBordism` and whose `hBor` field is the tethered membrane, the tether's closed
  embedding supplied by the weld keystone (`borTetheredOfWeld`). The final reduction
  `ambientSurgeryDatum_of_traceWitness` bottoms the datum out in exactly: the wave-3 trace bordism
  `b`+`hT2`, the tethered membrane `hBor`, and the algebraic surgery data.
* **`SpinSigmaRoute.SpinSigmaPresentation.HandleTradeCobordism`** — the raw handle-trace cobordism
  `IsDataBordant ξ p ((S²×S²) ⊔ p')`, whose existential bordism is a `surgeryTraceBordism` and whose
  residual is the generic `ξ.Bor` tangential structure (`dataBordant_of_traceBor`).

Consumes the Track-2 / provider lane read-only. Additive module. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryWeld
import SKEFTHawking.SingularSurgeryManifold
import SKEFTHawking.PinPlusKTSurgeryTrace
import SKEFTHawking.HandleTradeSurgery

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

namespace SKEFTHawking.PinPlusKTSurgeryTraceConsumers

variable {k : WithTop ℕ∞}

/-! ## §1. The keystone-supplied tether — `CharPairBorRealizedTethered` from a membrane weld.

The load-bearing bridge: build the tethered characteristic-pair bordism datum where the tether
`ιW : C(↑real.Q, b.W)` is the membrane weld (keystone) transported through the two presentation
homeomorphisms — the membrane `real.Q` presented as a handle-attachment carrier `HAQ.carrier`, the
bordism carrier `b.W` as `HAW.carrier`. The tether's **closed embedding** — the F4 discipline the
whole tethered structure turns on — is supplied for FREE by `Weld.isClosedEmbedding_carrierMap`
composed with the two homeomorphisms (each a closed embedding). Only the glue-compatibility
(`glueσ`/`glueτ`, tying the membrane's boundary inclusion / clopen identifications to the bordism's
boundary map through the weld) and the membrane presentation remain as honest inputs. -/

section Bridge

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s t : SingularManifold.{0} PUnit.{1} k I}

/-- **The membrane weld supplies the tether** (the keystone → tethered-`Bor` bridge). Given the
item-1 admissibility `wadmP`, the Hausdorff carrier, the membrane realization `real`, its
Taylor-leg/Lagrangian kernel data, AND a presentation of the membrane-and-bordism carriers as a
handle-attachment weld (`weld : Weld HAQ HAW`, `hQ : real.Q ≃ₜ HAQ.carrier`, `hW : b.W ≃ₜ
HAW.carrier`) with the glue compatibility, assemble `CharPairBorRealizedTethered b σ τ`. The tether
`ιW = hW⁻¹ ∘ carrierMap ∘ hQ` is a closed embedding (keystone + two homeos), discharging the F4
tether discipline geometrically. -/
noncomputable def borTetheredOfWeld
    {b : Bordism (I.prod (𝓡∂ 1)) s t}
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (wadmP : WAdmPinned b) (hWT2 : T2Space b.W)
    (real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis)
    (htaylor : TaylorLegVanishes σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (hlag : JointLagrangian σ.q τ.q (real.toMembrane σ.q τ.q).L)
    {HAQ HAW : HandleAttachment} (weld : HandleAttachment.Weld HAQ HAW)
    (hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier) (hW : b.W ≃ₜ HAW.carrier)
    (glueσ : ∀ x : ↑(sub real.U),
        hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.U x))))
          = b.e (Sum.inl (σ.emb (real.homσ x))))
    (glueτ : ∀ x : ↑(sub real.Uᶜ),
        hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ x))))
          = b.e (Sum.inr (τ.emb (real.homτ x))))
    (chartQ : ChartedSpace MembraneModel ↑real.Q) :
    CharPairBorRealizedTethered b σ τ :=
  mkCharPairBorRealizedTethered wadmP hWT2 real htaylor hlag
    (⟨fun x => hW.symm (weld.carrierMap (hQ x)),
      hW.symm.continuous.comp (weld.carrierMap.continuous.comp hQ.continuous)⟩)
    ((hW.symm.isClosedEmbedding).comp
      (weld.isClosedEmbedding_carrierMap.comp hQ.isClosedEmbedding))
    glueσ glueτ chartQ

end Bridge

/-! ## §2. Consumer 1 — `AmbientSurgeryDatum`: the `b` field via `surgeryTraceBordism`, and the
reduction to the sharp residuals. -/

variable {prov : CharPairWProviderPerOp (𝓡 4) k}
variable {p : StrMfd (pinPlusCharPairData prov).toTangentialData}

/-- **The ambient trace bordism, via Wave-3's `surgeryTraceBordism`.** Re-exports the Wave-3 packaging
at the ambient base `X = PUnit`, `I = 𝓡 4` — the setting of the Pin⁺ carrier. The classifying map to
`PUnit` is trivial (a subsingleton, so `g`/`hg`/`hg_restrict` are supplied internally), leaving
exactly the honest geometric inputs: the smooth surgery datum `D` (the `D²×D³` 2-handle attachment +
its chart/weld stack) and the boundary identification `e`/`he_smooth`/`he_inj`/`he_boundary`. The
manifold obstruction is discharged inside `surgeryTraceBordism`. To fill `AmbientSurgeryDatum.b`
(`Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1`) the caller instantiates `D` with `D.J = (𝓡 4).prod (𝓡∂ 1)`,
`D.k = 0`, `s = p'.1`, `t = p.1`. -/
noncomputable def ambientTraceBordism
    (D : SmoothSurgeryChartDatum) [FiniteDimensional ℝ D.E']
    (s t : SingularManifold.{0} PUnit.{1} D.k (𝓡 4))
    (e : s.M ⊕ t.M → D.toSurgeryChartDatum.toHandleAttachment.carrier)
    (he_smooth : letI := D.toSurgeryChartDatum.carrierChartedSpace
      ContMDiff (𝓡 4) D.J D.k e)
    (he_inj : Function.Injective e)
    (he_boundary : letI := D.toSurgeryChartDatum.carrierChartedSpace
      Set.range e = D.J.boundary D.toSurgeryChartDatum.toHandleAttachment.carrier) :
    letI := D.toSurgeryChartDatum.carrierChartedSpace
    Bordism D.J s t :=
  letI := D.toSurgeryChartDatum.carrierChartedSpace
  surgeryTraceBordism D s t e he_smooth he_inj he_boundary
    (fun _ => PUnit.unit) continuous_const (by funext z; exact Subsingleton.elim _ _)

/-- **Consumer 1 — the AmbientSurgeryDatum reduction to its sharp residuals** (round-9 spec item 1
respected: the datum lives OFF the rank-0 fibre through `hx0`). Assembles `AmbientSurgeryDatum prov p`
from exactly: the algebraic surgery data (`x`/`hx0`/`hxq` and the surgered `p'`/`hrank`), the Wave-3
trace bordism `b` (a `surgeryTraceBordism`; cf. `ambientTraceBordism`) with its Hausdorff carrier
`hT2`, and the tethered membrane `hBor` (a `CharPairBorRealizedTethered`; its tether's closed
embedding via `borTetheredOfWeld`+the keystone). This is the mission's win-shape: the whole datum
bottoms out in the wave-3 boundary inputs + the trace-W admissibility (inside `hBor`) + the membrane
weld — nothing else. -/
def ambientSurgeryDatum_of_traceWitness
    (x : Fin p.2.n → ZMod 2) (hx0 : x ≠ 0) (hxq : p.2.q.q x = 0)
    (p' : StrMfd (pinPlusCharPairData prov).toTangentialData) (hrank : p'.2.n + 2 = p.2.n)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1) (hT2 : T2Space b.W)
    (hBor : Nonempty (CharPairBorRealizedTethered b p'.2 p.2)) :
    AmbientSurgeryDatum prov p where
  x := x
  hx0 := hx0
  hxq := hxq
  p' := p'
  hrank := hrank
  b := b
  hT2 := hT2
  hBor := hBor

/-- **Consumer 1 — the full keystone-to-datum path.** Assembles `AmbientSurgeryDatum prov p` from the
algebraic surgery data, the Wave-3 trace bordism `b`+`hT2`, the trace-W admissibility `wadmP`, and the
membrane weld presentation (`real`/`weld`/`hQ`/`hW`/glue). The tethered membrane `hBor` is built by
`borTetheredOfWeld` — so its tether's closed embedding comes for FREE from the weld keystone. Every
residual is sharply named: the algebraic data, the wave-3 boundary inputs (in `b`), the trace-W
admissibility `wadmP`, and the membrane realization + weld + glue. -/
noncomputable def ambientSurgeryDatum_of_weld
    (x : Fin p.2.n → ZMod 2) (hx0 : x ≠ 0) (hxq : p.2.q.q x = 0)
    (p' : StrMfd (pinPlusCharPairData prov).toTangentialData) (hrank : p'.2.n + 2 = p.2.n)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1) (hT2 : T2Space b.W)
    (wadmP : WAdmPinned b)
    (real : GeoRealizationTied (TopCat.of p'.2.surf.M) (TopCat.of p.2.surf.M) p'.2.basis p.2.basis)
    (htaylor : TaylorLegVanishes p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L)
    (hlag : JointLagrangian p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L)
    {HAQ HAW : HandleAttachment} (weld : HandleAttachment.Weld HAQ HAW)
    (hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier) (hW : b.W ≃ₜ HAW.carrier)
    (glueσ : ∀ x : ↑(sub real.U),
        hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.U x))))
          = b.e (Sum.inl (p'.2.emb (real.homσ x))))
    (glueτ : ∀ x : ↑(sub real.Uᶜ),
        hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ x))))
          = b.e (Sum.inr (p.2.emb (real.homτ x))))
    (chartQ : ChartedSpace MembraneModel ↑real.Q) :
    AmbientSurgeryDatum prov p :=
  ambientSurgeryDatum_of_traceWitness x hx0 hxq p' hrank b hT2
    ⟨borTetheredOfWeld wadmP hT2 real htaylor hlag weld hQ hW glueσ glueτ chartQ⟩

/-! ## §3. Consumer 2 — `HandleTradeCobordism`: the raw trace cobordism supplies the existential
`IsDataBordant`, residual = the `ξ.Bor` tangential structure. -/

section HandleTrade

open SKEFTHawking.SpinSigmaRoute
open Matrix

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {ξ : TangentialData X k I}

/-- **The instantiation shape — a trace bordism supplies `IsDataBordant`.** The raw single cobordism
`b : Bordism (I.prod (𝓡∂ 1)) p.1 q.1` (a `surgeryTraceBordism` at the handle shape) carrying a
tangential `ξ.Bor` structure IS a structured bordism, so it discharges `IsDataBordant ξ p q`
directly. The only residual beyond the wave-3 trace bordism is the `ξ.Bor` structure on it — for a
generic `ξ` this is the abstract tangential enrichment; for the Pin⁺ carrier it is the
`CharPairBorRealizedTethered` (consumer 1). -/
theorem dataBordant_of_traceBor {p q : StrMfd ξ}
    (b : Bordism (I.prod (𝓡∂ 1)) p.1 q.1) (hBor : Nonempty (ξ.Bor b p.2 q.2)) :
    IsDataBordant ξ p q :=
  ⟨b, hBor⟩

/-- **The ambient trace bordism (generic base) — the `b`-source for `HandleTradeCobordism`.**
Re-exports `surgeryTraceBordism` at a generic base `X`/`I`. Fixing `Ha` the `S²×S²`-handle and the
attaching-circle standardization gives the single handle-trace cobordism `p ↝ (S²×S²) ⊔ p'` whose
class shadow is Benedetti's `[p] = [S²×S²] + [p']`. The output `Bordism D.J s t` fills the
`IsDataBordant` existential once `D.J = I.prod (𝓡∂ 1)`, `D.k = k`, `s`/`t` the two ends. -/
noncomputable def spinTraceBordism
    (D : SmoothSurgeryChartDatum) [FiniteDimensional ℝ D.E']
    (s t : SingularManifold.{0} X D.k I)
    (e : s.M ⊕ t.M → D.toSurgeryChartDatum.toHandleAttachment.carrier)
    (he_smooth : letI := D.toSurgeryChartDatum.carrierChartedSpace
      ContMDiff I D.J D.k e)
    (he_inj : Function.Injective e)
    (he_boundary : letI := D.toSurgeryChartDatum.carrierChartedSpace
      Set.range e = D.J.boundary D.toSurgeryChartDatum.toHandleAttachment.carrier)
    (g : D.toSurgeryChartDatum.toHandleAttachment.carrier → X) (hg : Continuous g)
    (hg_restrict : g ∘ e = Sum.elim s.f t.f) :
    letI := D.toSurgeryChartDatum.carrierChartedSpace
    Bordism D.J s t :=
  letI := D.toSurgeryChartDatum.carrierChartedSpace
  surgeryTraceBordism D s t e he_smooth he_inj he_boundary g hg hg_restrict

/-- **The instantiation shape, documented against `HandleTradeCobordism`.** The terminal surgery
primitive `HandleTradeCobordism` demands, per form-splitting input, a residual `p'` (rank `m`) with
`IsDataBordant ξ p ((S²×S²) ⊔ p')`. `dataBordant_of_traceBor` shows each such `IsDataBordant` is
supplied by a raw handle-trace bordism `b` (a `spinTraceBordism` existential, `Ha` the `S²×S²`-handle)
carrying a `ξ.Bor` structure — so the residual of the whole primitive, per input, is exactly the
`(b, ξ.Bor)` pair: the wave-3 trace bordism and its tangential enrichment. The `HandleTradeSurgery`
chain (`realizesSphereProducts_of_cobordism_and_base`) already lands `HandleTradeCobordism` at the
Freeze-A `RealizesSphereProducts` freeze; this module pins its geometric residual to the surgery
trace. -/
theorem handleTradeCobordism_residual_is_traceBor (R : SpinSigmaPresentation ξ) :
    R.HandleTradeCobordism =
      (∀ (p : StrMfd ξ) (m : ℕ) (eqv : Fin 2 ⊕ Fin m ≃ Fin (R.rank p))
        (N' : Matrix (Fin m) (Fin m) ℤ), IsHyperbolicForm N' →
        IntCongr (R.form p) (Matrix.reindex eqv eqv (Matrix.fromBlocks Hyp 0 0 N')) →
        ∃ p' : StrMfd ξ, R.rank p' = m ∧
          IsDataBordant ξ p ⟨R.s2s2.fst.sum p'.fst, ξ.sumStr R.s2s2.snd p'.snd⟩) :=
  rfl

end HandleTrade

end SKEFTHawking.PinPlusKTSurgeryTraceConsumers
