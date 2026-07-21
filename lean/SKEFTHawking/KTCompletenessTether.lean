/-
# Phase 5q.H W-D (Lane H-1) — the algebra–geometry TETHER: `IsotropicFramedAttachingDatum`,
`IsotropicSurgeryOutput`, and the source-faithful completeness summit

⛔ HARD SCOPE: this module FIXES THE INTERFACE (it constructs no geometry). It is the Lane H-1
interface freeze mandated by the 2026-07-20 vetted route dossier (`H_GEOMETRIC_LEG_DESIGN.md`,
"Lane H-1 — SUPERSEDED BY THE VETTED CODEX DOSSIER", items 2–4 of the binding route
recommendation): make the algebra–geometry tether EXPLICIT before Lane H-2 binds.

## The looseness being fixed

`IsotropicSurgeryTrace` (`KTCompletenessProvider.lean:268`) deliberately DROPS the isotropic class
`x` — its assembly (`IsotropicSurgeryTrace.toAmbientSurgeryDatum`) re-extracts an arbitrary
algebraic `x` via choice and pairs it with the geometric trace. That is formally sound for
CONSUMPTION (the summit only needs existence), but it leaves nothing in the types connecting the
`x` the algebra selects to the circle the geometry surgers. Lane H-2 (the membrane/weld packaging)
must be parameterized by a datum that CARRIES the tie, or its construction can drift.

This module supplies the tethered vocabulary, grounded entirely in in-tree types:

* `IsotropicFramedAttachingDatum prov p x` — the attaching-circle datum on the CARRIER's own
  characteristic surface `Σ = p.2.surf`: an embedded circle (`Circle1`, the in-tree `S¹`), its
  carried nonzero `H₁(S¹;ℤ/2)` class, **the tether `realizes_x`** (the pushed-forward class has
  coordinates EXACTLY `x` under the carrier's own basis tie, via the banked perfect-pairing
  coordinates `homologyCoords`), the framed annular tubular datum (embeddedness-as-data, the E1
  idiom — the carrier's grade is `k = 0`, so continuous + injective IS the honest level; the
  smooth strengthening arrives with the `k ≥ 1` capstone lift), and the `Ω₁^{Spin} ≅ ℤ/2` framing
  bit with its detection tie (the `CharSurfaceTrace.SpinClassDetectsQ` vocabulary, carrier-side).
* `IsotropicSurgeryOutput prov p x` — the H-2 OUTPUT interface: the attaching datum plus the
  algebraic `SurgeryReduction` at the SAME `x`, the geometric `IsotropicSurgeryTrace`, and the
  **exact quadratic identification** `q_ident` (the surgered representative's enhancement IS the
  reduction, through a linear equivalence) — strictly stronger than recording equal rank and
  Brown invariant (dossier §3.2).
* `BrownZeroHasIsotropicFramedAttachment` — **the minimal source-faithful H-1 summit** (dossier
  §4): per brown-0 non-spin REPRESENTATIVE, ∃ one tethered attaching datum. Per-representative,
  NOT per-isotropic-vector — the rank induction needs one suitable `x` each, and the per-class
  strengthening is deliberately NOT adopted (dossier: only if the mathematics genuinely proves it).
* `IsotropicSurgeryOutputSupply` → `KernelReducesToSpin` — the consumer wiring: the STRONGER
  tethered supply discharges the summit through the EXISTING untethered consumers, with the
  `AmbientSurgeryDatum`'s `x` being THE tethered one (`toAmbientSurgeryDatum` — the fix in code:
  no independent re-selection).

## What is deliberately NOT here

* No same-`M` compression-disk interface: the vetted dossier corrected the source attribution —
  KT §5's circle-surgery mechanism produces a bordism to a possibly-DIFFERENT end; no same-`M`
  embedded disk is produced or needed. (`CompressionDiskDatum` is adopted ONLY if a separate
  theorem with π₁/disk-embedding hypotheses is identified — dossier recommendation 5.)
* No transvection/normalization route (dossier recommendation 6 — DEAD as scoped).
* No geometric construction: inhabiting the summit is Lane H-1's genuine remaining geometric
  stack (embedded-circle realization · band-sum closure · framed tubular data · the Taylor
  detection discharge, statement-frozen at `CharSurfaceTrace.lean`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KTCompletenessProvider
import SKEFTHawking.SingularKroneckerBasisBridge
import SKEFTHawking.CharSurfaceTrace

open scoped Manifold
open Topology
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTSurgeryTrace
open SKEFTHawking.KTCompletenessProvider
open SKEFTHawking.SingularHomologyMod2 (Homology)
open SKEFTHawking.SingularCohomologyMod2 (Cohomology)
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.CharSurface (Circle1)

namespace SKEFTHawking.KTCompletenessTether

variable {k : WithTop ℕ∞}

/-! ## §1. The tethered attaching datum -/

/-- **The tethered framed attaching-circle datum at `(p, x)`** (Lane H-1 interface, dossier §3.2).
An embedded circle in the carrier's OWN characteristic surface `Σ = p.2.surf` realizing the
isotropic class `x`, with framing data:

* `f` / `inj` — the embedded circle (continuous + injective; the carrier's grade is `k = 0`, so
  this IS the honest smoothness level — the E1 embeddedness-as-data idiom);
* `fund` / `hfund` — the carried `H₁(S¹;ℤ/2)` class, NONZERO (the dossier's `fund_generator`
  demand at the honest in-tree level: `H₁(S¹;ℤ/2)` has no in-tree rank computation yet, and once
  it lands nonzero IS generator);
* `realizes_x` — **THE TETHER** (dossier: "the indispensable algebra–geometry tether"): under the
  carrier's own basis tie (`p.2.basis`, the `(n,q,surf)` tie of `CharPairStrBundled`), the
  pushed-forward circle class has coordinates EXACTLY `x` — via `homologyCoords` (the
  perfect-pairing coordinates: `xᵢ = ⟨basis⁻¹(δᵢ), f₊ fund⟩`). This is what
  `AmbientSurgeryDatum`/`IsotropicSurgeryTrace` cannot express: the algebra's `x` IS the
  geometry's circle class;
* `tub` / `tubInj` / `tubCore` — the framed annular tubular datum: an embedded annulus
  `S¹ × [-1,1] ↪ Σ` whose core circle is `f` (the trivial-normal-bundle framing carried as data —
  the actual attaching region the KT 2-handle consumes);
* `spinClass` / `hdetect` — the `Ω₁^{Spin} ≅ ℤ/2` class of the framing-induced spin structure,
  as data, TIED to the enhancement by the detection identity `embed2 spinClass = q(x)` (the
  carrier-side shadow of `CharSurfaceTrace.FramedCircle.SpinClassDetectsQ`; the geometric content
  — that `spinClass` is genuinely the induced framing's class — is exactly the Taylor-detection
  statement freeze recorded there, honestly NOT restated here). At an isotropic `x` the detection
  forces the bounding framing (`spinClass_eq_zero_of_isotropic`) — KT §5's "the framing is the
  bounding one, so the handle attaches". -/
structure IsotropicFramedAttachingDatum (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) (x : Fin p.2.n → ZMod 2) where
  /-- the embedded circle in the carrier's characteristic surface `Σ = p.2.surf`. -/
  f : C(↑Circle1, p.2.surf.M)
  /-- embeddedness as data: the circle map is injective. -/
  inj : Function.Injective f
  /-- the carried circle homology class. -/
  fund : Homology Circle1 1
  /-- the carried class is nonzero (generator-at-the-honest-level; see structure docstring). -/
  hfund : fund ≠ 0
  /-- **THE TETHER**: under the carrier's basis tie, the pushed-forward circle class has
  coordinates exactly `x`. -/
  realizes_x :
    homologyCoords p.2.basis
      (Homology.map (X := Circle1) (Y := TopCat.of p.2.surf.M) f 1 fund) = x
  /-- the framed annular tubular datum: an annulus around the circle in `Σ`. -/
  tub : C(↑Circle1 × ↥(Set.Icc (-1 : ℝ) 1), p.2.surf.M)
  /-- the annulus is embedded (as data). -/
  tubInj : Function.Injective tub
  /-- the annulus's core circle IS `f`. -/
  tubCore : ∀ z : ↑Circle1, tub (z, ⟨0, by norm_num⟩) = f z
  /-- the `Ω₁^{Spin} ≅ ℤ/2` class of the framing-induced spin structure on the circle (data;
  `0` = bounds, `1` = the Lie framing). -/
  spinClass : ZMod 2
  /-- the detection tie: the spin bit computes the enhancement value at `x`
  (`CharSurfaceTrace.SpinClassDetectsQ`, carrier-side). -/
  hdetect : embed2 spinClass = p.2.q.q x

namespace IsotropicFramedAttachingDatum

variable {prov : CharPairWProviderPerOp (𝓡 4) k}
variable {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
variable {x : Fin p.2.n → ZMod 2}

/-- **At an isotropic class the framing bounds**: `q x = 0` forces `spinClass = 0` through the
detection tie — KT §5's attachment condition (the framed circle's induced spin structure is the
bounding one, so the 2-handle's disk bundle attaches). -/
theorem spinClass_eq_zero_of_isotropic (d : IsotropicFramedAttachingDatum prov p x)
    (hxq : p.2.q.q x = 0) : d.spinClass = 0 := by
  have h : embed2 d.spinClass = 0 := by rw [d.hdetect, hxq]
  exact (SKEFTHawking.CharSurface.embed2_eq_zero_iff d.spinClass).mp h

/-- **The tether forces homological nontriviality of the circle in `Σ`**: for `x ≠ 0` the
pushed-forward class cannot vanish (its `homologyCoords` are `x`) — the "homologically
nontrivial embedded circle" hypothesis of the Taylor Lemma-1.2 descent
(`CharSurface.PinCharSurface.TaylorSurgeryDescends`), derived rather than assumed. -/
theorem pushforward_ne_zero (d : IsotropicFramedAttachingDatum prov p x) (hx0 : x ≠ 0) :
    Homology.map (X := Circle1) (Y := TopCat.of p.2.surf.M) d.f 1 d.fund ≠ 0 := by
  intro h0
  apply hx0
  rw [← d.realizes_x, h0, map_zero]

end IsotropicFramedAttachingDatum

/-! ## §2. The H-2 output interface — the exact quadratic identification -/

/-- **The tethered surgery OUTPUT at `(p, x)`** (the interface Lane H-2 must produce; dossier
§3.2's `IsotropicSurgeryOutput`). Extends the attaching datum with:

* `reduction` — the algebraic `SurgeryReduction` at the SAME `x` (not an independently chosen
  class);
* `trace` — the geometric residual (`IsotropicSurgeryTrace`: the surgered `p'`, the exact rank
  drop, the trace bordism, the Pin⁺ tether);
* `ident` / `q_ident` — **the exact quadratic identification**: the surgered representative's
  enhancement IS the algebraic reduction, through a linear equivalence intertwining the `q`s.
  Strictly stronger and more meaningful than recording equal rank and equal Brown invariant
  (dossier: `q_identification`); `ident_rank_eq` shows it RE-DERIVES the trace's `hrank`
  independently — the anti-drift cross-check. -/
structure IsotropicSurgeryOutput (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) (x : Fin p.2.n → ZMod 2)
    extends IsotropicFramedAttachingDatum prov p x where
  /-- the algebraic surgery reduction at the SAME class `x`. -/
  reduction : p.2.q.SurgeryReduction x
  /-- the geometric residual: surgered representative, rank drop, trace bordism, Pin⁺ tether. -/
  trace : IsotropicSurgeryTrace prov p
  /-- the space identification between the surgered representative's enhancement space and the
  reduction's. -/
  ident : (Fin trace.p'.2.n → ZMod 2) ≃ₗ[ZMod 2] (reduction.κ → ZMod 2)
  /-- **the exact quadratic identification**: the surgered enhancement IS the reduction. -/
  q_ident : ∀ u, trace.p'.2.q.q u = reduction.R.q (ident u)

namespace IsotropicSurgeryOutput

variable {prov : CharPairWProviderPerOp (𝓡 4) k}
variable {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
variable {x : Fin p.2.n → ZMod 2}

/-- The identification pins the surgered rank to the reduction's index cardinality
(`2^n' = 2^|κ|` forces `n' = |κ|`). -/
theorem ident_card_eq (o : IsotropicSurgeryOutput prov p x) :
    o.trace.p'.2.n = Fintype.card o.reduction.κ := by
  have h := Fintype.card_congr o.ident.toEquiv
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
  exact Nat.pow_right_injective (le_refl 2) h

/-- **The anti-drift cross-check**: the exact identification RE-DERIVES the trace's rank drop
`n' + 2 = n` independently (via `card_surgeryReduction`), so the trace's `hrank` and the
identification can never disagree. -/
theorem ident_rank_eq (o : IsotropicSurgeryOutput prov p x) (hxq : p.2.q.q x = 0) :
    o.trace.p'.2.n + 2 = p.2.n := by
  have hcard := p.2.q.card_surgeryReduction o.reduction hxq
  rw [Fintype.card_fin] at hcard
  rw [ident_card_eq o]
  omega

/-- The surgered enhancement's values transport all the way into the ORIGINAL enhancement on the
pair complement — composing the identification with the reduction's `agree`. -/
theorem q_transport (o : IsotropicSurgeryOutput prov p x) (u : Fin o.trace.p'.2.n → ZMod 2) :
    o.trace.p'.2.q.q u = p.2.q.q (o.reduction.e (o.ident u)) := by
  rw [o.q_ident u, o.reduction.agree]

/-- **The looseness fix in code**: the stronger tethered output yields the legacy
`AmbientSurgeryDatum` with `x` being THE tethered class — no independent re-selection (contrast
`IsotropicSurgeryTrace.toAmbientSurgeryDatum`, which re-extracts an arbitrary `x` by choice). -/
def toAmbientSurgeryDatum (o : IsotropicSurgeryOutput prov p x) (hx0 : x ≠ 0)
    (hxq : p.2.q.q x = 0) : AmbientSurgeryDatum prov p :=
  { x := x, hx0 := hx0, hxq := hxq, p' := o.trace.p', hrank := o.trace.hrank,
    b := o.trace.b, hT2 := o.trace.hT2, hBor := o.trace.hBor }

end IsotropicSurgeryOutput

/-! ## §3. The source-faithful summit statements -/

/-- **THE H-1 SUMMIT (minimal source-faithful; dossier §4)**: every non-spin brown-0
representative admits SOME nonzero isotropic class realized by a tethered framed attaching
datum. Per-REPRESENTATIVE existential (the rank induction needs one suitable `x` each); the
per-class ∀-strengthening is deliberately NOT adopted. Inhabiting this is Lane H-1's genuine
geometric stack (embedded-circle realization · band-sum closure · framed tubular data · the
Taylor detection discharge). -/
def BrownZeroHasIsotropicFramedAttachment (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
    charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
    0 < p.2.n →
    ∃ x : Fin p.2.n → ZMod 2, x ≠ 0 ∧ p.2.q.q x = 0 ∧
      Nonempty (IsotropicFramedAttachingDatum prov p x)

/-- **The full tethered supply (H-1 + H-2 combined)**: every non-spin brown-0 representative
admits a tethered surgery OUTPUT — attaching datum, algebraic reduction, geometric trace, and the
exact quadratic identification, all at ONE shared `x`. Lane H-2's job is exactly
`IsotropicFramedAttachingDatum → IsotropicSurgeryOutput` (the membrane/weld packaging), which
upgrades `BrownZeroHasIsotropicFramedAttachment` to this. -/
def IsotropicSurgeryOutputSupply (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
    charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
    0 < p.2.n →
    ∃ x : Fin p.2.n → ZMod 2, x ≠ 0 ∧ p.2.q.q x = 0 ∧
      Nonempty (IsotropicSurgeryOutput prov p x)

/-! ## §4. The consumer wiring — the tethered supply discharges the summit -/

variable {prov : CharPairWProviderPerOp (𝓡 4) k}

/-- **The tethered supply discharges the KT §5 completeness summit** — through the EXISTING
untethered consumer (`kernelReducesToSpin_of_ambientDatumSupply`), with each
`AmbientSurgeryDatum`'s `x` being THE tethered class of the output (via
`IsotropicSurgeryOutput.toAmbientSurgeryDatum`). Nothing is lost by strengthening the interface:
the stronger supply is exactly as consumable. -/
theorem kernelReducesToSpin_of_isotropicSurgeryOutputSupply
    (H : IsotropicSurgeryOutputSupply prov) : KernelReducesToSpin prov :=
  kernelReducesToSpin_of_ambientDatumSupply fun p hbrown hpos =>
    ((H p hbrown hpos).choose_spec.2.2.some).toAmbientSurgeryDatum
      (H p hbrown hpos).choose_spec.1 (H p hbrown hpos).choose_spec.2.1

/-- The shallow-binder form: the tethered supply discharges `KTSurgeryReduces` the same way. -/
theorem ktSurgeryReduces_of_isotropicSurgeryOutputSupply
    (H : IsotropicSurgeryOutputSupply prov) : KTSurgeryReduces prov :=
  ktSurgeryReduces_of_ambientDatumSupply fun p hbrown hpos =>
    ((H p hbrown hpos).choose_spec.2.2.some).toAmbientSurgeryDatum
      (H p hbrown hpos).choose_spec.1 (H p hbrown hpos).choose_spec.2.1

/-- The tethered output supply also reconstitutes the WEAKER per-representative trace supply
(dropping the tether) — the exact hypothesis of
`kernelReducesToSpin_of_isotropicSurgeryTraceSupply`. Documents the strict interface ordering:
`OutputSupply ⟹ trace supply ⟹ AmbientSurgeryDatum supply`. -/
noncomputable def isotropicSurgeryTraceSupply_of_outputSupply
    (H : IsotropicSurgeryOutputSupply prov) :
    ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → IsotropicSurgeryTrace prov p :=
  fun p hbrown hpos => ((H p hbrown hpos).choose_spec.2.2.some).trace

end SKEFTHawking.KTCompletenessTether
