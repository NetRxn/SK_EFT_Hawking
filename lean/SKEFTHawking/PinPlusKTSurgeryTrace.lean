/-
# Phase 5q.H W-D — THE SURGERY-TRACE CONSTRUCTION WAVE (the `KTSurgeryReduces` opener)

⛔ HARD SCOPE (round-9 FROZEN SPEC, `PinPlusKTStepGate` — BINDING): this module DISCHARGES NOTHING
of the round-8 TRIPLE `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}`. Per the G9-1 equivalence
`KTSurgeryReduces ⟺ KernelReducesToSpin`, everything here is consumed AND audited AS
`KernelReducesToSpin`, under the round-8 triple discipline verbatim. This wave REDUCES the single
gated geometric surgery step `KTSurgeryReduces` to its SHARPEST named geometric leaf — the ambient
KT §5 surgery datum `AmbientSurgeryDatum` — and banks the honest machinery (the Fin-reindexed
surgery-reduction algebra, the tie transports, the conditional assembly). Provider-inhabitation
rider (G8-1): every per-`prov` statement is CONDITIONAL (the provider has zero in-tree inhabitants
until Track-2's `cylData`/`addClosure` residuals land), not vacuous.

## The geometric content (KT-LMS-151 §5 p.217, Thm 5.1/5.2; `KT_LMS_Section5_completeness_proof_extracted.md`)
`KTSurgeryReduces prov` (`PinPlusKTKernelSpinRoute` §2) demands, for every non-spin (`0 < n`)
brown-0 representative `p`, a strictly rank-dropping `p'` with `[p'] = [p]` — ONE rank-lowering
tethered surgery step. KT §5: an isotropic class `x ∈ H₁(Σ;ℤ/2)` with `q(x) = 0` (the enhancement's
`q x = 0` is EXACTLY the framing-obstruction-vanishing / ambient-surgery-compatibility condition) is
represented by an embedded circle; surgering `Σ` along it (AMBIENT — inside the 4-manifold) lowers
the genus/rank by 2 and preserves the char-pair structure class. The BORDISM WITNESS is the trace of
the surgery — `W = M × I` with the membrane `Q =` the surgery trace of `Σ`
(`Σ × [0,½] ∪ 2-handle ∪ Σ' × [½,1]`) tethered into `M × I`, a `CharPairBorRealizedTethered`.

## What this wave banks
* **§1 — the algebra-to-geometry seam (enhancement side, BANKED unconditional algebra).**
  `exists_finReduction`: an isotropic class `x` (`q x = 0`, `x ≠ 0`) of a `Z4Quadratic (Fin n)`
  surgers to a `Z4Quadratic (Fin m)` with `m + 2 = n` (rank drops by EXACTLY 2 — `card_surgeryReduction`)
  and SAME Brown invariant (`brown_surgeryReduction` + `reindex_brown`). This is the four-field
  tie's enhancement leg on `Σ'`, reindexed to a concrete `Fin` rank.
* **§2 — `AmbientSurgeryDatum`, THE SHARPEST NAMED GEOMETRIC HYPOTHESIS.** The ambient KT §5 surgery
  step on `p`, parameterized (the embedded disk / framing / tubular data is geometric INPUT — named,
  not proven from scratch): the isotropic surgery class `x` (`q x = 0`), the surgered representative
  `p'` with the exact `n' + 2 = n` rank drop, and the surgery-trace bordism `b` carrying a GENUINE
  tether `CharPairBorRealizedTethered b p'.2 p.2`. Its extraction lemmas (off-fibre positivity, the
  class-equality tie, brown-preservation, algebra-match) are banked.
* **§3 — the conditional assembly.** `ktSurgeryReduces_of_ambientDatumSupply` (a universal
  ambient-datum supply ⟹ `KTSurgeryReduces`) and its headline
  `kernelReducesToSpin_of_ambientDatumSupply` (⟹ the deep `KernelReducesToSpin` binder, G9-1).

## Round-9 FROZEN-SPEC compliance (item 1 — the excluded degenerate model)
The construction produces a GENUINE tether OFF the `[p] = 0` fibre, NOT the empty-structure fake:
`AmbientSurgeryDatum prov p` FORCES `0 < p.2.n` (`ambientSurgeryDatum_pos_rank`; the nonzero
isotropic class `x : Fin p.2.n → ZMod 2` cannot live at rank 0), so no datum exists for a rank-0
(spin, `[p] = 0`-fibre) representative, and the `hBor` field demands an ACTUAL surgery-trace bordism
`b` from `p'.1` to `p.1` with a tethered membrane — which the empty structure (bordant only to `0`)
cannot supply for a general nonzero `[p]`. The terminal hypothesis is the sharpest geometric
statement: the AMBIENT surgery datum's existence for every non-spin brown-0 class (its discharge =
embedded-surgery-disk existence, gated next round).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTKernelSpinRoute
import SKEFTHawking.PinPlusKTKernelSector

open scoped Manifold
open Topology
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.RP4CharPairWitness
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute

namespace SKEFTHawking.PinPlusKTSurgeryTrace

variable {k : WithTop ℕ∞}

/-! ## §1. The algebra-to-geometry seam — the surgered enhancement, reindexed to a concrete `Fin`.

Unconditional algebra (no `prov`, no carrier, no vacuity concern). The KT §5 surgery on the
characteristic surface `Σ` along an isotropic circle `x` (`q x = 0`) descends to the enhancement as
a `SurgeryReduction`; `card_surgeryReduction` pins the rank drop to EXACTLY 2 and `brown_surgeryReduction`
+ `reindex_brown` pin the Brown invariant unchanged. `exists_finReduction` packages this as a
concrete `Z4Quadratic (Fin m)` with `m + 2 = n` — the enhancement leg of the four-field tie on `Σ'`,
the abstract prediction the geometric `AmbientSurgeryDatum` (§2) must (and does — `ambientDatum_matches_algebra`)
realize. -/

/-- **The Fin-reindexed surgery reduction of an isotropic enhancement class.** For a
`Z4Quadratic (Fin n)` and a nonzero isotropic `x` (`q x = 0`), the KT surgery move yields a reduced
enhancement on `Fin m` with `m + 2 = n` (rank drops by exactly 2) and the SAME Brown invariant.
BANKED unconditional algebra: the enhancement leg of the surgered surface's tie. Composes
`exists_surgeryReduction` (the abstract reduction), `card_surgeryReduction` (rank − 2),
`brown_surgeryReduction` (brown fixed) and `reindex_brown` (transport to `Fin`). -/
theorem exists_finReduction {n : ℕ} (Q : Z4Quadratic (Fin n)) {x : Fin n → ZMod 2}
    (hxq : Q.q x = 0) (hx0 : x ≠ 0) :
    ∃ (m : ℕ) (R : Z4Quadratic (Fin m)), m + 2 = n ∧ R.brown = Q.brown := by
  obtain ⟨S⟩ := Q.exists_surgeryReduction hxq hx0
  have hcard : n = Fintype.card S.κ + 2 := by
    have h := Q.card_surgeryReduction S hxq
    rwa [Fintype.card_fin] at h
  refine ⟨Fintype.card S.κ, S.R.reindex (Fintype.equivFin S.κ), by omega, ?_⟩
  rw [reindex_brown]
  exact (Q.brown_surgeryReduction S hxq).symm

/-! ## §2. `AmbientSurgeryDatum` — the sharpest named geometric hypothesis. -/

/-- **THE AMBIENT KT §5 SURGERY DATUM at `p`** (the terminal named hypothesis of this wave). Bundles
ONE ambient rank-lowering tethered surgery step on the non-spin brown-0 representative `p`:

* `x` / `hx0` / `hxq` — the mod-2 `H₁`-class of the embedded surgery circle in `Σ`, nonzero, with
  `q x = 0` (the enhancement's isotropy is EXACTLY the framing-obstruction-vanishing /
  ambient-surgery-compatibility condition, KT §5 / Thm 5.1). The nonzero class FORCES `0 < p.2.n`
  (`ambientSurgeryDatum_pos_rank`) — the datum lives OFF the rank-0 spin (`[p] = 0`) fibre.
* `p'` / `hrank` — the surgered representative, with the KT rank drop by EXACTLY 2 (`n' + 2 = n`);
  its algebraic invariants MATCH `exists_finReduction`'s prediction (`ambientDatum_matches_algebra`).
* `b` / `hT2` / `hBor` — the surgery-trace bordism `W` (= `M × I` with the trace membrane
  `Σ × [0,½] ∪ 2-handle ∪ Σ' × [½,1]`) carrying a GENUINE tether `CharPairBorRealizedTethered b p'.2 p.2`
  — the honest `Q`/`ιW`/pin membrane, NOT the empty-structure fake (round-9 spec item 1).

The disk / framing / tubular data underlying the ambient surgery is GEOMETRIC INPUT — named here (as
the existence of this datum), not proven from scratch; its discharge is embedded-surgery-disk
existence, gated next round. -/
structure AmbientSurgeryDatum (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) where
  /-- the mod-2 `H₁`-class of the embedded surgery circle in `Σ`. -/
  x : Fin p.2.n → ZMod 2
  /-- the class is nonzero (a genuine circle to surger). -/
  hx0 : x ≠ 0
  /-- `q x = 0` — the framing obstruction vanishes (ambient-surgery-compatibility, KT §5). -/
  hxq : p.2.q.q x = 0
  /-- the surgered representative (KT §5 genus/rank-drop-by-2 output). -/
  p' : StrMfd (pinPlusCharPairData prov).toTangentialData
  /-- the KT surgery drops the enhancement rank by EXACTLY 2. -/
  hrank : p'.2.n + 2 = p.2.n
  /-- the surgery-trace bordism `W` from `p'` to `p`. -/
  b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1
  /-- its carrier is Hausdorff. -/
  hT2 : T2Space b.W
  /-- **THE GENUINE TETHER**: the surgery-trace membrane realizes `[p'] = [p]` as a Pin⁺ bordism. -/
  hBor : Nonempty (CharPairBorRealizedTethered b p'.2 p.2)

variable {prov : CharPairWProviderPerOp (𝓡 4) k}
variable {p : StrMfd (pinPlusCharPairData prov).toTangentialData}

/-- **The datum lives OFF the rank-0 spin fibre** (round-9 spec item 1, the genuineness guarantee):
a nonzero isotropic class `x : Fin p.2.n → ZMod 2` cannot exist at rank 0, so `0 < p.2.n`. Hence no
`AmbientSurgeryDatum` exists for a spin (rank-0, `[p] = 0`-fibre) representative — the empty-structure
fake is structurally excluded. -/
theorem ambientSurgeryDatum_pos_rank (d : AmbientSurgeryDatum prov p) : 0 < p.2.n := by
  rcases Nat.eq_zero_or_pos p.2.n with h0 | h
  · haveI : IsEmpty (Fin p.2.n) := by rw [h0]; infer_instance
    exact absurd (Subsingleton.elim d.x 0) d.hx0
  · exact h

/-- The surgered representative strictly drops rank (from the exact `n' + 2 = n`). -/
theorem ambientSurgeryDatum_lt (d : AmbientSurgeryDatum prov p) : d.p'.2.n < p.2.n := by
  have := d.hrank; omega

/-- **The tether ties the classes**: `[p'] = [p]` (a thin specialization of `mk_eq_of_tethered` to
the datum's surgery-trace membrane). The rank drop plus this class-equality is one `KTSurgeryReduces`
step at `p`. -/
theorem ambientSurgeryDatum_mk_eq (d : AmbientSurgeryDatum prov p) :
    T2DataBordismGrp.mk (pinPlusCharPairData prov) d.p'
      = T2DataBordismGrp.mk (pinPlusCharPairData prov) p :=
  mk_eq_of_tethered prov d.b d.hT2 d.hBor

/-- **The surgery preserves the Brown invariant** — `brown(q') = brown(q)`, forced by the tether's
class-equality (`charPairBrown` reads the enhancement's `brown` on any representative). This is the
geometric shadow of `brown_surgeryReduction`; together with `hrank` it is the algebra-match. -/
theorem ambientSurgeryDatum_brown_preserved (d : AmbientSurgeryDatum prov p) :
    d.p'.2.q.brown = p.2.q.brown := by
  have h := congrArg (charPairBrown prov) (ambientSurgeryDatum_mk_eq d)
  rwa [charPairBrown_mk, charPairBrown_mk] at h

/-- **The geometric datum MATCHES the algebraic surgery reduction** (the algebra-to-geometry seam,
closed): the surgered representative's rank and Brown invariant are EXACTLY those `exists_finReduction`
(§1) predicts from the isotropic class `x` — rank `n − 2` and the same `brown`. The geometry realizes
the algebra; neither leg is free. -/
theorem ambientDatum_matches_algebra (d : AmbientSurgeryDatum prov p) :
    d.p'.2.n + 2 = p.2.n ∧ d.p'.2.q.brown = p.2.q.brown :=
  ⟨d.hrank, ambientSurgeryDatum_brown_preserved d⟩

/-! ## §3. The conditional assembly — the ambient-datum supply discharges the binder. -/

/-- **One ambient surgery step supplies the `KTSurgeryReduces` conclusion at `p`** (CONDITIONAL;
discharges nothing of the triple). The datum's rank drop + genuine tether meet the existential
`KTSurgeryReduces` demands via the banked `surgeryStep_of_tethered`. The open content is CONSTRUCTING
the datum (the ambient surgery), not this packaging. -/
theorem ktSurgeryStep_of_ambientDatum (d : AmbientSurgeryDatum prov p) :
    ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
      p'.2.n < p.2.n ∧
        T2DataBordismGrp.mk (pinPlusCharPairData prov) p'
          = T2DataBordismGrp.mk (pinPlusCharPairData prov) p :=
  surgeryStep_of_tethered prov (ambientSurgeryDatum_lt d) d.b d.hT2 d.hBor

/-- **THE WAVE HEADLINE — `KTSurgeryReduces ⟸ (∀ non-spin brown-0 class, `AmbientSurgeryDatum`)**
(CONDITIONAL; discharges nothing of the triple). A universal supply of the ambient surgery datum —
one per non-spin brown-0 representative — discharges the single gated geometric surgery step
`KTSurgeryReduces`. This is the load-bearing reduction of gap (1): the KT §5 kernel-null content is
EXACTLY the existence of the ambient surgery datum, and nothing more. The residual `∀`-hypothesis is
the sharpest possible geometric statement (embedded-surgery-disk existence), gated next round. -/
theorem ktSurgeryReduces_of_ambientDatumSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → AmbientSurgeryDatum prov p) :
    KTSurgeryReduces prov := by
  intro p hbrown hpos
  exact ktSurgeryStep_of_ambientDatum (H p hbrown hpos)

/-- **The deep-binder form — `KernelReducesToSpin ⟸ (ambient-datum supply)`** (CONDITIONAL;
discharges nothing of the triple). Composes the wave headline with the G9-1 equivalence
`KTSurgeryReduces ⟹ KernelReducesToSpin` (`kernelReducesToSpin_of_surgeryReduces`): the ambient
surgery datum supply discharges the DEEP KT §5 kernel-null binder `KernelReducesToSpin` — the whole
`∀ x ∈ ker` direction reduced to embedded-surgery-disk existence. Consumed AS `KernelReducesToSpin`
inside the round-8 triple, per the frozen spec. -/
theorem kernelReducesToSpin_of_ambientDatumSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → AmbientSurgeryDatum prov p) :
    KernelReducesToSpin prov :=
  kernelReducesToSpin_of_surgeryReduces prov (ktSurgeryReduces_of_ambientDatumSupply H)

/-! ## §4. The surgery-trace membrane — the banked trace topology + the L-kernel brown route.

Concrete-witness facts about the surgery-trace membrane carried by a tethered bordism, banked at the
`CharPairBorRealizedTethered` level (generic over the ends). These document what the datum's `hBor`
genuinely carries: a dim-3 charted membrane (`Σ × [0,½] ∪ handle ∪ Σ' × [½,1]`) closed-embedded in
`W`, whose boundary-to-interior `H₁`-kernel `L` (Taylor-vanishing + jointly Lagrangian) FORCES the
Brown-invariant equality of the ends via the anti-collapse engine — the KT surgery's
`brown`-preservation read off the membrane kernel directly, INDEPENDENT of `Quot.sound`. -/

section TraceTopology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
variable {s t : SingularManifold.{0} PUnit.{1} k I}
variable {b : Bordism (I.prod (𝓡∂ 1)) s t}
variable {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}

/-- **The surgery-trace membrane is a dim-3 charted object** — `Q` charts over `MembraneModel`
(`EuclideanSpace ℝ (Fin 2)` = the characteristic surface ⊕ `EuclideanHalfSpace 1` = the collar),
pinning `dim Q = 3` (surface × collar + the 2-handle), ruling out CW pathologies. The trace topology
the datum's `hBor` genuinely carries. -/
theorem surgeryTrace_membrane_charted (β : CharPairBorRealizedTethered b σ τ) :
    Nonempty (ChartedSpace MembraneModel β.real.Q) :=
  ⟨β.chartQ⟩

/-- **The surgery-trace membrane closed-embeds into the bordism carrier** `W` — `Q ⊆ W` faithfully
(the tether `ιW`). The membrane sits genuinely inside `W = M × I`, its boundary anchored to `∂W`
(the glue). -/
theorem surgeryTrace_membrane_closedEmbeds (β : CharPairBorRealizedTethered b σ τ) :
    IsClosedEmbedding β.ιW :=
  β.membrane_closedEmbeds_in_W

/-- **The membrane's `H₁`-kernel forces Brown-preservation** (the KT surgery's `brown` invariance,
read off the membrane kernel `L`). The Taylor-leg-vanishing + jointly-Lagrangian kernel of the
surgery-trace membrane forces `brown(q_σ) = brown(q_τ)` via the anti-collapse engine
(`CharPairBorRealized.brown_eq`) — the "kernel computation" leg of the seam, INDEPENDENT of the
class-equality (`Quot.sound`) route of `ambientSurgeryDatum_brown_preserved`. -/
theorem surgeryTrace_brown_eq_of_L (β : CharPairBorRealizedTethered b σ τ) :
    σ.q.brown = τ.q.brown :=
  β.toRealized.brown_eq

end TraceTopology

/-- **The datum's tether forces Brown-preservation through the membrane kernel** (the L-kernel route,
datum level): extracting the surgery-trace witness from `hBor`, the membrane's Taylor/Lagrangian
kernel forces `brown(q') = brown(q)` — independently of the class-equality route
(`ambientSurgeryDatum_brown_preserved`). Both routes agree: the geometry (membrane kernel) and the
class (`[p'] = [p]`) deliver the same `brown`-preservation, the anti-collapse consistency of the
surgery step. -/
theorem ambientSurgeryDatum_brown_preserved_via_L (d : AmbientSurgeryDatum prov p) :
    d.p'.2.q.brown = p.2.q.brown :=
  d.hBor.elim fun β => surgeryTrace_brown_eq_of_L β

end SKEFTHawking.PinPlusKTSurgeryTrace
