/-
# Phase 5q.H close-out (#179) — THE ROUND-9 SPHERE-OVERHANG RE-TRIAGE: the concrete surgery atom.

**Re-triage of the round-9 gate `SectorIsGeometric` (`PinPlusKTStepGate` §4, G9-5) against the
matured tree.** The gate froze `SectorIsGeometric prov` — *every broad-sector class
(`EmptySigmaRepresentable`, rank `n = 0`, `H¹(Σ) = 0`) admits a LITERALLY-empty-Σ representative
(`GeometricSpinRepresentable`)* — as an interface, NOT discharged, on the grounds that "killing a
nonempty trivial-`H¹` characteristic sphere is one more genuine surgery — no tether exists". The
re-triage CONFIRMS the freeze and NAMES the residual concretely.

## Verdict (kernel-checked): the freeze STANDS; the residual is the terminal-KRS bounding datum.

* **Not a dead fork.** No no-go refutes `SectorIsGeometric` (it is TRUE geometrically — a
  characteristic union-of-spheres bounds — and is the frozen replacement B-target absorbed by the
  C-leaf, `KernelNoGos` fork #17 `enriques-datum-refuted-as-shaped`). So the honest options are
  discharge / reduce, never a refutation.
* **No in-tree tether collapses a single characteristic sphere.** Every tethered op on
  representatives either PRESERVES the surface (`revStr`, `cylBor`) or RAISES rank (`sumStr`/`addBor`
  add `n`); the only "→ empty" op is `charPairNegBorTied` (the doubling `revStr σ ⊔ σ ~ ∅`), which at
  rank 0 (`revStr σ = σ`, `revStr_fixed_of_rank_zero`) gives only `σ ⊔ σ ~ ∅` (the 2-torsion
  `spinSector_two_torsion`), NEVER a single `σ ~ (empty-Σ)`. The round-9 analysis holds verbatim.
* **The concrete residual is `emptySourceRealizationTied`'s input.** The empty-source membrane
  realization (`PinPlusCharPairEmptySourceRealization`) realizes exactly the degenerate terminal-KRS
  step "the characteristic surface bounds": given a compact `T2` space `Q` in which the rank-0
  surface `Σ` closed-embeds (`∂Q = ∅ ⊔ Σ`) plus the two single-surface kernel conditions, it builds
  the collapse bordism. That per-structure BOUNDING DATUM — not a free field — is the honest
  geometric residual, the same "one more surgery" the gate named.
* **Recoverable from `KTKernelCard` (already in-tree).** `phiRange_of_KTKernelCard` +
  `spinForgetPhi_range_iff_sectorIsGeometric` give `SectorIsGeometric` from the kernel bound, so dC
  ALREADY fires via `nonempty_ktSpinPresentationDatum_of_row_of_kernelCard` (the G9-4 route). This
  module adds the OTHER honest hypothesis for dC's overhang route.

## What lands GREEN here (the honest reduction — NOT a discharge).

`RankZeroCollapsesToEmptySurf prov` — the concrete, per-structure "membrane-collapse" atom: every
rank-0 structured manifold is ONE-STEP `IsT2DataBordant` to an empty-Σ one. This is STRICTLY the
form the empty-source realization machinery produces (a single tethered `CharPairBorRealizedTethered`
witness), and it is strictly stronger than the class-level `SectorIsGeometric` (whose `mk`-equality
is only the `EqvGen` of one-step bordance). The reduction `sectorIsGeometric_of_…` therefore does NOT
weaken dC's consumer — dC still consumes the full `SectorIsGeometric`; this module supplies a
concrete, machinery-matching sufficient condition + wires dC's overhang leaf through it.

**Non-circularity**: zero `k₀`/`KTNonSplit` facts are consumed; the reduction is a pure
bordism-to-class-equality step (`T2DataBordismGrp.mk_eq_of_bordant`), and the atom is a geometric
input, not a restatement of the conclusion (`SectorIsGeometric → RankZeroCollapsesToEmptySurf` does
NOT hold — the class-level ∃ gives no single-step tether).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinPresentationRow

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTStepGate
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinPresentationRow

namespace SKEFTHawking.PinPlusKTSectorGeometricReduce

variable {k : WithTop ℕ∞}

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The concrete surgery atom -/

/-- **THE CONCRETE SPHERE-OVERHANG ATOM** (the round-9 residual, named) — every rank-0 structured
manifold is ONE-STEP `IsT2DataBordant` to a structure with a LITERALLY-empty characteristic surface.
This is exactly the collapse bordism the empty-source realization machinery
(`emptySourceRealizationTied`, `PinPlusCharPairEmptySourceRealization`) produces from the
per-structure BOUNDING DATUM (`Q` compact `T2` with `Σ` closed-embedded, `∂Q = ∅ ⊔ Σ`, plus the two
single-surface kernel conditions) — the honest geometric input "the characteristic surface bounds",
the "one more surgery" the round-9 gate identified.

Strictly stronger than the class-level `SectorIsGeometric` (one-step bordance vs `mk`-equality =
`EqvGen` of it), so a discharge routed through this atom cannot weaken dC's consumer. -/
def RankZeroCollapsesToEmptySurf : Prop :=
  ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
    IsSpinSectorStr prov p →
      ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
        IsEmpty p'.2.surf.M ∧ IsT2DataBordant (pinPlusCharPairData prov) p p'

/-! ## §2. The reduction -/

/-- **THE HONEST REDUCTION** — `RankZeroCollapsesToEmptySurf ⟹ SectorIsGeometric`. Given a
broad-sector class `x` with rank-0 representative `p`, the atom hands a one-step collapse bordism to
an empty-Σ structure `p'`; `mk_eq_of_bordant` turns it into `mk p' = mk p = x`, which is exactly the
`GeometricSpinRepresentable` witness. Zero `k₀`/`KTNonSplit` facts consumed. -/
theorem sectorIsGeometric_of_rankZeroCollapsesToEmptySurf
    (h : RankZeroCollapsesToEmptySurf prov) : SectorIsGeometric prov := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨p', hemp, hbord⟩ := h p hp
  exact ⟨p', hemp, (T2DataBordismGrp.mk_eq_of_bordant _ hbord).symm⟩

/-- **The class-level shadow of the atom is `SectorIsGeometric` itself** (the honest converse
direction — CLASS level only, not one-step): `SectorIsGeometric` yields, for every rank-0 structure
`p`, an empty-Σ structure `p'` with EQUAL CLASS `mk p' = mk p`. This makes precise that the ONLY
strengthening in the atom over the gate's Prop is the promotion of `mk`-equality to a single-step
tethered bordism — i.e. the atom is the concrete-surgery form, adding no sector restriction. -/
theorem rankZeroClassCollapse_of_sectorIsGeometric (h : SectorIsGeometric prov) :
    ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData, IsSpinSectorStr prov p →
      ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
        IsEmpty p'.2.surf.M ∧
          T2DataBordismGrp.mk (pinPlusCharPairData prov) p'
            = T2DataBordismGrp.mk (pinPlusCharPairData prov) p := by
  intro p hp
  exact h _ ⟨p, hp, rfl⟩

/-! ## §3. dC's overhang leaf, wired through the concrete atom -/

variable {prov}

/-- **dC wiring — `KTSpinPresentationDatum` from the row, on the CONCRETE overhang atom**: Direction
C's leaf from `{row, hA, hB, hΦg, RankZeroCollapsesToEmptySurf}`. The overhang is consumed AS A
HYPOTHESIS in its honest concrete-surgery form (the per-structure collapse bordism), reduced to
`SectorIsGeometric` in place. The row supplies `{R, g, hg, hdvd}`; `hΦg` is the generator image. A
discharge of dC on this route must supply the collapse bordism (the terminal-KRS bounding datum),
NOT re-derive it — no in-tree tether does (round-9 freeze). -/
theorem nonempty_ktSpinPresentationDatum_of_row_of_collapse (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g) = ktKernelRep prov)
    (hcol : RankZeroCollapsesToEmptySurf prov) :
    Nonempty (KTSpinPresentationDatum prov (spinEmptyData prov)) :=
  nonempty_ktSpinPresentationDatum_of_row row hA hB hΦg
    (sectorIsGeometric_of_rankZeroCollapsesToEmptySurf prov hcol)

end SKEFTHawking.PinPlusKTSectorGeometricReduce
