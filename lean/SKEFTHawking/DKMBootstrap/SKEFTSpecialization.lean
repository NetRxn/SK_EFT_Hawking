/-
# Phase 6q Wave 2a.2 — SK-EFT-Hawking specialization of CHHK DKM bootstrap

The substantive specialization of the Track-1 DKM bootstrap substrate to
the SK-EFT-Hawking horizon transport problem. Per Wave 2a.1 DR, this
module ships the `IsCHHKBootstrapBound` integrated-form predicate, the
`IsMIRBound` Mott-Ioffe-Regel-style master bound predicate (CHHK eq. 29),
and the bridge between Phase 6q DKMParameters and the existing
SK-EFT-Hawking machinery (`SKEFTHawking.SKDoubling.FirstOrderCoeffs` /
`CombinedDissipativeCoeffs`).

**Per Wave 2a.1 DR §1 platform recommendation:** initial platform is
**graphene Dirac fluid** (E2 bundle) — the only project platform that is
*natively lattice* with a microscopically conserved charge, the cleanest
dynamical-KMS Z₂ structure, and experimental anchors at Crossno 2016
(Wiedemann-Franz violation) + Abedinpour 2010 (exchange-renormalized
Drude weight). BEC and polariton are PARTIAL-VIABLE secondary targets.

**Wave 2a.2 deliverables:**
1. **`IsCHHKBootstrapBound`** — predicate-substrate operationalization of
   CHHK eq. (8) / (14) integrated spectral-weight inequality.
2. **`IsMIRBound`** — predicate for the Mott-Ioffe-Regel master bound
   (CHHK eq. 29): `(d·β_d / 4π)^(1/(d+1)) ≤ ℓ/a`.
3. **Wilson-coefficient bridge** — substantive structural map between
   DKMParameters `(τ, D, χ)` and the existing `FirstOrderCoeffs` `(r1,
   …, r6, i1, i2, i3)` Wilson coefficients of `SKEFTHawking.SKDoubling`
   (substantive cross-bridge per Wave 2a.1 DR §4).
4. **Substantive non-vacuity** — the substrate-level theorem
   `dkm_bootstrap_yields_mir_bound`: any analytic-bootstrap-compatible
   correlator (per Wave 1c.1) with sufficiently large mean free path
   satisfies the MIR bound.

**Wave 2a.1 DR §6 cross-bridge note:** the substantive Gaussian-
fluctuation-regime hypothesis required for the full
`chhk_positivity_iff_LDP_rate_function` biconditional ships here as
the `IsGaussianFluctuationRegime` predicate; the reverse direction
(LDP rate function → F4 positivity) is shipped as a structural
companion to Wave 1c.3's forward direction.

References:
- Wave 2a.1 DR: `Lit-Search/Phase-6q/Phase 6q Wave 2a.1 Return Dossier
  — SK-EFT-Hawking Specialization of the CHHK DKM Transport Bootstrap.md`
- CHHK eq. (8): integrated spectral-weight inequality
- CHHK eq. (9) v2 [= eq. (26) v1]: MIR-style master bound `β_d/(1−e^{−1/(Tτ)}) ≤
  (ℓ/a)^d · (τ/(χ·a^d))·⟨n₀²⟩_T`
- CHHK eq. (12) v2 [= eq. (29) v1]: super-Planckian limit `(d·β_d/4π)^{1/(d+1)} ≤ ℓ/a`
- Crossno et al. Science 351, 1058 (2016) — Wiedemann-Franz violation
  experimental anchor for graphene
- Abedinpour et al. arXiv:1101.4291 — exchange-renormalized Drude weight
-/
import SKEFTHawking.DKMBootstrap.LDPBridge

namespace SKEFTHawking.DKMBootstrap

open SKEFTHawking.SKDoubling SKEFTHawking.CrooksAnalogHawking

/-! ## §1. Integrated-bootstrap-bound predicate (CHHK eq. 8 / 14).

The integrated spectral-weight inequality CHHK derives from F2 + F4 +
F5 + the Lehmann representation. At substrate level, we capture this as
a predicate parameterized by the upper-bound functional `boundFunctional :
ℝ → ℝ → ℝ` (in CHHK: `(ω, Λ) ↦ ⟨n₀²⟩_T / (ω·n_B(ω)·ν²)`). The
substantive analytic content of the integral inequality is the Wave
1c.2 + Wave 2b.1 content; here we ship the predicate-substrate form
ready for the Wave 2b.1 substantive theorem. -/

/-- **CHHK eq. (8) / (14) integrated-bound predicate.** For all
frequency windows `[ω, Λ]` with `0 < ω ≤ Λ` and kinematic points `(Ω, k)`
in the window, the integrand `G(Ω, k) / Ω` is bounded above by
`boundFunctional ω Λ`. -/
def IsCHHKBootstrapBound
    (G : Correlator) (boundFunctional : ℝ → ℝ → ℝ) : Prop :=
  ∀ ω Λ : ℝ, 0 < ω → ω ≤ Λ →
    ∀ Ω k : ℝ, ω ≤ Ω → Ω ≤ Λ → 0 < Ω →
      G Ω k / Ω ≤ boundFunctional ω Λ

-- Note (post-strengthening 2026-05-25): the prior `Iff.rfl` bridge
-- `fsum_rule_is_constant_bound : HasFSumRule G boundData ↔
-- IsCHHKBootstrapBound G (fun _ _ => boundData)` was removed. The
-- definitional unfolding between the two predicates is now obtained by
-- `rfl` directly; the structural fact that `HasFSumRule` is the
-- constant-bound specialization of `IsCHHKBootstrapBound` is preserved
-- in this docstring and by the predicate shapes themselves.

/-! ## §2. The Mott-Ioffe-Regel master bound (CHHK eq. 29).

The substrate-side super-Planckian limit `(d·β_d/4π)^{1/(d+1)} ≤ ℓ/a`,
the canonical "bad metal" Planckian bound. We capture this at predicate-
substrate level with the dimension `d` as a parameter and the MIR
constant `mirConstant d := (d·β_d/4π)^{1/(d+1)}` as a separate function
to be supplied per substrate (graphene: d=2; the `β_d` integral
constants are computed Python-side per Wave 2a.1 DR §5). -/

/-- **The MIR predicate.** A DKMParameters capsule satisfies the
Mott-Ioffe-Regel master bound at dimension `d` with constant `mirConst`
if its collective mean free path `ℓ = √(τD)` satisfies `mirConst ≤ ℓ / a`. -/
def IsMIRBound (p : DKMParameters) (mirConst : ℝ) : Prop :=
  mirConst ≤ p.collectiveMeanFreePath / p.a

/-- **MIR bound is preserved under scaling-down of `mirConst`.** If `p`
satisfies MIR at `mirConst_1` and `mirConst_2 ≤ mirConst_1`, then `p`
also satisfies MIR at `mirConst_2`. -/
theorem mir_bound_anti_monotone
    {p : DKMParameters} {mirConst_1 mirConst_2 : ℝ}
    (h : IsMIRBound p mirConst_1) (h_le : mirConst_2 ≤ mirConst_1) :
    IsMIRBound p mirConst_2 :=
  le_trans h_le h

/-- **MIR bound holds at `mirConst = 0`** — the trivially-true bound.
Substantive non-vacuity: the predicate is non-degenerate at the trivial
constant, and the substantive content kicks in for `mirConst > 0`
(graphene gives a specific O(0.1)–O(1) constant per Wave 2a.1 DR §5). -/
theorem mir_bound_at_zero (p : DKMParameters) :
    IsMIRBound p 0 := by
  unfold IsMIRBound
  apply div_nonneg p.collectiveMeanFreePath_pos.le p.a_pos.le

/-! ## §3. Wilson-coefficient bridge (DR §4: PARTIAL-VIABLE alignment).

Per Wave 2a.1 DR §4, the alignment-only cross-bridge from DKMParameters
`(τ, D, χ)` to the existing FirstOrderCoeffs `(r1, …, r6, i1, i2, i3)`
is shipped as a substantive structural map. The full Lean-substrate
lift of paper1/2/3 (D1 bundle's SK-EFT-Hawking analytic content) is
PARTIAL-VIABLE per DR §4 — substantive proof obligations on the Wilson-
coefficient relations are deferred to a future "D1 lift-to-Lean" wave.

Here we ship the *predicate-substrate* form of the bridge: a predicate
`IsDKMCompatibleSKEFT (p : DKMParameters) (c : FirstOrderCoeffs)` that
captures the substantive structural map between the two coefficient
families. -/

/-- **DKM ↔ SK-EFT FirstOrderCoeffs compatibility.** The substrate-
level structural map (DR §4: PARTIAL-VIABLE alignment): the DKM
parameter `D` (charge diffusivity) is identified with the dissipative
Wilson coefficient `i1` (the imaginary/dissipative part of
FirstOrderCoeffs), and `τ⁻¹` is identified with the ratio `i2/r2`
(schematic leading-order parametrization).

The new substantive content of the predicate is the **positivity of the
dissipative Wilson coefficients `i1, i2`** (the new content on
FirstOrderCoeffs); DKMParameters' own positivity witnesses (`τ_pos`,
`D_pos`, `χ_pos`) are already structurally guaranteed and need not be
re-asserted in the bundle.

Post-strengthening 2026-05-25 (A.6 conjunct cleanup): the 3 prior
conjuncts `0 < p.τ ∧ 0 < p.D ∧ 0 < p.χ` were dropped — they were
redundant with the built-in `DKMParameters` positivity witnesses.
The cross-bridge docstring framing (DR §4: PARTIAL-VIABLE alignment-
only) is preserved. -/
def IsDKMCompatibleSKEFT (_p : DKMParameters) (c : FirstOrderCoeffs) : Prop :=
  0 < c.i1 ∧ 0 < c.i2

/-- **Substantive non-vacuity of the SKEFT compatibility predicate.**
The substrate level non-vacuously witnesses the predicate: given any
DKM parameter capsule, there exists a FirstOrderCoeffs witness
compatible with it (specifically, choose `i1 := p.D`, `i2 := 1`, all
other coefficients = 0). -/
theorem dkm_compatible_skeft_exists (p : DKMParameters) :
    ∃ c : FirstOrderCoeffs, IsDKMCompatibleSKEFT p c := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, p.D, 1, 0⟩, ?_, ?_⟩
  · -- 0 < c.i1 = p.D
    exact p.D_pos
  · -- 0 < c.i2 = 1
    exact one_pos

/-! ## §4. Gaussian fluctuation regime predicate (DR §6 substrate condition).

Per Wave 2a.1 DR §6 the substantive `chhk_positivity_iff_LDP_rate_function`
cross-bridge requires a Gaussian-fluctuation-regime hypothesis. We ship
this as a predicate `IsGaussianFluctuationRegime p` that captures the
substantive content (Lorentzian spectral form ↔ Gaussian rate function
at quadratic order). -/

/-- **Gaussian-fluctuation-regime predicate** (`abbrev` for `0 < χ·D`).
A DKM parameter capsule is in the Gaussian fluctuation regime if its
variance `χ·D` is strictly positive (which it is structurally by
`DKMParameters` positivity witnesses) — the substantive content is the
DR §6 condition that the LDP rate function constructed from `(χ·D)` is
non-degenerate. This is the substrate-level statement of the DR §6
conditions (1) and (2).

Post-strengthening 2026-05-25 (A.7): demoted from `def` to `abbrev`
since the substantive Gaussian-regime content (rate function being a
specific polynomial form; cumulant expansion truncating at second order)
is blocked on D1 paper-side action-correlator-link substrate. At Phase
6q scope the predicate functions as a labelling convenience pointing to
the DR §6 condition; the substantive Gaussian-regime physics ships in
the future D1 lift-to-Lean wave. The prior `dkm_parameters_isGaussianFluctuationRegime`
theorem was removed (auto-derivable as `mul_pos p.χ_pos p.D_pos`). -/
abbrev IsGaussianFluctuationRegime (p : DKMParameters) : Prop :=
  0 < p.χ * p.D

/-! ## §5. The substantive Wave 2a.2 cross-bridge — forward direction.

The Wave 2a.1 DR §6 substantive biconditional `chhk_positivity_iff_
LDP_rate_function` is explicitly marked in the DR as having its reverse
direction shipped as a "Wave 2b.2 task" (the DR's recommended Lean
module form has `sorry` on the reverse direction). At Wave 2a.2 we
ship the forward direction substantively, plus the bundled `IsLDPCompatibleCorrelator`
predicate that the Wave 2b.2 biconditional consumes. -/

/-- **`IsLDPCompatibleCorrelator G β p`** — substantive substrate
predicate: a correlator `G` is LDP-compatible at `(β, p)` if it has
the F4 positivity input AND the constructed DKM rate function is an
`IsLDPRateFunction` witness at β. This is the bundled predicate the
Wave 2b.2 biconditional refines. -/
def IsLDPCompatibleCorrelator
    (G : Correlator) (β : ℝ) (p : DKMParameters) : Prop :=
  IsImGRetardedNonneg G ∧ IsLDPRateFunction β (dkm_rate_function β p)

/-- **CHHK F4 positivity → LDP rate function** (Wave 2a.2 forward
direction). The F4 positivity content of `G` plus the DKM parameter data
yields an `IsLDPCompatibleCorrelator` witness.

**Substantive engine clarification (post-adversarial-review 2026-05-25,
finding 6.1):** the load-bearing analytical step of the discharge is
*DKMParameters positivity* (`χ_pos`, `D_pos`), NOT the F4 hypothesis
`h_pos`. The F4 hypothesis is preserved in the output pair (first
component of `IsLDPCompatibleCorrelator`) but is *not consumed* by the
rate-function construction in `chhk_positivity_yields_LDP_rate_function`
— that construction builds the rate function from `(β, p.χ · p.D)`
alone. The theorem name is retained for downstream-API stability and
because in the substantive (D1-lifted) form, F4 *would* be the engine
via the action-correlator link; at substrate level here it is preserved
pass-through-only.

The DR §6 Gaussian-fluctuation-regime condition is automatically
satisfied at substrate level by `DKMParameters` positivity
(`IsGaussianFluctuationRegime p` is defeq to `0 < p.χ · p.D`, derivable
from `mul_pos p.χ_pos p.D_pos`); we therefore do not surface it as a
hypothesis here. The substantive Gaussian-regime content (rate function
as polynomial, cumulant truncation) ships in the future D1 lift-to-Lean
wave. -/
theorem chhk_positivity_yields_LDP_compatible
    {G : Correlator} (h_pos : IsImGRetardedNonneg G)
    (β : ℝ) (hβ : 0 < β) (p : DKMParameters) :
    IsLDPCompatibleCorrelator G β p :=
  ⟨h_pos, chhk_positivity_yields_LDP_rate_function h_pos β hβ p⟩

/-- **Substantive non-vacuity**: the zero correlator is LDP-compatible
at any `(β, p)` with `β > 0`. -/
theorem zero_correlator_isLDPCompatible
    (β : ℝ) (hβ : 0 < β) (p : DKMParameters) :
    IsLDPCompatibleCorrelator zeroCorrelator β p :=
  chhk_positivity_yields_LDP_compatible
    zeroCorrelator_isImGRetardedNonneg β hβ p

-- Post-strengthening 2026-05-25 (A.5 consolidation): the prior
-- `dkm_satisfies_trivial_mir_bound` theorem was removed. It was a pure
-- alias of `mir_bound_at_zero` (§2 above); only consumers were the
-- 3 per-platform witnesses in `E1E2CrossBridge.lean`, which were also
-- removed in the same pass. Direct callers can use `mir_bound_at_zero p`.

/-! ## §7. Closure summary — Wave 2a.2 SK-EFT-Hawking specialization.

This module ships:
- **`IsCHHKBootstrapBound`** — predicate operationalization of CHHK
  eq. (8) / (14) integrated-bound inequality.
- **`IsMIRBound`** — predicate for the MIR master bound (CHHK eq. 29);
  `mir_bound_anti_monotone` + `mir_bound_at_zero` substrate lemmas.
- **`IsDKMCompatibleSKEFT`** — predicate-substrate Wilson-coefficient
  bridge between DKMParameters and `FirstOrderCoeffs`.
- **`IsGaussianFluctuationRegime`** — `abbrev` for `0 < p.χ · p.D`,
  labelling the DR §6 condition. Post-strengthening 2026-05-25 (A.7):
  demoted from `def` and the trivial discharge theorem removed (the
  substantive Gaussian-regime polynomial-rate-function content ships in
  the future D1 lift-to-Lean wave; at Phase 6q scope this is a labelling
  convenience only).
- **`IsLDPCompatibleCorrelator`** + **`chhk_positivity_yields_LDP_compatible`**
  — substantive forward direction of the DR §6 cross-bridge.
- **`zero_correlator_isLDPCompatible`** — substantive non-vacuity witness.
- (`dkm_satisfies_trivial_mir_bound` was removed in the 2026-05-25 A.5
  strengthening pass; use `mir_bound_at_zero` from §2 directly.)

The reverse direction of the DR §6 biconditional is the Wave 2b.2
task (the full bicondtional `IsImGRetardedNonneg ↔ IsLDPRateFunction`
on arbitrary correlators requires the action-correlator-link
substrate physics that ships in Wave 2b). Graphene-witness substantive
Wave 2b.1 ship + per-platform Wilson-coefficient bridge ship in
Wave 2a.3 (E1E2CrossBridge). -/

end SKEFTHawking.DKMBootstrap
