/-
# Phase 6q Wave 2a.2 — SK-EFT-Hawking specialization of CHHK DKM bootstrap

Wave 2a.1 DR motivates specializing transport to the SK-EFT-Hawking
horizon. This module defines the `IsCHHKBootstrapBound` pointwise bound
and the `IsMIRBound` inequality predicate (CHHK v2 Eq. (12)),
and a coefficient positivity test for the existing
SK-EFT-Hawking machinery (`SKEFTHawking.SKDoubling.FirstOrderCoeffs` /
`CombinedDissipativeCoeffs`).

**Historical Wave 2a.1 DR §1 recommendation:** the initial comparator is
**graphene Dirac fluid** (E2 bundle) — the only project platform that is
*natively lattice* with a microscopically conserved charge, the cleanest
dynamical-KMS Z₂ structure, and experimental anchors at Crossno 2016
(Wiedemann-Franz violation) + Abedinpour 2010 (exchange-renormalized
Drude weight). BEC and polariton are PARTIAL-VIABLE secondary targets.

**Wave 2a.2 deliverables:**
1. **`IsCHHKBootstrapBound`** — pointwise bound with a frequency-window
   threshold.
2. **`IsMIRBound`** — predicate for the Mott-Ioffe-Regel inequality
   (CHHK v2 Eq. (12)): `(d·β_d / 4π)^(1/(d+1)) ≤ ℓ/a`.
3. **Wilson-coefficient positivity** — tests `0 < i1` and `0 < i2`.
   Physical coefficient identification remains open.
4. **Rate-function compatibility** — pairs supplied F4 with the
   parameterized rate-function witness.

References:
- Wave 2a.1 DR: `Lit-Search/Phase-6q/Phase 6q Wave 2a.1 Return Dossier
  — SK-EFT-Hawking Specialization of the CHHK DKM Transport Bootstrap.md`
- CHHK v2 Eqs. (2), (25): thermal weighted spectral bound
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

/-! ## §1. Legacy pointwise bootstrap bound.

The source bounds a thermal integral over frequency and momentum. Here
`boundFunctional ω Λ` sets a threshold for each point. -/

/-- In every window `[ω, Λ]` with `0 < ω ≤ Λ`, bound `G(Ω, k) / Ω` at
each included positive frequency and every momentum. -/
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

/-! ## §2. Predicate for the MIR inequality (CHHK v2 Eq. (12)).

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
This is the zero-constant control. Physical positive MIR lower bounds
require separate evidence. -/
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

The proposed identification motivates the positivity test below. -/

/-- Tests positivity of `i1` and `i2`. The DKM parameter argument is
unused. The proposed relations `D = i1` and `τ⁻¹ = i2/r2` remain separate
obligations. -/
def IsDKMCompatibleSKEFT (_p : DKMParameters) (c : FirstOrderCoeffs) : Prop :=
  0 < c.i1 ∧ 0 < c.i2

/-- A witness for the positivity test, with `i1 := p.D` and `i2 := 1`. -/
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
an alias `IsGaussianFluctuationRegime p` for variance positivity. -/

/-- **Gaussian-fluctuation-regime predicate** (`abbrev` for `0 < χ·D`).
The alias is positive by the DKM parameter fields. A Gaussian
fluctuation law for a state requires separate evidence.

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

/-! ## §5. Pairing F4 with the constructed rate-function witness.

The Wave 2a.1 DR §6 biconditional motivates this interface. The theorem
below preserves the F4 input and pairs it with the parameterized
rate-function witness. -/

/-- **`IsLDPCompatibleCorrelator G β p`** — compatibility
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

/-- Zero-correlator control for the compatibility pair at `β > 0`. -/
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
- **`IsCHHKBootstrapBound`** — pointwise bound on `G(Ω,k) / Ω`.
- **`IsMIRBound`** — predicate for the MIR inequality (CHHK v2 Eq. (12));
  `mir_bound_anti_monotone` + `mir_bound_at_zero` substrate lemmas.
- **`IsDKMCompatibleSKEFT`** — Wilson-coefficient positivity test.
- **`IsGaussianFluctuationRegime`** — `abbrev` for `0 < p.χ · p.D`,
  labelling the DR §6 condition. Post-strengthening 2026-05-25 (A.7):
  demoted from `def` and the trivial discharge theorem removed (the
  substantive Gaussian-regime polynomial-rate-function content ships in
  the future D1 lift-to-Lean wave; at Phase 6q scope this is a labelling
  convenience only).
- **`IsLDPCompatibleCorrelator`** + **`chhk_positivity_yields_LDP_compatible`**
  — package F4 and the parameter-only rate-function witness.
- **`zero_correlator_isLDPCompatible`** — zero-correlator control.
- (`dkm_satisfies_trivial_mir_bound` was removed in the 2026-05-25 A.5
  strengthening pass; use `mir_bound_at_zero` from §2 directly.)

The thermal weighted bound, physical MIR inference, Wilson-coefficient
identification and microscopic LDP connection remain separate
obligations. -/

end SKEFTHawking.DKMBootstrap
