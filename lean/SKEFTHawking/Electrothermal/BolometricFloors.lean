import SKEFTHawking.Electrothermal.ETFResponsivity
import SKEFTHawking.Detection.MatchedFilter

/-!
# Bolometric noise floors and the composed detector error floor (Phase 6EC, Wave 3)

The closing wave of the `6E*` detector-side stack. Wave 1 fixed the linearized electrothermal
model and its stability dichotomy; Wave 2 derived the responsivity and its `(1+ℒ)` correction.
This wave supplies the two noise channels a thermal detector actually has — **phonon**
(thermal-fluctuation) noise and **Johnson** noise referred to input power — composes them in
quadrature through 6EB's algebra, and hands the result to 6EB's matched-filter budget and 6EA's
Gaussian threshold floor.

The capstone (`bolometer_error_floor`) is the statement the whole stack existed to make: *no
threshold readout of a thermal detector of this linearized class, through any admissible
single-shot filter, can average better than this error* — with every modelling assumption
(equilibrium, whiteness, uncorrelatedness, the device identification) sitting in the binder list.

## What is cited versus what is built

Per the roadmap, the FDT content is **cited, not re-derived**:

* `phononNEP` / `johnsonNEP` are built here (nothing electrothermal existed), but
  `phonon_psd_eq_johnsonNyquist_scaled` shows the phonon PSD **is** the repo-canonical
  `GrapheneNoiseFormula.johnsonNyquistPSD` evaluated at the *thermal* conductance and scaled by
  `T` — so the `4·k_B·T²·G` prefactor is tied to an existing declaration rather than asserted.
* Quadrature composition is **6EB's** `nep_quadrature_two` / `nep_quadrature_add`, consumed with
  its `IsUncorrelatedAt` hypothesis intact. This wave does not restate quadrature.
* The error floor is **6EB's** `error_floor_from_budget` composed with **6EA's**
  `avgError_ge_gaussianQ_sharp`, reached through `matchedBudget` at `S₀ := NEP_total²`.

## Conventions (inherited, not re-chosen)

One-sided PSD throughout, from 6EB Wave 1's `IsWhiteFilteredVariance`. The phonon channel's
one-sided PSD is `4·k_B·T²·G` and the Johnson *current* PSD is `4·k_B·T/R`; both are referred to
input power by dividing by the **ETF-corrected** responsivity, never the bare one — using the bare
form understates the Johnson NEP by exactly `|1+ℒ|`
(`johnsonNEP_bare_understates_by_one_plus_loopGain`), which is Wave 2's overclaim reappearing in
the noise budget.

## Roadmap UNKNOWN-2, resolved as pre-decided

The white `4·k_B·T²·G` phonon form ships with the equilibrium hypothesis explicit
(`IsThermalFluctuationLimited`, a `Prop` parameter in the 6EB Wave-1 style). The `γ`-factor
gradient correction — for a detector with a non-negligible temperature drop across the link — is
**not** shipped and is not blocked on: it is a tagged extension, and
`phononPSD_gamma_correction_not_modelled` records in-tree that the shipped form is the `γ = 1`
special case so no consumer can mistake it for the general result.

**⚠ Guardrail (inherited).** Every statement is about the *stated linearized model* with declared
noise hypotheses. No claim about any physical instrument.

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology*.
-/

namespace SKEFTHawking.Electrothermal

open SKEFTHawking.Detection SKEFTHawking.QuantumNetwork MeasureTheory

namespace ETFModel

/-! ## The phonon (thermal-fluctuation) channel -/

/-- **One-sided phonon (thermal-fluctuation) noise PSD** of the thermal link: `4·k_B·T²·G`.

`kB` is Boltzmann's constant and `T` the operating temperature, in the dimensionless-reals unit
contract this series inherits from `GrapheneNoiseFormula`. This is the *power* PSD referred to the
absorber, so it composes directly against the matched-filter budget without a responsivity step —
which is why the phonon channel is the irreducible one. -/
noncomputable def phononPSD (m : ETFModel) (kB T : ℝ) : ℝ := 4 * kB * T ^ 2 * m.G

/-- **Phonon NEP** — the square root of `phononPSD`, via 6EB's `nepOfPSD` rather than a fresh
square root, so the spectral-NEP convention is the one 6EB fixed. -/
noncomputable def phononNEP (m : ETFModel) (kB T : ℝ) : ℝ := nepOfPSD (m.phononPSD kB T)

/-- **The equilibrium / white-approximation hypothesis, declared as a `Prop` parameter.**

`Vph` is the phonon channel's output-variance functional; the channel is thermal-fluctuation
limited exactly when that variance is white with one-sided PSD `phononPSD`. Carried as a
hypothesis for the same reason 6EB Wave 1 carries whiteness that way: the repo models no
stochastic processes, and both equilibrium and flatness are *modelling assumptions about the
link*, not consequences of the algebra. They appear in the binder list of every consuming
statement below. -/
def IsThermalFluctuationLimited (Vph : (ℝ → ℝ) → ℝ) (m : ETFModel) (kB T Tw : ℝ) : Prop :=
  IsWhiteFilteredVariance Vph (m.phononPSD kB T) Tw

/-- **The phonon prefactor is the repo-canonical FDT PSD, cited not asserted.**

    4·k_B·T²·G  =  johnsonNyquistPSD (k_B·T) G · T

i.e. the phonon PSD is `GrapheneNoiseFormula.johnsonNyquistPSD` evaluated at the **thermal**
conductance `G` (rather than an electrical one) and scaled by the operating temperature. This is
what ties the `4` and the `T²` to an existing declaration — the roadmap's "cite `FDTNoiseFloor`,
do not re-derive it" — instead of leaving them as a literal a reader must trust. -/
theorem phonon_psd_eq_johnsonNyquist_scaled (m : ETFModel) (kB T : ℝ) :
    m.phononPSD kB T = GrapheneNoiseFormula.johnsonNyquistPSD (kB * T) m.G * T := by
  unfold phononPSD GrapheneNoiseFormula.johnsonNyquistPSD
  ring

/-- The phonon PSD is positive at any physical bias point. -/
theorem phononPSD_pos (m : ETFModel) {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G) :
    0 < m.phononPSD kB T := by
  unfold phononPSD
  positivity

/-- **The spectral round trip:** `NEP_ph² = phononPSD`. Needs non-negativity of the PSD — this is
`nepOfPSD`'s square, not a definitional unfolding — and is what lets the declared equilibrium
hypothesis be handed to 6EB's quadrature machinery in `isWhite_of_thermalFluctuationLimited`. -/
theorem phononNEP_sq (m : ETFModel) {kB T : ℝ} (hnn : 0 ≤ m.phononPSD kB T) :
    m.phononNEP kB T ^ 2 = m.phononPSD kB T := by
  unfold phononNEP nepOfPSD
  exact Real.sq_sqrt hnn

/-- **The declared equilibrium hypothesis feeds 6EB's quadrature algebra.**

`IsThermalFluctuationLimited` is stated with the *PSD*; `nep_quadrature_add` consumes whiteness
stated with the *squared NEP*. This is the bridge, and it is the reason
`bolometer_nep_floor` below is a composition rather than a forwarder: the physical hypothesis goes
in, the algebraic precondition comes out. -/
theorem isWhite_of_thermalFluctuationLimited {Vph : (ℝ → ℝ) → ℝ} {m : ETFModel} {kB T Tw : ℝ}
    (hlim : IsThermalFluctuationLimited Vph m kB T Tw) (hnn : 0 ≤ m.phononPSD kB T) :
    IsWhiteFilteredVariance Vph (m.phononNEP kB T ^ 2) Tw := by
  rw [m.phononNEP_sq hnn]
  exact hlim

/-- **The phonon floor is monotone in the thermal conductance** — a better-isolated detector is
quieter, and strictly so. A screen, not a platitude: it makes the shipped form falsifiable against
a reported NEP that improves with increasing `G`. -/
theorem phononPSD_strictMono_conductance {m m' : ETFModel} {kB T : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : m.G < m'.G) :
    m.phononPSD kB T < m'.phononPSD kB T := by
  unfold phononPSD
  have h4 : 0 < 4 * kB * T ^ 2 := by positivity
  exact mul_lt_mul_of_pos_left hG h4

/-- **The shipped phonon form is the `γ = 1` special case, recorded in-tree.**

Roadmap UNKNOWN-2: the general thermal-fluctuation NEP carries a geometry factor `γ` for the
temperature gradient across the link, `NEP² = 4·γ·k_B·T²·G`. This wave ships `γ = 1` (the
isothermal-link limit) with the equilibrium hypothesis explicit, and this theorem states the
relationship so that no consumer can read the shipped form as the general result: for `γ > 1` the
true floor is **strictly higher** than the one shipped, so the shipped form is an *optimistic*
bound outside its limit — the direction a reader must know. -/
theorem phononPSD_gamma_correction_not_modelled (m : ETFModel) {kB T γ : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G) (hγ : 1 < γ) :
    m.phononPSD kB T < γ * m.phononPSD kB T := by
  have hpos := m.phononPSD_pos hkB hT hG
  nlinarith

/-! ## The Johnson channel, referred to input power -/

/-- **One-sided Johnson current-noise PSD** of the bias-point resistance: `4·k_B·T/R`. Stated in
the same convention as `phononPSD` (both are `johnsonNyquistPSD`-shaped; here the conductance is
the electrical `1/R`). -/
noncomputable def johnsonCurrentPSD (m : ETFModel) (kB T : ℝ) : ℝ := 4 * kB * T / m.R

/-- **Johnson NEP, referred to input power through the ETF-corrected responsivity.**

    NEP_J = √(4·k_B·T/R) / |R_etf|

The responsivity used is Wave 2's `responsivityETF` — the physical one — never `responsivityBare`.
The consequence of getting that wrong is quantified in
`johnsonNEP_bare_understates_by_one_plus_loopGain`. -/
noncomputable def johnsonNEP (m : ETFModel) (kB T : ℝ) : ℝ :=
  nepOfPSD (m.johnsonCurrentPSD kB T) / |m.responsivityETF|

/-- **The bare-responsivity Johnson budget understates the true Johnson NEP by exactly `|1+ℒ|`.**

Wave 2's overclaim reappearing where it does real damage: NEP is output noise *divided* by
responsivity, so the bare form — which overstates responsivity by `(1+ℒ)` — understates this noise
channel by the same factor. At the published `ℒ = 3` bias point that is a factor of 4 in a
*noise* budget.

Consumes `responsivity_etf_correction`, so this is a computation across the wave boundary rather
than a restatement. -/
theorem johnsonNEP_bare_understates_by_one_plus_loopGain (m : ETFModel) (kB T : ℝ)
    (hGne : m.G ≠ 0) (hL : 1 + m.loopGain ≠ 0) :
    nepOfPSD (m.johnsonCurrentPSD kB T) / |m.responsivityBare|
      = m.johnsonNEP kB T / |1 + m.loopGain| := by
  unfold johnsonNEP
  rw [responsivity_etf_correction m hGne hL, abs_mul]
  rw [div_div, mul_comm (|1 + m.loopGain|) (|m.responsivityETF|)]

/-! ## Quadrature composition — 6EB's algebra, consumed -/

/-- **The two-channel bolometer NEP family**, indexed so it plugs directly into 6EB's
`nep_quadrature_two`: channel `0` is phonon, channel `1` is Johnson. -/
noncomputable def bolometerNEP (m : ETFModel) (kB T : ℝ) : Fin 2 → ℝ
  | 0 => m.phononNEP kB T
  | 1 => m.johnsonNEP kB T

/-- **The composed bolometer noise floor**, in the form a budget table is written in:

    σ_out / H(0)  =  √(NEP_ph² + NEP_J²) · √ENBW(h)

Quadrature itself is 6EB's `nep_quadrature_two`, consumed with its `IsUncorrelatedAt` hypothesis
intact (`Detection.quadrature_uncorrelated_hypothesis_load_bearing` already witnesses that `hindep`
cannot be dropped). What this theorem adds is the **physical** entry point: the phonon channel is
supplied as the declared equilibrium hypothesis `IsThermalFluctuationLimited`, and the whiteness
precondition 6EB needs is discharged internally via `isWhite_of_thermalFluctuationLimited`. So a
consumer states physics, not spectral algebra. -/
theorem bolometer_nep_floor (m : ETFModel) {kB T Tw : ℝ} {Vtot : (ℝ → ℝ) → ℝ}
    {V : Fin 2 → (ℝ → ℝ) → ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G)
    (hindep : IsUncorrelatedAt Finset.univ Vtot V)
    (hphonon : IsThermalFluctuationLimited (V 0) m kB T Tw)
    (hjohnson : IsWhiteFilteredVariance (V 1) (m.johnsonNEP kB T ^ 2) Tw)
    (h : ℝ → ℝ) (hDC : (∫ x in (0:ℝ)..Tw, h x) ≠ 0) :
    Real.sqrt (Vtot h / (∫ x in (0:ℝ)..Tw, h x) ^ 2)
      = Real.sqrt (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) * Real.sqrt (enbw h Tw) := by
  have hwhite : ∀ i, IsWhiteFilteredVariance (V i) (m.bolometerNEP kB T i ^ 2) Tw := by
    intro i
    match i with
    | 0 => exact isWhite_of_thermalFluctuationLimited hphonon (m.phononPSD_pos hkB hT hG).le
    | 1 => exact hjohnson
  exact nep_quadrature_two hindep hwhite h hDC

/-- **The phonon-limited screen, as an `iff`** — the analogue of 6EB's `shotLimited_iff_psd_lt`,
and a decision procedure on a budget rather than a one-way heuristic.

A thermal detector is **phonon-limited** exactly when the input-referred Johnson PSD falls below
the phonon PSD. Both sides are in the same one-sided convention, and the Johnson side carries its
responsivity referral explicitly — so this is the comparison a budget table can be checked against,
not a qualitative claim.

Shipped in place of the two `x² ≤ x² + y²` orderings the roadmap's "monotone consequences" would
literally have licensed: those are true of any reals and carry no bolometric content, whereas this
separates the two physical regimes.

Carries **no** non-vanishing-responsivity binder: at `R_etf = 0` both sides collapse to
`0 < phononPSD` identically (Lean's total division), so the equivalence holds there too and a
`responsivityETF ≠ 0` hypothesis would be dead weight rather than a guard. -/
theorem phononLimited_iff_psd_lt (m : ETFModel) {kB T : ℝ}
    (hnnPh : 0 ≤ m.phononPSD kB T) (hnnJ : 0 ≤ m.johnsonCurrentPSD kB T) :
    m.johnsonNEP kB T ^ 2 < m.phononNEP kB T ^ 2
      ↔ m.johnsonCurrentPSD kB T / m.responsivityETF ^ 2 < m.phononPSD kB T := by
  rw [m.phononNEP_sq hnnPh]
  unfold johnsonNEP nepOfPSD
  rw [div_pow, Real.sq_sqrt hnnJ, sq_abs]

/-- **The composed PSD is positive at any physical bias point** — discharged from the physical
hypotheses (`0 < kB`, `0 < T`, `0 < G`) rather than assumed, which is what makes the capstone
below carry content instead of forwarding an abstract positivity binder. -/
theorem bolometer_psd_pos (m : ETFModel) {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G) :
    0 < m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2 := by
  have hph : 0 < m.phononNEP kB T ^ 2 := by
    rw [m.phononNEP_sq (m.phononPSD_pos hkB hT hG).le]
    exact m.phononPSD_pos hkB hT hG
  nlinarith [sq_nonneg (m.johnsonNEP kB T)]

/-! ## The capstone: the composed detector error floor -/

/-- **The capstone of the `6E*` detector stack.**

For a thermal detector of this linearized class, with total input-referred noise PSD
`S₀ = NEP_ph² + NEP_J²`, read out through **any** admissible single-shot filter and classified by
**any** threshold: the average assignment error is at least `Q(budget/2)`, where the budget is
6EB's filter-free matched-filter budget at the template `s`.

Everything upstream is consumed, nothing re-derived: 6EB's `error_floor_from_budget` (hence 6EA's
`avgError_ge_gaussianQ_sharp`) supplies the floor, and the noise scale entering it is this wave's
quadrature-composed bolometer PSD. The device identification (`hμ`, `hσV`) and the whiteness of
the composed channel (`hwhite`) remain the consumer's declared hypotheses.

The **positivity of the composed noise scale is discharged here** from the physical hypotheses
`0 < kB`, `0 < T`, `0 < G` (via `bolometer_psd_pos`) rather than taken as an abstract binder — so
the capstone is a composition of this wave's physics with 6EB's bound, not a forwarder.

This is what makes the layer a *ceiling*: it is stated against the best possible linear readout,
so no cleverer filter and no better threshold can beat it. -/
theorem bolometer_error_floor (m : ETFModel) {kB T Tw : ℝ} {V : (ℝ → ℝ) → ℝ}
    {s hf : ℝ → ℝ} {μ₀ μ₁ σ t : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G)
    (hwhite : IsWhiteFilteredVariance V
      (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw)
    (hTw : 0 ≤ Tw)
    (hadm : IsAdmissibleFilter Tw s hf)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 Tw)
    (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..Tw, hf x * s x) (hσV : σ = Real.sqrt (V hf)) :
    gaussianQ (matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s / 2)
      ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t) :=
  error_floor_from_budget hwhite (m.bolometer_psd_pos hkB hT hG) hTw hadm hs hσ hμle hμ hσV

end ETFModel

end SKEFTHawking.Electrothermal
