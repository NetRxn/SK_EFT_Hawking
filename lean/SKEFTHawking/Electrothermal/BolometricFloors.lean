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

**And its irreducible form** (`phonon_only_error_floor`, with the channel-agnostic
`phonon_floor_of_psd_ge` behind it) removes the Johnson channel from the *conclusion*: the floor
computed from the thermal-fluctuation channel alone still binds, so eliminating Johnson noise
entirely — or any other channel — cannot beat it. That is the phase's headline thesis, and until
2026-07-29 it was prose rather than a declaration: `bolometer_error_floor` bounds the error by
`Q(B(NEP_ph² + NEP_J²)/2)`, which is a statement about a detector that *has* Johnson noise. The
missing step was the budget's antitonicity in the noise PSD, now shipped in 6EB as
`Detection.matchedBudget_antitone_psd`.

## What is cited versus what is built

Per the roadmap, the FDT content is **cited, not re-derived**:

* The genuine FDT citation is `johnsonCurrentPSD_eq_johnsonNyquist`: the Johnson *current* PSD is
  `GrapheneNoiseFormula.johnsonNyquistPSD` at the **electrical** conductance `1/R` — right channel,
  right conductance, coherent units.
* The phonon prefactor `4·k_B·T²·G` is **asserted, not cited**: it is the thermal-fluctuation
  result, and it is *not* derivable from the Johnson–Nyquist declaration.
  `phonon_psd_eq_johnsonNyquist_scaled` records the arithmetic resemblance and nothing more — see
  its docstring, which states plainly that the identity holds for any `4·a·b²·c` and therefore
  constrains nothing.
* Quadrature composition is **6EB's** `nep_quadrature_two` / `nep_quadrature_add`, consumed with
  its `IsUncorrelatedAt` hypothesis intact. This wave does not restate quadrature.
* The error floor is **6EB's** `error_floor_from_budget` composed with **6EA's**
  `avgError_ge_gaussianQ_sharp`, reached through `matchedBudget` at `S₀ := NEP_total²`; the
  irreducible form additionally consumes 6EB's `matchedBudget_antitone_psd` and 6EA's
  `gaussianQ_antitone`, neither restated here.

## Conventions at the Wave-2 seam

Responsivities are **signed** (Wave 2, Guardrail 2); NEPs and PSDs are **magnitudes** (6EB:
`nepOfPSD S = √S ≥ 0`). Every referral in this file therefore divides by `|responsivityETF|`, and
as of 2026-07-29 Wave 2's own NEP transfers do too, so the two waves no longer disagree at the
seam. The magnitude is the right object for a noise density — but it carries **no** stability
information, which `johnsonNEP_correction_magnitude_loses_stability_information` proves rather
than asserts (two published bias points, identical `|1 − ℒ| = 2`, opposite sides of Wave 1's
dichotomy). Correcting a Johnson budget is not certifying an operating point.

## Conventions (inherited, not re-chosen)

One-sided PSD throughout, from 6EB Wave 1's `IsWhiteFilteredVariance`. The phonon channel's
one-sided PSD is `4·k_B·T²·G` and the Johnson *current* PSD is `4·k_B·T/R`.

**Only the Johnson channel is referred through the responsivity.** Thermal-fluctuation noise
enters the heat balance at exactly the point the signal does, so it is already an input-referred
*power* and needs no responsivity step (`phononPSD`'s docstring); dividing it by the responsivity
would double-refer it. The asymmetry is physics, not an oversight.

The Johnson channel carries **two** distinct ETF effects — the ETF-corrected responsivity *and*
the noise source's own thermal feedback `johnsonTransfer = (1−ℒ)/(1+ℒ)` — whose net effect is that
an ETF-unaware budget understates this channel by `|1 − ℒ|`
(`johnsonNEP_eq_abs_one_sub_loopGain_mul_naive`).

## Roadmap UNKNOWN-2, resolved as pre-decided

The white `4·k_B·T²·G` phonon form ships with the equilibrium hypothesis explicit
(`IsThermalFluctuationLimited`, a `Prop` parameter in the 6EB Wave-1 style). The `γ`-factor
gradient correction — for a detector with a non-negligible temperature drop across the link — is
now **modelled**: `phononPSDGamma` carries it, `IsThermalFluctuationLimitedGamma` is the
general-γ equilibrium hypothesis, and `phononPSD_eq_phononPSDGamma_one` pins the shipped form as
the `γ = 1` (isothermal-link) case.

**⚠ Direction corrected 2026-07-31.** This header previously recorded the `γ = 1` form as an
*optimistic* bound, on the strength of two theorems hypothesizing `γ > 1`. That is backwards.
Referred to the bolometer temperature, `γ ∈ (0, 1]` (Mather 1982; `F_link ∈ [1/2, 1]` in the TES
literature — see `phononPSDGamma`'s provenance note), so the shipped form **over**states the
phonon noise and the `γ = 1` floor **overstates the floor** for any gradient-loaded detector.
That is fail-open in the direction this module names as its worst available defect, and it is now
stated as a theorem (`gammaOne_phononFloor_overstates`) rather than mis-recorded in prose.

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

/-- **An arithmetic resemblance, NOT a citation** — labelled as such deliberately.

    4·k_B·T²·G  =  johnsonNyquistPSD (k_B·T) G · T

This is true, and it constrains **nothing**: `johnsonNyquistPSD x y = 4·x·y`, so the identity holds
for *any* `4·a·b²·c` whatsoever. It is also unit-incoherent as a citation — `johnsonNyquistPSD`'s
declared contract is a **current** PSD at an **electrical** conductance, and `G` here is thermal.

It is kept only because the resemblance is worth recording, and it is named honestly so that no
reader mistakes it for provenance. The phonon prefactor is the **thermal-fluctuation** result and
is *asserted* by `phononPSD`; it is not derivable from Johnson–Nyquist. The genuine FDT citation in
this file is `johnsonCurrentPSD_eq_johnsonNyquist`.

*(Corrected 2026-07-29 after adversarial review, which showed the original "cited, not asserted"
docstring claim was false.)* -/
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

/-- **The PSD-stated equilibrium hypothesis feeds 6EB's NEP²-stated quadrature algebra.**

`IsThermalFluctuationLimited` is stated with the *PSD*; `nep_quadrature_add` consumes whiteness
stated with the *squared NEP*. The bridge between them is `phononNEP_sq`, i.e. the spectral round
trip `(√S)² = S`, which is where the non-negativity hypothesis `hnn` is spent.

**Scope of the claim.** `IsThermalFluctuationLimited` is a *definitional alias* for
`IsWhiteFilteredVariance Vph (phononPSD …) Tw`, so it supplies a physically meaningful **name**,
not additional content — an abbreviation cannot make a consumer's hypothesis stronger or weaker.
What this lemma genuinely contributes is the `√`-round-trip conversion, and what the consumers
genuinely contribute is discharging `hnn` from the *physical* hypotheses `0 < kB`, `0 < T`,
`0 < G` through `phononPSD_pos` rather than carrying an abstract non-negativity binder.
*(Claim narrowed 2026-07-29 after adversarial review: the earlier docstring credited the alias
with the work.)* -/
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

/-- **The general (γ-corrected) thermal-fluctuation PSD**, `4·γ·k_B·T²·G`.

`γ` is the thermal-link gradient factor — `F_link` in the TES instrument literature. Referred to
the **bolometer** temperature `T` and the conductance `G(T)` at that temperature (the convention
`phononPSD` fixes), it obeys `0 < γ ≤ 1`: `γ = 1` exactly in the isothermal-link limit
`T_bolo → T_bath`, falling toward `1/2` for a strongly loaded detector.

**Provenance (added 2026-07-31; previously the prefactor was asserted).** Mather's non-equilibrium
bolometer theory [Appl. Opt. **21**, 1125 (1982), DOI 10.1364/AO.21.001125] establishes that phonon
noise in the link is *reduced* relative to the equilibrium `4k_BT²G` form — by as much as 30 %. In
the diffuse phonon-conduction case the factor is

    γ  =  n/(2n+1) · ((T_b/T_s)^(2n+1) − 1)/((T_b/T_s)^n − 1) · (T_b/T_s)^(−(n+1))

with `n` the thermal-conductivity index and `T_b/T_s` the bolometer-to-bath temperature ratio
(the third factor converts the literature's `T_bath`-referred statement to this module's
`T_bolo`-referred convention, using `G ∝ T^(n−1)`). It tends to `1` as `T_b/T_s → 1` and equals
`≈ 0.47` at `T_b/T_s = 2, n = 4`, reproducing the quoted `[1/2, 1]` range. -/
noncomputable def phononPSDGamma (m : ETFModel) (kB T γ : ℝ) : ℝ := 4 * γ * kB * T ^ 2 * m.G

/-- **The shipped phonon PSD is exactly the `γ = 1` case** — the isothermal-link limit. -/
theorem phononPSD_eq_phononPSDGamma_one (m : ETFModel) (kB T : ℝ) :
    m.phononPSD kB T = m.phononPSDGamma kB T 1 := by
  unfold phononPSD phononPSDGamma
  ring

/-- **γ can only REDUCE the phonon PSD**: for `0 < γ < 1` the true PSD is *strictly below* the
shipped `γ = 1` form.

⚠️ **Direction corrected 2026-07-31 (physics error, not a wording change).** Two now-deleted
theorems (`phononPSD_gamma_correction_not_modelled`, `phononPSD_lt_phononPSDGamma`) hypothesized
`1 < γ` and concluded the shipped form was an *optimistic* bound. That is backwards: `γ` is
bounded above by `1` (see `phononPSDGamma`'s provenance note), so `1 < γ` is an unphysical regime
and the shipped form is an **over**estimate of the phonon noise, never an underestimate. The
consequence for this module's stated defect class is the opposite of what was recorded — see
`gammaOne_phononFloor_overstates`. -/
theorem phononPSDGamma_lt_phononPSD (m : ETFModel) {kB T γ : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    m.phononPSDGamma kB T γ < m.phononPSD kB T := by
  have hpos := m.phononPSD_pos hkB hT hG
  unfold phononPSDGamma
  unfold phononPSD at hpos ⊢
  nlinarith

/-- The non-strict form, valid on the whole physical range `γ ≤ 1`. -/
theorem phononPSDGamma_le_phononPSD (m : ETFModel) {kB T γ : ℝ}
    (hkB : 0 ≤ kB) (hG : 0 ≤ m.G) (hγ : γ ≤ 1) :
    m.phononPSDGamma kB T γ ≤ m.phononPSD kB T := by
  unfold phononPSDGamma phononPSD
  nlinarith [mul_nonneg (mul_nonneg hkB (sq_nonneg T)) hG]

/-- **The `γ = 1` floor is NOT conservative for a gradient-loaded detector — it OVERSTATES.**

This is the scope statement that matters, and it points the opposite way from the one this module
shipped until 2026-07-31. A floor claims `error ≥ F`. Because the true `γ` is `< 1` for any
detector with a real temperature gradient across its link, the true phonon PSD — and hence the
true noise floor — is *strictly below* the one computed at `γ = 1`. A detector can therefore sit
strictly between the true floor and the shipped floor, so asserting the `γ = 1` floor of this
module for such a detector is an **overclaim**, i.e. fail-open in exactly the direction the module
header names as the worst defect available.

The shipped theorems are not unsound: every one of them is conditional on
`IsThermalFluctuationLimited`, which pins the variance to be white *at the `γ = 1` PSD*, so a
gradient-loaded detector simply fails their hypothesis and they say nothing about it. What was
wrong was the recorded *direction of the risk*. Consumers wanting the general case should carry
`IsThermalFluctuationLimitedGamma` below. -/
theorem gammaOne_phononFloor_overstates (m : ETFModel) {kB T γ : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    m.phononPSDGamma kB T γ < m.phononPSD kB T ∧ m.phononPSD kB T = m.phononPSDGamma kB T 1 :=
  ⟨m.phononPSDGamma_lt_phononPSD hkB hT hG hγ0 hγ1, m.phononPSD_eq_phononPSDGamma_one kB T⟩

/-- **The general-γ equilibrium hypothesis**, so a consumer modelling a gradient-loaded link has a
declared `Prop` to carry instead of being silently restricted to `γ = 1`. The `γ = 1` instance is
definitionally `IsThermalFluctuationLimited`, recorded by
`isThermalFluctuationLimitedGamma_one_iff`. -/
def IsThermalFluctuationLimitedGamma (Vph : (ℝ → ℝ) → ℝ) (m : ETFModel) (kB T γ Tw : ℝ) : Prop :=
  IsWhiteFilteredVariance Vph (m.phononPSDGamma kB T γ) Tw

/-- The general-γ hypothesis at `γ = 1` is the shipped one. -/
theorem isThermalFluctuationLimitedGamma_one_iff {Vph : (ℝ → ℝ) → ℝ} {m : ETFModel} {kB T Tw : ℝ} :
    IsThermalFluctuationLimitedGamma Vph m kB T 1 Tw ↔ IsThermalFluctuationLimited Vph m kB T Tw := by
  unfold IsThermalFluctuationLimitedGamma IsThermalFluctuationLimited
  rw [m.phononPSD_eq_phononPSDGamma_one kB T]

/-! ## The Johnson channel, referred to input power -/

/-- **One-sided Johnson current-noise PSD** of the bias-point resistance: `4·k_B·T/R`. Stated in
the same convention as `phononPSD` (both are `johnsonNyquistPSD`-shaped; here the conductance is
the electrical `1/R`). -/
noncomputable def johnsonCurrentPSD (m : ETFModel) (kB T : ℝ) : ℝ := 4 * kB * T / m.R

/-- **The Johnson source's electrothermal transfer factor**, `(1 − ℒ)/(1 + ℒ)`.

Under voltage bias the Johnson EMF `v_n` does **not** merely add to the output current: it also
perturbs the dissipated Joule power (`P = (V+v_n)²/R`, so `∂P/∂v_n = 2·I₀`), which drives the
thermal circuit and feeds back through `dI/dT`. Eliminating `δT` from the coupled pair

    δI   = v_n/R + (dI/dT)·δT
    C·δṪ = 2·I₀·v_n − G_eff·δT        (steady state: δT = 2·I₀·v_n/G_eff)

gives `δI/v_n = (1/R)·(1 − ℒ)/(1 + ℒ)` (`johnson_transfer_eq`, derived below rather than
asserted). Sanity: at `ℒ = 0` the factor is `1` (no feedback), and the strong-feedback limit
recovers the standard `NEP_J² → 4·k_B·T·P_J`. -/
noncomputable def johnsonTransfer (m : ETFModel) : ℝ :=
  (1 - m.loopGain) / (1 + m.loopGain)

/-- **Johnson NEP, referred to input power through the ETF-corrected responsivity, *with* the
electrothermal transfer of the noise source itself.**

    NEP_J = √(4·k_B·T/R) · |(1−ℒ)/(1+ℒ)| / |R_etf|

Two distinct ETF effects are present and both are needed — omitting either is a first-order error
in the wave whose entire subject is electrothermal feedback:

* the **responsivity** is the ETF-corrected `responsivityETF`, never `responsivityBare`;
* the **source** couples to the thermal circuit through `johnsonTransfer`, derived in
  `johnson_transfer_eq`.

Their net effect against an ETF-unaware budget is a single factor `|1 − ℒ|`, quantified in
`johnsonNEP_eq_abs_one_sub_loopGain_mul_naive`.

The phonon channel needs no analogue: thermal-fluctuation noise enters the heat balance at exactly
the point the signal does, so it is unchanged when input-referred. That asymmetry is the physics,
and it is why only this channel carries a transfer factor. -/
noncomputable def johnsonNEP (m : ETFModel) (kB T : ℝ) : ℝ :=
  nepOfPSD (m.johnsonCurrentPSD kB T) * |m.johnsonTransfer| / |m.responsivityETF|

/-- **The Johnson current PSD is the repo-canonical Johnson–Nyquist declaration**, at the
*electrical* conductance `1/R` — a genuine citation with matching units, unlike a rearrangement
that would hold for any product. -/
theorem johnsonCurrentPSD_eq_johnsonNyquist (m : ETFModel) (kB T : ℝ) (hR : m.R ≠ 0) :
    m.johnsonCurrentPSD kB T = GrapheneNoiseFormula.johnsonNyquistPSD (kB * T) (1 / m.R) := by
  unfold johnsonCurrentPSD GrapheneNoiseFormula.johnsonNyquistPSD
  field_simp

/-- **The Johnson current PSD is positive at any physical bias point** — the counterpart of
`phononPSD_pos`, and the fact every consumer of the Johnson channel actually needs. Shipped as a
matched pair with the degenerate-branch disclosure below so the two branches are visible together
rather than only the flattering one. -/
theorem johnsonCurrentPSD_pos (m : ETFModel) {kB T : ℝ} (hkB : 0 < kB) (hT : 0 < T)
    (hR : 0 < m.R) : 0 < m.johnsonCurrentPSD kB T := by
  unfold johnsonCurrentPSD
  positivity

/-- **The `R = 0` branch is junk, and it is junk in the OPTIMISTIC direction** — disclosed, because
an undisclosed optimistic branch is the dangerous kind.

At `R = 0` Lean's total division makes `johnsonCurrentPSD = 4·k_B·T/0 = 0`: a **noise-free**
Johnson channel. Physically there is no resistive bias point at `R = 0` (the voltage-biased Joule
power `V²/R` is undefined there, exactly as Wave 1's `loopGain_R_hypothesis_load_bearing`
records), so the `0` is an artefact — but unlike a junk value that merely blocks a conclusion,
this one *manufactures* a favourable one: `phononLimited_R_hypothesis_load_bearing` shows the
resulting model is certified phonon-limited by this file's own screen.

Every statement that reads physics into the Johnson channel must therefore carry `0 < R`. -/
theorem johnsonCurrentPSD_of_R_eq_zero (m : ETFModel) (kB T : ℝ) (hR : m.R = 0) :
    m.johnsonCurrentPSD kB T = 0 := by
  unfold johnsonCurrentPSD
  rw [hR, div_zero]

/-- **The transfer factor, derived from the coupled small-signal equations.**

Given the current response `δI = v_n/R + (dI/dT)·δT` and the steady-state thermal response to the
Johnson-driven Joule perturbation `δT = 2·I₀·v_n/G_eff`, the net current-per-EMF is
`(1/R)·(1 − ℒ)/(1 + ℒ)`. Stated as the identity between the composed expression and
`johnsonTransfer/R`, so the definition above is *derived* rather than posited. -/
theorem johnson_transfer_eq (m : ETFModel) (hR : m.R ≠ 0) (hG : m.G ≠ 0)
    (hL : 1 + m.loopGain ≠ 0) :
    1 / m.R + m.currentTempSlope * (2 * (m.V / m.R) / m.effectiveConductance)
      = m.johnsonTransfer / m.R := by
  unfold johnsonTransfer currentTempSlope effectiveConductance loopGain
  have hRsq : m.R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  -- `1 + ℒ = (R²G + V²·dRdT)/(R²G)`, so the cleared denominator is nonzero
  have hD : m.V ^ 2 * m.dRdT + m.R ^ 2 * m.G ≠ 0 := by
    intro h
    apply hL
    unfold loopGain
    field_simp
    linarith
  have hGL : m.G * (1 + m.V ^ 2 * m.dRdT / (m.R ^ 2 * m.G)) ≠ 0 := by
    intro h
    apply hL
    unfold loopGain
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hG
    · linarith
  have hDinv : (m.V ^ 2 * m.dRdT + m.R ^ 2 * m.G)
      * (m.V ^ 2 * m.dRdT + m.R ^ 2 * m.G)⁻¹ = 1 := mul_inv_cancel₀ hD
  field_simp
  linear_combination -hDinv

/-- **The naive Johnson budget** — bare responsivity, and no electrothermal transfer on the noise
source. This is what a budget written without ETF awareness computes. -/
noncomputable def johnsonNEPNaive (m : ETFModel) (kB T : ℝ) : ℝ :=
  nepOfPSD (m.johnsonCurrentPSD kB T) / |m.responsivityBare|

/-- **The two Johnson budgets differ by exactly the factor `|1 − ℒ|`.**

    NEP_J = |1 − ℒ| · NEP_J^naive

**This is an equality, not a direction.** The naive budget understates the true one exactly when
`|1 − ℒ| > 1` — i.e. for `ℒ > 2` or `ℒ < 0` — and *overstates* it otherwise. At `ℒ = 1` the
electrothermal transfer vanishes outright and the true Johnson NEP is `0` while the naive budget
is not (`johnsonNEP_naive_overstates_at_unit_loopGain`). The direction is therefore pinned by a
separate biconditional, `johnsonNEPNaive_lt_johnsonNEP_iff`, under its own hypothesis, exactly as
Wave 2 pins its own transfer with `nep_bare_lt_nep_etf_of_loopGain_pos`. *(This theorem was named
`…_naive_understates_by_one_sub_loopGain` until 2026-07-29; the name asserted a direction the
statement does not carry and which is false on `0 < ℒ < 2`.)*

Two ETF effects partially cancel, and the surviving factor is `|1 − ℒ|`, **not** `|1 + ℒ|`:
the bare responsivity overstates the response by `(1 + ℒ)`, which alone would understate NEP by
that factor, but the Johnson source's own thermal feedback contributes `|(1−ℒ)/(1+ℒ)|`, and the
`(1+ℒ)` cancels. At the published `ℒ = 3` bias point the naive budget is therefore a factor of
**2** low — not 4.

*(Corrected 2026-07-29 after adversarial review: the first version of this theorem omitted the
source's thermal feedback entirely and claimed `|1+ℒ|`. The omission was a first-order error in
the wave whose subject is electrothermal feedback; it was built out, not disclosed around.)*

**Why magnitudes here are correct, and what they still cannot do.** Wave 2's
`responsivity_magnitudeOnly_loses_stability_information` declares the magnitude-only reading of
the *responsivity correction* unsound. That verdict does not transfer to this statement, and the
distinction is not a matter of taste: a **noise density is intrinsically non-negative** (6EB fixes
`nepOfPSD S = √S ≥ 0`), so `|·|` is the only well-typed object on both sides here — a signed
"NEP" is not a noise density in any convention. What *does* transfer is the warning attached to
it: this correction factor **carries no stability information whatever**, and
`johnsonNEP_correction_magnitude_loses_stability_information` proves it by exhibiting two bias
points with the identical factor `|1 − ℒ| = 2` on **opposite sides** of Wave 1's dichotomy. A
consumer that corrects a Johnson budget by this factor has therefore learned nothing about
whether the operating point is stable, and must pair it with `etf_stable_iff`. *(Wave-3 discharge
of the phase's Definition-of-Done guardrail (b), added 2026-07-29.)*

**Hypotheses are minimal.** Only `1 + ℒ ≠ 0` is carried — a `G ≠ 0` binder was dropped along with
the one in `responsivity_etf_correction`, since at `G = 0` both NEPs collapse to Lean's
total-division `0` and the identity holds as a junk coincidence
(`Electrothermal.ETFModel.responsivity_of_G_eq_zero`).

Consumes `responsivity_etf_correction`, so this is a computation across the wave boundary. -/
theorem johnsonNEP_eq_abs_one_sub_loopGain_mul_naive (m : ETFModel) (kB T : ℝ)
    (hL : 1 + m.loopGain ≠ 0) :
    m.johnsonNEP kB T = |1 - m.loopGain| * m.johnsonNEPNaive kB T := by
  unfold johnsonNEP johnsonNEPNaive johnsonTransfer
  rw [responsivity_etf_correction m hL, abs_mul, abs_div]
  have hL' : |1 + m.loopGain| ≠ 0 := abs_ne_zero.mpr hL
  field_simp

/-- **The direction of the Johnson-budget error, pinned — and its exact boundary.**

The naive budget is strictly below the true one **iff** `|1 − ℒ| > 1`:

    NEP_J^naive < NEP_J   ↔   1 < |1 − ℒ|.

This is the Wave-3 analogue of Wave 2's `nep_bare_lt_nep_etf_of_loopGain_pos`, and it is stated as
a biconditional rather than a one-way implication because the boundary is the falsifiable content:
`|1 − ℒ| > 1` cuts the bias line into `ℒ < 0` and `ℒ > 2` (understated) versus `0 ≤ ℒ ≤ 2`
(overstated, or exact at `ℒ ∈ {0, 2}`). A budget on the `0 < ℒ < 2` branch that "corrects" its
Johnson channel upward has moved *away* from the truth.

The positivity hypothesis is on the naive budget itself rather than on its ingredients, because
that is precisely what the ordering needs and it keeps the statement free of `R`/`G`/`kB`/`T` sign
bookkeeping. -/
theorem johnsonNEPNaive_lt_johnsonNEP_iff (m : ETFModel) (kB T : ℝ)
    (hL : 1 + m.loopGain ≠ 0) (hpos : 0 < m.johnsonNEPNaive kB T) :
    m.johnsonNEPNaive kB T < m.johnsonNEP kB T ↔ 1 < |1 - m.loopGain| := by
  rw [johnsonNEP_eq_abs_one_sub_loopGain_mul_naive m kB T hL]
  exact lt_mul_iff_one_lt_left hpos

/-- **At `ℒ = 1` the naive Johnson budget OVERSTATES — the falsifier for the old name.**

At the bias point `C = G = R = V = dR/dT = 1` the loop gain is exactly `1`, so the electrothermal
transfer `(1 − ℒ)/(1 + ℒ)` vanishes and the true Johnson NEP is `0`, while the naive budget reads
`2` (at `kB = T = 1`). So the naive budget is not merely a factor low — on this branch it is
**high**, and the theorem above cannot be read as an "understates" claim.

This is the concrete counterexample behind the 2026-07-29 rename of
`johnsonNEP_eq_abs_one_sub_loopGain_mul_naive`. -/
theorem johnsonNEP_naive_overstates_at_unit_loopGain :
    (⟨1, 1, 1, 1, 1⟩ : ETFModel).loopGain = 1 ∧
      (⟨1, 1, 1, 1, 1⟩ : ETFModel).johnsonNEP 1 1 = 0 ∧
      (⟨1, 1, 1, 1, 1⟩ : ETFModel).johnsonNEPNaive 1 1 = 2 := by
  norm_num [ETFModel.loopGain, ETFModel.johnsonNEP, ETFModel.johnsonNEPNaive,
    ETFModel.johnsonTransfer, ETFModel.johnsonCurrentPSD, ETFModel.responsivityETF,
    ETFModel.responsivityBare, ETFModel.currentTempSlope, ETFModel.effectiveConductance,
    Detection.nepOfPSD]

/-- Johnson-channel witness on the **relaxing** side, `ℒ = +5`: `1 + ℒ = 6 ≠ 0`, so the Johnson
correction identity applies, and `|1 − ℒ| = 4`.

Wave 1's published witnesses cannot serve here. The equal-factor condition `|1 − a| = |1 − b|`
with `a ≠ b` forces `a + b = 2`, so pairing `speedupWitness` (`ℒ = 3`) across the dichotomy forces
`ℒ = −1` — precisely the marginal point where `1 + ℒ = 0` and the correction identity is empty.
Hence this pair. -/
noncomputable def johnsonQuietWitness : ETFModel := ⟨1, 1, 1, 1, 5⟩

/-- Johnson-channel witness on the **divergent** side, `ℒ = −3`: `1 + ℒ = −2 ≠ 0`, and
`|1 − ℒ| = 4` — the same correction factor as `johnsonQuietWitness`, on the other side of
`etf_stable_iff`. -/
noncomputable def johnsonDivergentWitness : ETFModel := ⟨1, 1, 1, 1, -3⟩

theorem johnsonQuietWitness_loopGain : johnsonQuietWitness.loopGain = 5 := by
  unfold ETFModel.loopGain johnsonQuietWitness; norm_num

theorem johnsonDivergentWitness_loopGain : johnsonDivergentWitness.loopGain = -3 := by
  unfold ETFModel.loopGain johnsonDivergentWitness; norm_num

/-- **The `|1 − ℒ|` Johnson correction carries NO stability information** — the Wave-3 analogue of
Wave 2's `responsivity_magnitudeOnly_loses_stability_information`, and the reason the magnitude
form above must never be read as a certificate.

Two bias points share the identical correction factor `|1 − ℒ| = 4` while sitting on **opposite
sides** of Wave 1's dichotomy: `johnsonQuietWitness` (`ℒ = 5`, every perturbation decays) and
`johnsonDivergentWitness` (`ℒ = −3`, `PerturbationsDecay` fails). So a budget that has applied the
factor `4` to its Johnson channel has learned nothing about which side it is on, and in particular
cannot rule out a non-relaxing operating point.

**Both witnesses satisfy `1 + ℒ ≠ 0`, and the theorem says so.** That conjunct is not decoration:
without it the pair would exhibit the factor at a point where
`johnsonNEP_eq_abs_one_sub_loopGain_mul_naive` does not apply, and `|1 − ℒ|` there would be the
value of an expression rather than *the correction factor* — which is exactly the defect this
statement had until 2026-07-29, when it used `marginalWitness` (`ℒ = −1`, where `1 + ℒ = 0` and
the correction identity has no content). The pair is in fact **forced**: `|1 − a| = |1 − b|` with
`a ≠ b` requires `a + b = 2`, so a stable/divergent pair with `b < −1` needs `a > 3`; `(5, −3)` is
the smallest such pair in integers.

This is not the claim that the magnitude is the *wrong object* for a noise density — it is the
right object (see `johnsonNEP_eq_abs_one_sub_loopGain_mul_naive`'s docstring). It is the claim
that the noise correction is **not** a stability screen, so `etf_stable_iff` remains mandatory. -/
theorem johnsonNEP_correction_magnitude_loses_stability_information :
    (1 + johnsonQuietWitness.loopGain ≠ 0 ∧ 1 + johnsonDivergentWitness.loopGain ≠ 0) ∧
      |1 - johnsonQuietWitness.loopGain| = |1 - johnsonDivergentWitness.loopGain| ∧
      johnsonQuietWitness.PerturbationsDecay ∧ ¬ johnsonDivergentWitness.PerturbationsDecay := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [johnsonQuietWitness_loopGain]; norm_num
  · rw [johnsonDivergentWitness_loopGain]; norm_num
  · rw [johnsonQuietWitness_loopGain, johnsonDivergentWitness_loopGain]
    norm_num
  · rw [etf_stable_iff _ (by norm_num [johnsonQuietWitness]) (by norm_num [johnsonQuietWitness]),
      johnsonQuietWitness_loopGain]
    norm_num
  · rw [etf_stable_iff _ (by norm_num [johnsonDivergentWitness])
      (by norm_num [johnsonDivergentWitness]), johnsonDivergentWitness_loopGain]
    norm_num

/-- **The Johnson budget error at the published bias point, as a rational number.** At Wave 1's
`speedupWitness` (`ℒ = 3`) the ETF-unaware Johnson budget is low by exactly a factor of **2** — not
the factor `4` a responsivity-only correction would predict, because the noise source's own
thermal feedback cancels one power of `(1+ℒ)`.

Backs the numeric claim in `johnsonNEP_eq_abs_one_sub_loopGain_mul_naive`'s docstring with a
theorem, in the same style as Wave 2's `speedupWitness_nep_quarter`; falsifiable by arithmetic,
with no floating point anywhere. -/
theorem speedupWitness_johnsonNEP_double (kB T : ℝ) :
    speedupWitness.johnsonNEP kB T = 2 * speedupWitness.johnsonNEPNaive kB T := by
  rw [johnsonNEP_eq_abs_one_sub_loopGain_mul_naive speedupWitness kB T
    (by rw [speedupWitness_loopGain]; norm_num), speedupWitness_loopGain]
  norm_num

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
cannot be dropped).

What this theorem adds over `nep_quadrature_two` is one specific thing, stated without
embellishment: 6EB's `hwhite` for the phonon channel asks for whiteness at the **squared NEP**,
and that precondition is discharged here from `0 < kB`, `0 < T`, `0 < G` — the *physical* binders
— through `phononPSD_pos` and `isWhite_of_thermalFluctuationLimited`, rather than being passed
through as an abstract non-negativity hypothesis. The `IsThermalFluctuationLimited` wrapper is a
naming convenience on top of that (it unfolds to `IsWhiteFilteredVariance` at the phonon PSD) and
is not itself content. *(Claim narrowed 2026-07-29 after adversarial review, which correctly
objected that "a consumer states physics, not spectral algebra" is not earned by an
abbreviation.)* -/
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

/-- **The Johnson NEP is the spectral NEP of the input-referred Johnson PSD.**

    NEP_J = √( S_I · |(1−ℒ)/(1+ℒ)|² / R_etf² )

i.e. referring the Johnson *current* PSD to the input plane through the transfer factor and the
ETF responsivity, and then taking 6EB's `nepOfPSD`, gives exactly `johnsonNEP`. Needs
`0 ≤ S_I` — this is `√(a·b²/c²) = √a·|b|/|c|`, not a definitional unfolding — and it is what lets
the screen below be phrased on **NEPs** in 6EB's own functional rather than on their squares. -/
theorem johnsonNEP_eq_nepOfPSD (m : ETFModel) {kB T : ℝ}
    (hnnJ : 0 ≤ m.johnsonCurrentPSD kB T) :
    m.johnsonNEP kB T
      = nepOfPSD (m.johnsonCurrentPSD kB T * m.johnsonTransfer ^ 2
          / m.responsivityETF ^ 2) := by
  unfold johnsonNEP nepOfPSD
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul hnnJ, Real.sqrt_sq_eq_abs,
    Real.sqrt_sq_eq_abs]

/-- **The phonon-limited screen, as an `iff` on the NEPs** — the analogue of 6EB's
`shotLimited_iff_psd_lt`, and a decision procedure on a budget rather than a one-way heuristic.

A thermal detector is **phonon-limited** exactly when the input-referred Johnson PSD falls below
the phonon PSD. Both sides are in the same one-sided convention, and the Johnson side carries its
transfer factor and responsivity referral explicitly — so this is the comparison a budget table
can be checked against, not a qualitative claim.

**Stated on NEPs, not on NEP².** The earlier NEP² form was a *definitional unfolding*: after
`nepOfPSD` is expanded, `NEP_J² = S_I·tr²/R_etf²` and `NEP_ph² = S_ph` are literally the same
reals as the two sides of the right-hand comparison, so the biconditional held for arbitrary reals
with no `ETFModel` content at all. Comparing the NEPs instead restores the substance — the
`Real.sqrt` monotonicity of `Real.sqrt_lt_sqrt_iff`, exactly as 6EB's `shotLimited_iff_psd_lt`
does. *(Restated 2026-07-29 after adversarial review.)*

Shipped in place of the two `x² ≤ x² + y²` orderings the roadmap's "monotone consequences" would
literally have licensed: those are true of any reals and carry no bolometric content, whereas this
separates the two physical regimes.

**Minimal hypotheses.** Only non-negativity of the Johnson *current* PSD is carried. No
`responsivityETF ≠ 0` binder: at `R_etf = 0` both sides collapse to `0 < phononPSD` identically.
No `0 ≤ phononPSD` binder either (dropped 2026-07-29): if the phonon PSD were negative then
`phononNEP` is Lean's `√(negative) = 0` while the input-referred Johnson PSD is non-negative, so
both sides are false and the equivalence still holds. -/
theorem phononLimited_iff_psd_lt (m : ETFModel) {kB T : ℝ}
    (hnnJ : 0 ≤ m.johnsonCurrentPSD kB T) :
    m.johnsonNEP kB T < m.phononNEP kB T
      ↔ m.johnsonCurrentPSD kB T * m.johnsonTransfer ^ 2 / m.responsivityETF ^ 2
          < m.phononPSD kB T := by
  rw [m.johnsonNEP_eq_nepOfPSD hnnJ]
  unfold phononNEP nepOfPSD
  exact Real.sqrt_lt_sqrt_iff (by positivity)

/-- **The phonon-limited regime is INHABITED** — a concrete bias point at which the screen fires.

Wave 1's published `speedupWitness` (`C=G=R=V=1`, `dR/dT=3`, hence `ℒ = 3`, `R_etf = −3/4`,
`johnsonTransfer = −1/2`) at `k_B = T = 1`: the input-referred Johnson PSD is
`4·(1/4)/(9/16) = 16/9`, comfortably under the phonon PSD `4`. So the detector is
phonon-limited — the irreducible thermal-fluctuation channel dominates.

Without a witness the `iff` above would be an empty decision procedure; 6EB's `shotLimited_witness`
says exactly this about its own crossover screen and is the precedent followed here. Reusing an
already-published Wave-1 bias point rather than minting a convenient new one keeps the claim tied
to a model whose stability verdict is already a theorem. -/
theorem phononLimited_witness :
    speedupWitness.johnsonNEP 1 1 < speedupWitness.phononNEP 1 1 := by
  rw [speedupWitness.phononLimited_iff_psd_lt (by
    unfold johnsonCurrentPSD speedupWitness; norm_num)]
  unfold johnsonCurrentPSD johnsonTransfer phononPSD responsivityETF currentTempSlope
    effectiveConductance loopGain speedupWitness
  norm_num

/-- **The `0 < R` hypothesis is load-bearing for the screen — and dropping it is OPTIMISTIC.**

A model with `R = 0` is certified **phonon-limited** by `phononLimited_iff_psd_lt`, for any
positive phonon PSD, because Lean's total division reports a *vanishing* Johnson PSD
(`johnsonCurrentPSD_of_R_eq_zero`) — a noise-free Johnson channel. The verdict is junk, and it is
junk in the direction that flatters the detector, which is why it is disclosed as a theorem rather
than left implicit.

Same shape as Wave 1's `loopGain_R_hypothesis_load_bearing`, and the reason
`bolometer_nep_floor` and `bolometer_error_floor` are stated over the *phonon* channel's physical
positivity hypotheses rather than over an abstract PSD. -/
theorem phononLimited_R_hypothesis_load_bearing (m : ETFModel) {kB T : ℝ}
    (hR : m.R = 0) (hph : 0 < m.phononPSD kB T) :
    m.johnsonNEP kB T < m.phononNEP kB T := by
  rw [m.phononLimited_iff_psd_lt (by rw [m.johnsonCurrentPSD_of_R_eq_zero kB T hR])]
  rw [m.johnsonCurrentPSD_of_R_eq_zero kB T hR]
  simpa using hph

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
theorem bolometer_error_floor (m : ETFModel) {kB T Tw : ℝ} {Vtot : (ℝ → ℝ) → ℝ}
    {V : Fin 2 → (ℝ → ℝ) → ℝ}
    {s hf : ℝ → ℝ} {μ₀ μ₁ σ t : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G)
    (hindep : IsUncorrelatedAt Finset.univ Vtot V)
    (hphonon : IsThermalFluctuationLimited (V 0) m kB T Tw)
    (hjohnson : IsWhiteFilteredVariance (V 1) (m.johnsonNEP kB T ^ 2) Tw)
    (hTw : 0 ≤ Tw)
    (hadm : IsAdmissibleFilter Tw s hf)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 Tw)
    (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..Tw, hf x * s x) (hσV : σ = Real.sqrt (Vtot hf)) :
    gaussianQ (matchedBudget (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw s / 2)
      ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t) := by
  -- the composed whiteness is DERIVED from the two channels via 6EB's quadrature algebra,
  -- so `IsUncorrelatedAt` — the hypothesis 6EB proved non-droppable — is in the binder list
  have hch : ∀ i, IsWhiteFilteredVariance (V i) (m.bolometerNEP kB T i ^ 2) Tw := by
    intro i
    match i with
    | 0 => exact isWhite_of_thermalFluctuationLimited hphonon (m.phononPSD_pos hkB hT hG).le
    | 1 => exact hjohnson
  have hwhite : IsWhiteFilteredVariance Vtot
      (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw := by
    have := nep_quadrature_add hindep (fun i _ => hch i)
    simpa [Fin.sum_univ_two, bolometerNEP] using this
  exact error_floor_from_budget hwhite (m.bolometer_psd_pos hkB hT hG) hTw hadm hs hσ hμle hμ hσV

/-! ## The irreducible floor: what no detector of this class can beat -/

/-- **The universal thermal-fluctuation floor: any readout whose noise is at least phonon-limited.**

For a readout whose composed input-referred noise is white with one-sided PSD `S₀`, and whose `S₀`
is **at least** the thermal-fluctuation PSD `NEP_ph²` — with *no* assumption about what the
remaining noise is, or whether there is any at all — the average assignment error is at least
`Q(B(NEP_ph²)/2)`, the floor computed from the phonon channel **alone**.

The engine is 6EB's `matchedBudget_antitone_psd`: a smaller PSD yields a *larger* deflection
budget, and `gaussianQ_antitone` turns a larger budget into a *smaller* error floor — so
evaluating the floor at the phonon PSD alone is valid for every detector at or above it, and the
resulting bound mentions no other channel.

This is the statement that makes the thermal-fluctuation channel *irreducible* rather than merely
present: improving, or entirely removing, every other noise source cannot push the error below
this value. `phonon_only_error_floor` below instantiates it at this wave's two-channel bolometer;
the strength of the present form is that it does not need the detector to be that bolometer. -/
theorem phonon_floor_of_psd_ge (m : ETFModel) {kB T Tw S₀ : ℝ} {Vtot : (ℝ → ℝ) → ℝ}
    {s hf : ℝ → ℝ} {μ₀ μ₁ σ t : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G)
    (hwhite : IsWhiteFilteredVariance Vtot S₀ Tw)
    (hge : m.phononNEP kB T ^ 2 ≤ S₀)
    (hTw : 0 ≤ Tw) (hadm : IsAdmissibleFilter Tw s hf)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 Tw)
    (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..Tw, hf x * s x) (hσV : σ = Real.sqrt (Vtot hf)) :
    gaussianQ (matchedBudget (m.phononNEP kB T ^ 2) Tw s / 2)
      ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t) := by
  have hph : 0 < m.phononNEP kB T ^ 2 := by
    rw [m.phononNEP_sq (m.phononPSD_pos hkB hT hG).le]
    exact m.phononPSD_pos hkB hT hG
  have hbud : matchedBudget S₀ Tw s ≤ matchedBudget (m.phononNEP kB T ^ 2) Tw s :=
    matchedBudget_antitone_psd hph hge s
  refine le_trans (gaussianQ_antitone (show matchedBudget S₀ Tw s / 2
    ≤ matchedBudget (m.phononNEP kB T ^ 2) Tw s / 2 by linarith)) ?_
  exact error_floor_from_budget hwhite (lt_of_lt_of_le hph hge) hTw hadm hs hσ hμle hμ hσV

/-- **THE PHASE'S THESIS, AS A THEOREM: even a Johnson-noise-free detector of this class cannot
beat the thermal-fluctuation floor.**

    Q( B(NEP_ph²) / 2 )  ≤  average assignment error

for a thermal detector of the stated linearized class, read out through **any** admissible
single-shot filter and classified by **any** threshold — with the Johnson channel *deleted from
the bound*. It appears in the hypotheses only to build the detector's actual noise; it does not
appear in the conclusion, and the conclusion is unchanged if it vanishes.

The roadmap's Wave-3 "Why" promises that *"no thermal detector of this linearized class beats
this NEP floor at a stated bias point"* becomes a theorem. `bolometer_error_floor` alone does not
deliver that: its budget is the **composed** `NEP_ph² + NEP_J²`, so it is a statement about a
detector that *has* Johnson noise, and a reader could reasonably ask whether a quieter readout
escapes it. This theorem answers that: it does not, because the phonon channel enters the heat
balance at the point the signal does. *(Shipped 2026-07-29; the gap was found by adversarial
review, which observed that the phase's headline claim was prose rather than a declaration.)*

Route: this wave's quadrature composition supplies the whiteness (via `nep_quadrature_add`, so
`IsUncorrelatedAt` stays in the binder list), the trivial ordering `NEP_ph² ≤ NEP_ph² + NEP_J²`
supplies the hypothesis of `phonon_floor_of_psd_ge`, and 6EB's `matchedBudget_antitone_psd`
composed with 6EA's `gaussianQ_antitone` does the rest. Note which ordering it is: the roadmap's
"monotone consequences" `x² ≤ x² + y²` — declined at Wave 3's close as carrying no bolometric
content on its own — turns out to be *exactly* the step that makes the thesis provable once it is
composed with the budget's antitonicity. It is content-free as a theorem and load-bearing as a
lemma; both readings were right. -/
theorem phonon_only_error_floor (m : ETFModel) {kB T Tw : ℝ} {Vtot : (ℝ → ℝ) → ℝ}
    {V : Fin 2 → (ℝ → ℝ) → ℝ}
    {s hf : ℝ → ℝ} {μ₀ μ₁ σ t : ℝ}
    (hkB : 0 < kB) (hT : 0 < T) (hG : 0 < m.G)
    (hindep : IsUncorrelatedAt Finset.univ Vtot V)
    (hphonon : IsThermalFluctuationLimited (V 0) m kB T Tw)
    (hjohnson : IsWhiteFilteredVariance (V 1) (m.johnsonNEP kB T ^ 2) Tw)
    (hTw : 0 ≤ Tw)
    (hadm : IsAdmissibleFilter Tw s hf)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 Tw)
    (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..Tw, hf x * s x) (hσV : σ = Real.sqrt (Vtot hf)) :
    gaussianQ (matchedBudget (m.phononNEP kB T ^ 2) Tw s / 2)
      ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t) := by
  have hch : ∀ i, IsWhiteFilteredVariance (V i) (m.bolometerNEP kB T i ^ 2) Tw := by
    intro i
    match i with
    | 0 => exact isWhite_of_thermalFluctuationLimited hphonon (m.phononPSD_pos hkB hT hG).le
    | 1 => exact hjohnson
  have hwhite : IsWhiteFilteredVariance Vtot
      (m.phononNEP kB T ^ 2 + m.johnsonNEP kB T ^ 2) Tw := by
    have := nep_quadrature_add hindep (fun i _ => hch i)
    simpa [Fin.sum_univ_two, bolometerNEP] using this
  exact m.phonon_floor_of_psd_ge hkB hT hG hwhite
    (by nlinarith [sq_nonneg (m.johnsonNEP kB T)]) hTw hadm hs hσ hμle hμ hσV

end ETFModel

end SKEFTHawking.Electrothermal
