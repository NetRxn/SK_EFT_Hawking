import SKEFTHawking.Detection.FilterFloors

/-!
# Phase 6EB Wave 2 — NEP algebra, responsivity chains, and the SNR composition

**Publication target: bundle D12** (*Kernel-Verified Detector & Readout Metrology*).

Wave 1 (`SKEFTHawking.Detection.FilterFloors`) built the filter layer: the one-sided ENBW of an
interval-supported filter and the single-shot realizability floor `ENBW·T ≥ 1/2`. This file
builds the layer every detector budget is actually *written* in: noise-equivalent power (NEP)
referred to a declared plane, the responsivity chain that carries it to the classified variable,
quadrature composition of independent sources, and the end-to-end SNR — with a ceiling inherited
from the Wave-1 floor.

## Unit contract (Phase 6EB UNKNOWN-3, resolved here)

Following the `SKEFTHawking.GrapheneNoiseFormula` precedent, all quantities are **dimensionless
reals** carrying a **declared** unit contract; dimensions are not modelled repo-wide. The
contract for this file, fixed once:

| symbol | Lean | unit |
|---|---|---|
| one-sided power PSD | `S_P`, `shotPowerPSD` | W²/Hz |
| NEP (input-referred, one-sided) | `nepOfPSD`, `nepOfOutput` | W/√Hz |
| responsivity | `R` | (output unit)/W |
| ENBW | `enbw` (Wave 1) | Hz |
| output noise | `σ` | output unit |

The composition `σ = R · NEP · √ENBW` is then dimensionally closed:
`(out/W) · (W/√Hz) · √Hz = out` (`sigma_eq_responsivity_nep_sqrt_enbw`). A prefactor error in
any single link breaks that closure — which is what makes the contract falsifiable rather than
decorative.

## Convention — ONE-SIDED, and the falsifier targets a MIXED pairing

The one-sided convention is inherited from `GrapheneNoiseFormula`
(`johnsonNyquistPSD = 4·kB_T·σ_Q`, `hawkingNoisePSD` with its leading `2`) through Wave 1's
`enbw`, whose denominator carries the matching factor `2`. `shotPowerPSD E_ph P = 2·E_ph·P`
carries the same leading `2`.

Wave 1 established the sharp constraint on what a convention falsifier can even *say*:

> the product `S₀ · ENBW` is convention-**invariant** — as a physical variance must be — so
> "one-sided versus two-sided" is **unfalsifiable from a variance alone**.

The falsifiers here therefore target a **MIXED** pairing, not a convention as such, and the
distinction is discharged as a matched pair of theorems rather than left as prose:

* `sigma_conventionPair_consistent_invariant` — converting **both** links together
  (`NEP ↦ NEP/√2` with `ENBW ↦ 2·ENBW`) leaves `σ` **exactly unchanged**. So a *consistent*
  convention switch is invisible in `σ`, and any falsifier phrased against it would be vacuous.
* `sigma_conventionMix_eq_sqrt_two_mul` — converting **one** link only (a one-sided NEP paired
  with a two-sided ENBW) multiplies `σ` by exactly `√2`, and
  `sigma_conventionMix_ne` shows the two are then **provably different**, so the mix is a
  detectable error, not a rephrasing.
* `mixedConvention_error_gt_41_percent` / `mixedConvention_error_lt_42_percent` — the same
  discrepancy at a concrete operating point, bracketed by a certified rational enclosure
  (`1.41 < √2 < 1.4143`). The two-sided bracket matters: it says the mix is wrong by **exactly**
  a `√2`, so the size of an observed discrepancy diagnoses the error rather than merely flagging
  one.

Wave 1's `enbw_oneSided_ne_twoSided` supplies the underlying disagreement of the two ENBW
normalizations; this file consumes it as `enbwTwoSided_eq_two_mul_enbw` rather than restating it.

## Two-layer honesty

The *algebra* here is Lean-verified. Every physical modelling assumption is a **declared
hypothesis** appearing in the binder list of every statement that uses it — never smuggled into
a definition and then unfolded:

* `IsWhiteFilteredVariance` (Wave 1) — the source is white with the stated one-sided PSD;
* `IsResponsivityChain` — the readout chain is linear with responsivity `R` (variances scale by
  `R²`);
* `IsUncorrelatedAt` — the members of a finite source family are uncorrelated at the common
  plane, so their variances add. This is the hypothesis behind quadrature addition and it is
  **not** free: `quadrature_uncorrelated_hypothesis_load_bearing` exhibits a fully-correlated
  pair whose true total PSD is `4·S`, whereas the quadrature rule would predict `2·S` — an
  output-noise error of exactly `√2` (`correlated_pair_sigma_eq_sqrt_two_mul`).

## Non-vacuity

* `nep_incident_gt_absorbed` — referring a budget to the incident plane makes it **strictly
  worse** whenever `0 < η < 1`; the direction is pinned, so the reciprocal error is detectable.
  Its `0 < η` hypothesis is non-droppable (`nep_incident_eta_pos_load_bearing`).
* `snrChain_le_window_ceiling` — a genuine end-to-end ceiling: composing with Wave 1's floor,
  **no** admissible single-shot filter can exceed `SNR ≤ P_sig·√(2T)/NEP`. The ceiling is
  **sharp**, attained exactly by the matched boxcar (`snrChain_window_ceiling_attained`), so it
  is the optimal readout's actual performance rather than a lossy bound.
* `snr_doubling_window_gt_41_percent` — a certified rational witness that the SNR strictly
  *improves* when a budget term improves, so the monotonicity family is not vacuous.
* `shotLimited_witness` — a concrete `norm_num` operating point where the shot NEP exceeds the
  Johnson–Nyquist NEP, so the crossover screen `shotLimited_iff_psd_lt` is inhabited.

## References

- `docs/roadmaps/Phase6EB_Roadmap.md` — Wave 2 acceptance criteria; UNKNOWN-3.
- `docs/dev-loops/Phase6EB/LAB_NOTEBOOK_INDEX.md` — the Wave-1 decision that the falsifier must
  target the mixed pairing.
- `SKEFTHawking.Detection.FilterFloors` — `enbw`, `IsWhiteFilteredVariance`,
  `variance_eq_psd_mul_enbw`, `enbw_mul_window_ge_half`, `enbw_boxcar`.
- `SKEFTHawking.GrapheneNoiseFormula` — the PSD convention anchor, consumed by
  `nep_thermal_johnsonNyquist` and `shotLimited_witness`.
-/

namespace SKEFTHawking.Detection

open MeasureTheory

/-! ## Definitions -/

/-- **NEP from a one-sided input-referred power PSD.** `NEP = √S_P`, i.e. the amplitude spectral
density of the input-referred power fluctuation: `[W/√Hz] = √([W²/Hz])`.

The defining property is carried by `nepOfPSD_sq` (`NEP² = S_P`), not by this definition's
`rfl`. -/
noncomputable def nepOfPSD (S_P : ℝ) : ℝ := √S_P

/-- **NEP defined operationally, input-referred.** Given the output noise `σ` (in the classified
variable's units), the chain responsivity `R` (output/W) and the readout's equivalent noise
bandwidth, the input-referred NEP is

    NEP = σ / (R · √ENBW)                                   [W/√Hz]

i.e. the input power density that would produce the observed output noise. This is the
definition the *plane* matters for: `R` must be the responsivity **at the plane the NEP is
referred to** (`nep_incident_absorbed_transfer`).

**Degenerate branch, disclosed.** At `R = 0` (a chain with no signal path) Lean's total division
returns `0` (`nepOfOutput_of_responsivity_eq_zero`); the physically meaningful statements below
carry `0 < R` explicitly. -/
noncomputable def nepOfOutput (sigma R enbwVal : ℝ) : ℝ := sigma / (R * √enbwVal)

/-- **One-sided shot-noise PSD of an optical power signal:** `S_P = 2·E_ph·P`  [W²/Hz], for
photon energy `E_ph` [J] and mean power `P` [W].

The leading `2` is the **one-sided** convention, matching `GrapheneNoiseFormula.hawkingNoisePSD`
and Wave 1's `enbw` normalization; a two-sided convention halves it. Pairing this with a
two-sided ENBW is exactly the detectable mixed-convention error
(`sigma_conventionMix_eq_sqrt_two_mul`). -/
noncomputable def shotPowerPSD (E_ph P : ℝ) : ℝ := 2 * E_ph * P

/-- **End-to-end SNR of the readout chain**: signal output `R·P_sig` over noise output
`R·NEP·√ENBW` (the composition proved in `sigma_eq_responsivity_nep_sqrt_enbw`).

The responsivity is written on **both** numerator and denominator deliberately: it cancels
(`snrChain_independent_of_responsivity`), which is the detector-metrology analogue of
`GrapheneNoiseFormula.snr_independent_of_sigma_Q` — SNR is a property of the *budget*, not of
the gain. -/
noncomputable def snrChain (R P_sig nepVal enbwVal : ℝ) : ℝ :=
  (R * P_sig) / (R * nepVal * √enbwVal)

/-- **Absorbed power** at a detector of absorption (quantum) efficiency `η` under incident
power: `P_abs = η · P_inc`. The single physical input from which the responsivity dual
`R_inc = η · R_abs` is *derived* (`responsivity_incident_eq`) rather than assumed. -/
def absorbedPower (η P_inc : ℝ) : ℝ := η * P_inc

/-- **Chain linearity, declared as an explicit hypothesis.** The readout chain is linear with
responsivity `R`: an input-referred fluctuation is carried to the output with amplitude gain
`R`, hence variance gain `R²`. `Vin` is the input-referred output-variance functional (as in
Wave 1's `IsWhiteFilteredVariance`), `Vout` the same quantity at the output plane.

Carried as a `Prop` parameter for the same reason Wave 1 carries whiteness that way: the repo
models no stochastic processes, and chain linearity is a *modelling assumption* about a physical
instrument. It appears in the binder list of every theorem that uses it. -/
def IsResponsivityChain (Vout Vin : (ℝ → ℝ) → ℝ) (R : ℝ) : Prop :=
  ∀ h, Vout h = R ^ 2 * Vin h

/-- **Uncorrelatedness of a finite source family at a common plane, declared as an explicit
hypothesis:** the total output variance is the *sum* of the member variances (all cross-terms
vanish).

This is the entire content of "independent sources add in quadrature", and it is a physical
assumption about the sources — never derivable from the algebra. It is stated over a `Finset`
family and consumed by `nep_quadrature_add`; that it cannot be dropped is witnessed by
`quadrature_uncorrelated_hypothesis_load_bearing`, where a fully-correlated pair has total PSD
`4·S` against the quadrature rule's `2·S`. -/
def IsUncorrelatedAt {ι : Type*} (s : Finset ι) (Vtot : (ℝ → ℝ) → ℝ)
    (V : ι → (ℝ → ℝ) → ℝ) : Prop :=
  ∀ h, Vtot h = ∑ i ∈ s, V i h

/-- **The two-sided ENBW normalization** — Wave 1's `enbw` without its one-sided factor `2`.
Defined only so that the mixed-convention falsifiers below can *name* the wrong pairing;
never used as this file's convention. -/
noncomputable def enbwTwoSided (h : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ x in (0:ℝ)..T, h x ^ 2) / (∫ x in (0:ℝ)..T, h x) ^ 2

/-! ## NEP basics and the unit contract -/

/-- **The unit contract, in statement form:** `NEP² = S_P`, i.e. `[W/√Hz]² = [W²/Hz]`. This is
the defining property the roadmap's `nep_def` asks to be carried in a statement rather than only
in a docstring; it is consumed by `shot_nep_formula`, which is what makes the shot NEP's leading
`2` a checkable prefactor instead of a naming choice. Requires `0 ≤ S_P` — a PSD is
non-negative. -/
theorem nepOfPSD_sq {S_P : ℝ} (hS : 0 ≤ S_P) : nepOfPSD S_P ^ 2 = S_P := by
  unfold nepOfPSD
  exact Real.sq_sqrt hS

/-- **The degenerate branch, disclosed.** A chain of zero responsivity has no signal path, so
the input-referred NEP is undefined; Lean's total division returns `0`. Stated so consumers
cannot mistake the junk value for a physical noise density. -/
theorem nepOfOutput_of_responsivity_eq_zero (sigma enbwVal : ℝ) :
    nepOfOutput sigma 0 enbwVal = 0 := by
  unfold nepOfOutput; simp

/-! ## Plane transfer: incident versus absorbed -/

/-- **The responsivity dual, DERIVED from the absorption relation.** A detector responds to the
power it *absorbs*, with responsivity `R_abs`; under incident power `P_inc` it absorbs
`η · P_inc`, so the output per **incident** watt is

    R_inc = (R_abs · P_abs) / P_inc = η · R_abs.

Stated as a derivation (from `absorbedPower`) rather than an assumption, so the `η` in
`nep_incident_absorbed_transfer` traces to the physical absorption relation. -/
theorem responsivity_incident_eq {R_abs η P_inc : ℝ} (hP : P_inc ≠ 0) :
    R_abs * absorbedPower η P_inc / P_inc = η * R_abs := by
  unfold absorbedPower
  field_simp

/-- **Plane transfer of NEP:** `NEP_inc = NEP_abs / η`.

The same physical output noise `σ`, referred through the incident-plane responsivity
`R_inc = η·R_abs` (`responsivity_incident_eq`) instead of the absorbed-plane `R_abs`, yields an
NEP larger by `1/η`.

The incident-plane responsivity is **not** posited as `η·R_abs`: it is written as the measured
output-per-incident-watt `R_abs·P_abs/P_inc` and reduced by `responsivity_incident_eq`, so the
`η` in the conclusion traces to the absorption relation `P_abs = η·P_inc` rather than to a
definition.

**Honesty note on the hypotheses.** Once the responsivity dual is in hand the remaining step is
*unconditional* in Lean: at `η = 0` both sides collapse to the junk value `0` of total division,
so `0 < η` is **not** load-bearing here and is deliberately not claimed to be. The physical
content — that incident referencing is strictly *worse* — is carried by
`nep_incident_gt_absorbed`, and it is **there** that `0 < η` is genuinely non-droppable
(`nep_incident_eta_pos_load_bearing`). -/
theorem nep_incident_absorbed_transfer {sigma R_abs η P_inc enbwVal : ℝ} (hP : P_inc ≠ 0) :
    nepOfOutput sigma (R_abs * absorbedPower η P_inc / P_inc) enbwVal
      = nepOfOutput sigma R_abs enbwVal / η := by
  rw [responsivity_incident_eq hP]
  unfold nepOfOutput
  rw [div_div]
  ring_nf

/-- **Referring a budget to the incident plane is strictly worse.** For any sub-unit absorption
efficiency `0 < η < 1`, the incident-plane NEP strictly exceeds the absorbed-plane NEP.

This is the direction-pinned, falsifiable half of the plane-transfer algebra: the ubiquitous
budget error of quoting an absorbed-plane NEP as if it were incident-plane understates the noise
by `1/η`, and the reciprocal error (`×η` instead of `/η`) would *reverse* this inequality. -/
theorem nep_incident_gt_absorbed {sigma R_abs η enbwVal : ℝ} (hσ : 0 < sigma) (hR : 0 < R_abs)
    (he : 0 < enbwVal) (hη : 0 < η) (hη1 : η < 1) :
    nepOfOutput sigma R_abs enbwVal < nepOfOutput sigma (η * R_abs) enbwVal := by
  unfold nepOfOutput
  have hs : 0 < √enbwVal := Real.sqrt_pos.mpr he
  have h1 : 0 < η * R_abs * √enbwVal := by positivity
  have h2 : η * R_abs * √enbwVal < R_abs * √enbwVal := by nlinarith [mul_pos hR hs]
  exact div_lt_div_of_pos_left hσ h1 h2

/-- **The `0 < η` hypothesis of `nep_incident_gt_absorbed` CANNOT be dropped.** At `η = 0` every
other hypothesis holds (`σ = R_abs = ENBW = 1`) and the conclusion **fails**: the incident-plane
NEP collapses to the junk value `0` (`nepOfOutput_of_responsivity_eq_zero`), which is not
strictly greater than the absorbed-plane NEP.

Physically a detector that absorbs nothing has no incident-referred figure of merit at all —
the same shape as Wave 1's `enbw_dcGain_hypothesis_load_bearing`. -/
theorem nep_incident_eta_pos_load_bearing :
    ¬ nepOfOutput 1 1 1 < nepOfOutput 1 (0 * 1) 1 := by
  unfold nepOfOutput
  norm_num

/-- **Quantitative plane transfer at a stated operating point:** a detector absorbing half the
incident power has exactly **twice** the incident-plane NEP.

A genuine instance of `nep_incident_absorbed_transfer` — the responsivity is written in the same
measured `R_abs·P_abs/P_inc` form and the proof *calls* the transfer theorem — so the `1/η`
factor becomes a number a reader can check rather than a symbol. -/
theorem nep_halfEfficiency_doubles :
    nepOfOutput 1 (1 * absorbedPower (1 / 2) 1 / 1) 1 = 2 * nepOfOutput 1 1 1 := by
  rw [nep_incident_absorbed_transfer one_ne_zero]
  unfold nepOfOutput
  norm_num

/-! ## The composition `σ = R · NEP · √ENBW` -/

/-- **THE NOISE COMPOSITION — `σ = R · NEP · √ENBW`.**

For a source that is white with one-sided input-referred PSD `NEP²` (`hwhite`), read out through
a linear chain of responsivity `R` (`hchain`) and a filter `h` of non-zero DC gain (`hDC`), the
DC-normalized output noise is exactly

    σ = R · NEP · √ENBW(h).

Both physical assumptions are **explicit hypotheses**, per the roadmap's Wave-2 AC: whiteness
via Wave 1's `IsWhiteFilteredVariance`, chain linearity via `IsResponsivityChain`. The proof
**calls** Wave 1's `variance_eq_psd_mul_enbw`, so this is a genuine cross-wave bridge rather
than a docstring reference.

Dimensionally the statement closes the unit contract: `(out/W)·(W/√Hz)·√Hz = out`. -/
theorem sigma_eq_responsivity_nep_sqrt_enbw {Vin Vout : (ℝ → ℝ) → ℝ} {R nepVal T : ℝ}
    (hR : 0 ≤ R) (hnep : 0 ≤ nepVal)
    (hchain : IsResponsivityChain Vout Vin R)
    (hwhite : IsWhiteFilteredVariance Vin (nepVal ^ 2) T)
    (h : ℝ → ℝ) (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) :
    √(Vout h / (∫ x in (0:ℝ)..T, h x) ^ 2) = R * nepVal * √(enbw h T) := by
  have hkey : Vout h / (∫ x in (0:ℝ)..T, h x) ^ 2
      = R ^ 2 * (nepVal ^ 2 * enbw h T) := by
    rw [hchain h, mul_div_assoc, variance_eq_psd_mul_enbw hwhite h hDC]
  rw [hkey, Real.sqrt_mul (sq_nonneg R), Real.sqrt_mul (sq_nonneg nepVal),
    Real.sqrt_sq hR, Real.sqrt_sq hnep, mul_assoc]

/-- **The spectral and operational NEP definitions agree.** Inverting the composition: feeding
the observed output noise `σ = R·NEP·√ENBW` back through the operational definition
`nepOfOutput` returns the spectral `NEP` itself — independently of the responsivity, of the
filter, and of the window.

That round trip is the whole reason NEP is a *figure of merit*: it is what remains after the
readout chain and the integration time are divided out. -/
theorem nep_def_operational_eq_spectral {R nepVal enbwVal : ℝ} (hR : R ≠ 0)
    (he : 0 < enbwVal) :
    nepOfOutput (R * nepVal * √enbwVal) R enbwVal = nepVal := by
  unfold nepOfOutput
  have hs : √enbwVal ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr he)
  field_simp

/-! ## Shot-noise-limited NEP -/

/-- **The shot-noise NEP: `NEP_shot = √(2·E_ph·P_abs)`** (one-sided), recovered from the
*actual filtered output noise* of the chain.

Not an evaluation of a definition: the left-hand side is the operationally input-referred NEP
of a shot-noise-limited chain — output noise divided by responsivity and `√ENBW` — and it equals
`√(2·E_ph·P_abs)` **for every** responsivity `R`, **every** admissible filter `h`, and **every**
window `T`. The chain and the readout divide out exactly; what is left is the source.

The leading `2` is the one-sided convention (`shotPowerPSD`), pinned to
`GrapheneNoiseFormula`'s. -/
theorem shot_nep_formula {Vin Vout : (ℝ → ℝ) → ℝ} {R E_ph P_abs T : ℝ}
    (hR : 0 < R) (hE : 0 ≤ E_ph) (hP : 0 ≤ P_abs)
    (hchain : IsResponsivityChain Vout Vin R)
    (hwhite : IsWhiteFilteredVariance Vin (shotPowerPSD E_ph P_abs) T)
    (h : ℝ → ℝ) (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) (he : 0 < enbw h T) :
    nepOfOutput (√(Vout h / (∫ x in (0:ℝ)..T, h x) ^ 2)) R (enbw h T)
      = √(2 * E_ph * P_abs) := by
  have hS : (0:ℝ) ≤ shotPowerPSD E_ph P_abs := by unfold shotPowerPSD; positivity
  have hsq : (√(2 * E_ph * P_abs)) ^ 2 = shotPowerPSD E_ph P_abs := nepOfPSD_sq hS
  have hwhite' : IsWhiteFilteredVariance Vin ((√(2 * E_ph * P_abs)) ^ 2) T := by
    rw [hsq]; exact hwhite
  rw [sigma_eq_responsivity_nep_sqrt_enbw hR.le (Real.sqrt_nonneg _) hchain hwhite' h hDC]
  exact nep_def_operational_eq_spectral (ne_of_gt hR) he

/-- **Input-referred NEP of a Johnson–Nyquist-limited chain.** Referring the repo-canonical
one-sided thermal PSD `GrapheneNoiseFormula.johnsonNyquistPSD kB_T σ_Q = 4·kB_T·σ_Q` (a *current*
PSD, A²/Hz) back through a responsivity `R` (A/W) gives the input-referred power NEP

    NEP_thermal = √(4·kB_T·σ_Q) / R                        [W/√Hz].

A genuine cross-module bridge: the statement **calls** `johnsonNyquistPSD` and the proof calls
`johnsonNyquistPSD_pos`. -/
theorem nep_thermal_johnsonNyquist {kB_T sigma_Q R : ℝ} (hkT : 0 < kB_T) (hsQ : 0 < sigma_Q)
    (hR : 0 < R) :
    nepOfPSD (GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q / R ^ 2)
      = √(4 * kB_T * sigma_Q) / R := by
  have hS : 0 < GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q :=
    GrapheneNoiseFormula.johnsonNyquistPSD_pos kB_T sigma_Q hkT hsQ
  unfold nepOfPSD GrapheneNoiseFormula.johnsonNyquistPSD
  rw [Real.sqrt_div (by unfold GrapheneNoiseFormula.johnsonNyquistPSD at hS; linarith),
    Real.sqrt_sq hR.le]

/-- **The shot-noise-limited screen.** A chain is shot-noise-limited exactly when the shot PSD
exceeds the input-referred thermal PSD — an `iff`, so it is a decision procedure on the budget
and not a one-way heuristic. Both sides are stated in the same (one-sided) convention. -/
theorem shotLimited_iff_psd_lt {E_ph P_abs kB_T sigma_Q R : ℝ} (hkT : 0 < kB_T)
    (hsQ : 0 < sigma_Q) (hR : 0 < R) :
    nepOfPSD (GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q / R ^ 2)
        < nepOfPSD (shotPowerPSD E_ph P_abs)
      ↔ GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q / R ^ 2
        < shotPowerPSD E_ph P_abs := by
  have hS : 0 < GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q :=
    GrapheneNoiseFormula.johnsonNyquistPSD_pos kB_T sigma_Q hkT hsQ
  have hpos : 0 ≤ GrapheneNoiseFormula.johnsonNyquistPSD kB_T sigma_Q / R ^ 2 := by positivity
  unfold nepOfPSD
  exact Real.sqrt_lt_sqrt_iff hpos

/-- **The crossover screen is inhabited** — a concrete operating point where the chain *is*
shot-noise-limited: `kB_T·σ_Q = 1`, `R = 1` gives a thermal PSD of `4`, while `E_ph = 1`,
`P_abs = 3` gives a shot PSD of `6 > 4`. Without a witness the `iff` above would be an empty
decision procedure. -/
theorem shotLimited_witness :
    nepOfPSD (GrapheneNoiseFormula.johnsonNyquistPSD 1 1 / (1:ℝ) ^ 2)
      < nepOfPSD (shotPowerPSD 1 3) := by
  rw [shotLimited_iff_psd_lt one_pos one_pos one_pos]
  unfold GrapheneNoiseFormula.johnsonNyquistPSD shotPowerPSD
  norm_num

/-! ## Quadrature composition of independent sources -/

/-- **Independent sources add in quadrature at a common plane.** If a finite family of sources
is uncorrelated at the plane (`hindep` — the variances add) and each member is white with
one-sided PSD `NEP i ²` (`hwhite`), then the total is white with PSD `∑ NEP i ²`; equivalently
the total NEP is `√(∑ NEP i ²)` (`nep_total_eq_sqrt_sum_sq`).

The independence assumption is a **hypothesis over the family**, not a property baked into a
definition and then unfolded: `quadrature_uncorrelated_hypothesis_load_bearing` shows the
conclusion is false without it. -/
theorem nep_quadrature_add {ι : Type*} {s : Finset ι} {Vtot : (ℝ → ℝ) → ℝ}
    {V : ι → (ℝ → ℝ) → ℝ} {nep : ι → ℝ} {T : ℝ}
    (hindep : IsUncorrelatedAt s Vtot V)
    (hwhite : ∀ i ∈ s, IsWhiteFilteredVariance (V i) (nep i ^ 2) T) :
    IsWhiteFilteredVariance Vtot (∑ i ∈ s, nep i ^ 2) T := by
  intro h
  rw [hindep h, Finset.sum_congr rfl (fun i hi => hwhite i hi h), ← Finset.sum_mul,
    ← Finset.sum_div]

/-- **The composition with a quadrature-summed budget.** The output noise of the whole family is
`√(∑ NEP i ²) · √ENBW(h)` — i.e. it is `sigma_eq_responsivity_nep_sqrt_enbw` with the single
`NEP` replaced by the family's quadrature sum `√(∑ NEP i ²)`, which is the form a detector
budget table is actually written in. Consumes `nep_quadrature_add` and Wave 1's
`variance_eq_psd_mul_enbw`. -/
theorem nep_total_eq_sqrt_sum_sq {ι : Type*} {s : Finset ι} {Vtot : (ℝ → ℝ) → ℝ}
    {V : ι → (ℝ → ℝ) → ℝ} {nep : ι → ℝ} {T : ℝ}
    (hindep : IsUncorrelatedAt s Vtot V)
    (hwhite : ∀ i ∈ s, IsWhiteFilteredVariance (V i) (nep i ^ 2) T)
    (h : ℝ → ℝ) (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) :
    √(Vtot h / (∫ x in (0:ℝ)..T, h x) ^ 2)
      = √(∑ i ∈ s, nep i ^ 2) * √(enbw h T) := by
  rw [variance_eq_psd_mul_enbw (nep_quadrature_add hindep hwhite) h hDC,
    Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (nep i))]

/-- **Quadrature addition of two sources, explicitly:** the output noise is
`√(NEP₁² + NEP₂²) · √ENBW`. The two-source specialization of `nep_total_eq_sqrt_sum_sq`, in the
shape a two-line budget table uses. -/
theorem nep_quadrature_two {Vtot : (ℝ → ℝ) → ℝ} {V : Fin 2 → (ℝ → ℝ) → ℝ} {nep : Fin 2 → ℝ}
    {T : ℝ}
    (hindep : IsUncorrelatedAt Finset.univ Vtot V)
    (hwhite : ∀ i, IsWhiteFilteredVariance (V i) (nep i ^ 2) T)
    (h : ℝ → ℝ) (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) :
    √(Vtot h / (∫ x in (0:ℝ)..T, h x) ^ 2)
      = √(nep 0 ^ 2 + nep 1 ^ 2) * √(enbw h T) := by
  rw [nep_total_eq_sqrt_sum_sq hindep (fun i _ => hwhite i) h hDC]
  congr 2
  simp [Fin.sum_univ_two]

/-- **The uncorrelatedness hypothesis of `nep_quadrature_add` CANNOT be dropped.**

Two *fully correlated* identical sources add in **amplitude**, not in quadrature: their total
one-sided PSD is `(2a)² = 4·S`, whereas the quadrature rule would predict `S + S = 2·S`. The
witness exhibits exactly that pair — each member white with PSD `S`, the total white with PSD
`4·S` — and shows it is **not** uncorrelated in the sense of `IsUncorrelatedAt`, so the
quadrature theorem does not apply to it. The discrepancy is a factor `√2` in `σ`, the same
magnitude as the mixed-convention error below.

Same shape as Wave 1's `enbw_dcGain_hypothesis_load_bearing`. -/
theorem quadrature_uncorrelated_hypothesis_load_bearing {S : ℝ} (hS : 0 < S) :
    ∃ V Vtot : (ℝ → ℝ) → ℝ,
      IsWhiteFilteredVariance V S 1 ∧
      IsWhiteFilteredVariance Vtot (4 * S) 1 ∧
      ¬ IsUncorrelatedAt (Finset.univ : Finset (Fin 2)) Vtot (fun _ => V) := by
  refine ⟨fun h => S / 2 * ∫ x in (0:ℝ)..1, h x ^ 2,
    fun h => 4 * S / 2 * ∫ x in (0:ℝ)..1, h x ^ 2, fun _ => rfl, fun _ => rfl, ?_⟩
  intro hcon
  have hone : (∫ _x in (0:ℝ)..1, (1:ℝ) ^ 2) = 1 := by norm_num
  have := hcon (fun _ => (1:ℝ))
  simp only [Fin.sum_univ_two, hone, mul_one] at this
  linarith

/-- **How wrong quadrature gets it: exactly `√2`.** A fully-correlated identical pair has total
PSD `4·S` where the quadrature rule predicts `S + S`. Since the output noise goes as the square
root of the PSD at fixed bandwidth (`sigma_eq_responsivity_nep_sqrt_enbw`), the statement below
is exactly the ratio of the two output noises: the truth exceeds the quadrature budget by a
factor `√2` — the same magnitude, and for a structurally identical reason (one link of the
composition off by a factor of two), as the mixed-convention error
`sigma_conventionMix_eq_sqrt_two_mul`.

This is what upgrades `quadrature_uncorrelated_hypothesis_load_bearing` from "the hypothesis is
needed" to "here is the size of the error if you skip it". -/
theorem correlated_pair_sigma_eq_sqrt_two_mul (S : ℝ) :
    √(4 * S) = √2 * √(S + S) := by
  rw [show S + S = 2 * S by ring, show (4:ℝ) * S = 2 * (2 * S) by ring,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (2 * S)]

/-! ## Convention discipline — the falsifier targets a MIXED pairing -/

/-- The two-sided ENBW normalization is exactly twice the one-sided one. Unconditional: at zero
DC gain both sides collapse to Lean's junk `0`. This is the arithmetic behind Wave 1's
`enbw_oneSided_ne_twoSided`, which supplies the *disagreement*; here it supplies the exact
factor consumed by the mixed-pairing falsifiers. -/
theorem enbwTwoSided_eq_two_mul_enbw (h : ℝ → ℝ) (T : ℝ) :
    enbwTwoSided h T = 2 * enbw h T := by
  unfold enbwTwoSided enbw
  rcases eq_or_ne ((∫ x in (0:ℝ)..T, h x) ^ 2) 0 with hz | hz
  · rw [hz]; simp
  · field_simp

/-- **A CONSISTENT convention switch is invisible in `σ` — so it is unfalsifiable.**

Converting **both** links together — the NEP from a one-sided to a two-sided normalization
(`NEP ↦ NEP/√2`) and the ENBW likewise (`ENBW ↦ 2·ENBW`) — leaves the composed output noise
`σ = R·NEP·√ENBW` **exactly unchanged**, as a physical quantity must be.

This theorem exists to make the *next* one non-vacuous: it proves that "which convention" is
undetectable from `σ`, so a falsifier phrased against a convention as such would be empty
(Wave 1's finding for `S₀·ENBW`, lifted to the `σ` composition). Only a **mixed** pairing is
detectable.

Note the invariance needs **no** hypothesis on the bandwidth at all: it is an identity of the
composition, which is exactly why it cannot serve as a falsifier. -/
theorem sigma_conventionPair_consistent_invariant (R nepVal enbwVal : ℝ) :
    R * (nepVal / √2) * √(2 * enbwVal) = R * nepVal * √enbwVal := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hne : √2 ≠ 0 := by positivity
  rw [Real.sqrt_mul h2]
  field_simp

/-- **A MIXED pairing is off by exactly `√2`.**

Pairing a **one-sided** NEP with a **two-sided** ENBW — the single most common factor-of-2 error
in a detector budget — multiplies the reported output noise by exactly `√2`. Unlike a consistent
convention switch (`sigma_conventionPair_consistent_invariant`, invariant) this is a genuine
numerical discrepancy, which is why the falsifier is aimed here. -/
theorem sigma_conventionMix_eq_sqrt_two_mul (R nepVal enbwVal : ℝ) :
    R * nepVal * √(2 * enbwVal) = √2 * (R * nepVal * √enbwVal) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- **The mixed pairing is DETECTABLE**: at any live operating point the mixed-convention `σ`
differs from the correct one. So a statement that silently pairs a one-sided NEP with a
two-sided ENBW is *wrong*, not merely differently phrased — the Phase-6EB guardrail
("a convention-ambiguous theorem is a defect") discharged for the NEP layer. -/
theorem sigma_conventionMix_ne {R nepVal enbwVal : ℝ} (hR : 0 < R) (hnep : 0 < nepVal)
    (he : 0 < enbwVal) :
    R * nepVal * √(2 * enbwVal) ≠ R * nepVal * √enbwVal := by
  rw [sigma_conventionMix_eq_sqrt_two_mul R nepVal enbwVal]
  have hs : 0 < √enbwVal := Real.sqrt_pos.mpr he
  have hprod : 0 < R * nepVal * √enbwVal := by positivity
  have h2 : (1:ℝ) < √2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  nlinarith [hprod, h2]

/-- Certified rational lower bound `√2 > 1.41`, in the `NumericalBounds` rational-enclosure
style (compare `Detection.GaussianThreshold`'s `gaussianQ_two_*_rational`). Consumed by
`mixedConvention_error_gt_41_percent` and `snr_doubling_window_gt_41_percent`. -/
theorem sqrt_two_gt_rational : (1.41 : ℝ) < √2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- Certified rational upper bound `√2 < 1.4143`, closing the enclosure. Consumed by
`mixedConvention_error_lt_42_percent`: without an upper bound the mixed-convention discrepancy
would only be known to be *at least* a factor `1.41`, and the point of the falsifier is that it
is **exactly** a `√2`. -/
theorem sqrt_two_lt_rational : √2 < (1.4143 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- **The mixed-convention error at a concrete operating point, as a number.**

On the matched boxcar of unit window — Wave 1's saturating filter, `ENBW = 1/2` — pairing the
one-sided NEP with the two-sided ENBW (`enbwTwoSided`) overstates the output noise by more than
**41 %**. A hand-checkable magnitude, not a symbolic factor: the certified bound
`√2 > 1.41` (`sqrt_two_gt_rational`) does the work, and the boxcar values come from Wave 1's
`enbw_boxcar` via `enbwTwoSided_eq_two_mul_enbw`. -/
theorem mixedConvention_error_gt_41_percent :
    1.41 * √(enbw (boxcar 1) 1) < √(enbwTwoSided (boxcar 1) 1) := by
  rw [enbwTwoSided_eq_two_mul_enbw, enbw_boxcar 1 one_pos]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hs : 0 < √(1 / (2 * (1:ℝ))) := by
    apply Real.sqrt_pos.mpr; norm_num
  nlinarith [sqrt_two_gt_rational, hs]

/-- **The other side of the bracket: the mixed-convention error is at most 41.43 %.**

Together with `mixedConvention_error_gt_41_percent` this pins the discrepancy inside
`(1.41, 1.4143)` — so the mixed pairing is not merely "wrong by at least something", it is wrong
by **exactly** a factor `√2`, certified by rational enclosure. A reader can therefore use the
size of an observed discrepancy to diagnose *which* error was made: a factor `√2` in `σ` is a
convention mix (or, equivalently sized, a correlated pair treated as independent —
`correlated_pair_sigma_eq_sqrt_two_mul`), whereas other magnitudes are not. -/
theorem mixedConvention_error_lt_42_percent :
    √(enbwTwoSided (boxcar 1) 1) < 1.4143 * √(enbw (boxcar 1) 1) := by
  rw [enbwTwoSided_eq_two_mul_enbw, enbw_boxcar 1 one_pos]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hs : 0 < √(1 / (2 * (1:ℝ))) := by
    apply Real.sqrt_pos.mpr; norm_num
  nlinarith [sqrt_two_lt_rational, hs]

/-! ## End-to-end SNR: cancellation, monotonicity, and the window ceiling -/

/-- **SNR is a property of the budget, not of the gain**: the responsivity cancels between
signal and noise. The detector-metrology analogue of
`GrapheneNoiseFormula.snr_independent_of_sigma_Q`, and the identity every monotonicity statement
below is proved through. -/
theorem snrChain_independent_of_responsivity {R P_sig nepVal enbwVal : ℝ} (hR : R ≠ 0) :
    snrChain R P_sig nepVal enbwVal = P_sig / (nepVal * √enbwVal) := by
  unfold snrChain
  rw [mul_assoc, mul_div_mul_left _ _ hR]

/-- Two chains of different responsivity have the same SNR — the cancellation in the shape of
`GrapheneNoiseFormula.snr_independent_of_sigma_Q`. -/
theorem snrChain_eq_of_responsivity {R R' P_sig nepVal enbwVal : ℝ} (hR : R ≠ 0) (hR' : R' ≠ 0) :
    snrChain R P_sig nepVal enbwVal = snrChain R' P_sig nepVal enbwVal := by
  rw [snrChain_independent_of_responsivity hR, snrChain_independent_of_responsivity hR']

/-- **Budget term 1 — signal power: SNR is strictly INCREASING in `P_sig`.** -/
theorem snrChain_strictMono_signal {R nepVal enbwVal P P' : ℝ} (hR : R ≠ 0) (hnep : 0 < nepVal)
    (he : 0 < enbwVal) (hPP : P < P') :
    snrChain R P nepVal enbwVal < snrChain R P' nepVal enbwVal := by
  rw [snrChain_independent_of_responsivity hR, snrChain_independent_of_responsivity hR]
  have hs : 0 < √enbwVal := Real.sqrt_pos.mpr he
  have hd : 0 < nepVal * √enbwVal := by positivity
  exact div_lt_div_of_pos_right hPP hd

/-- **Budget term 2 — NEP: SNR is strictly DECREASING in the noise-equivalent power.** Signed
separately from the other terms so that "monotone in each budget term" is a checkable claim per
term rather than a summary. -/
theorem snrChain_strictAnti_nep {R P_sig enbwVal n n' : ℝ} (hR : R ≠ 0) (hP : 0 < P_sig)
    (he : 0 < enbwVal) (hn : 0 < n) (hnn : n < n') :
    snrChain R P_sig n' enbwVal < snrChain R P_sig n enbwVal := by
  rw [snrChain_independent_of_responsivity hR, snrChain_independent_of_responsivity hR]
  have hs : 0 < √enbwVal := Real.sqrt_pos.mpr he
  have h1 : 0 < n * √enbwVal := by positivity
  have h2 : n * √enbwVal < n' * √enbwVal := by nlinarith
  exact div_lt_div_of_pos_left hP h1 h2

/-- **Budget term 3 — bandwidth: SNR is strictly DECREASING in the ENBW.** A wider readout
bandwidth admits more noise; combined with Wave 1's floor `ENBW ≥ 1/(2T)` this is what turns the
integration window into the ceiling `snrChain_le_window_ceiling`. -/
theorem snrChain_strictAnti_enbw {R P_sig nepVal e e' : ℝ} (hR : R ≠ 0) (hP : 0 < P_sig)
    (hnep : 0 < nepVal) (he : 0 < e) (hee : e < e') :
    snrChain R P_sig nepVal e' < snrChain R P_sig nepVal e := by
  rw [snrChain_independent_of_responsivity hR, snrChain_independent_of_responsivity hR]
  have hs : 0 < √e := Real.sqrt_pos.mpr he
  have hss : √e < √e' := Real.sqrt_lt_sqrt he.le hee
  have h1 : 0 < nepVal * √e := by positivity
  have h2 : nepVal * √e < nepVal * √e' := by nlinarith
  exact div_lt_div_of_pos_left hP h1 h2

/-- **THE END-TO-END CEILING — no admissible single-shot readout beats `P_sig·√(2T)/NEP`.**

Composing the SNR algebra with Wave 1's realizability floor `ENBW(h)·T ≥ 1/2`: since no filter
integrating over a window of length `T` can have a smaller equivalent noise bandwidth than
`1/(2T)`, **every** admissible filter `h` — interval-integrable with integrable square and
non-zero DC gain — obeys

    SNR ≤ P_sig · √(2T) / NEP.

This is the screen the phase exists to hand to composite ceilings: it bounds the readout by the
integration time alone, independently of the filter's shape and of the responsivity. The proof
**calls** `enbw_mul_window_ge_half`. -/
theorem snrChain_le_window_ceiling {R P_sig nepVal T : ℝ} (h : ℝ → ℝ)
    (hR : R ≠ 0) (hP : 0 ≤ P_sig) (hnep : 0 < nepVal) (hT : 0 < T)
    (hint : IntervalIntegrable h volume 0 T)
    (hsq : IntervalIntegrable (fun x => h x ^ 2) volume 0 T)
    (hDC : (∫ x in (0:ℝ)..T, h x) ≠ 0) :
    snrChain R P_sig nepVal (enbw h T) ≤ P_sig * √(2 * T) / nepVal := by
  have hfloor := enbw_mul_window_ge_half h T hT hint hsq hDC
  have h2T : (0:ℝ) < 2 * T := by positivity
  have hE : 1 / (2 * T) ≤ enbw h T := by
    rw [div_le_iff₀ h2T]
    nlinarith [hfloor]
  have hs2T : 0 < √(2 * T) := Real.sqrt_pos.mpr h2T
  have hval : √(1 / (2 * T)) = 1 / √(2 * T) := by
    rw [Real.sqrt_div' 1 h2T.le, Real.sqrt_one]
  have hsle : √(1 / (2 * T)) ≤ √(enbw h T) := Real.sqrt_le_sqrt hE
  have hb : 1 / √(2 * T) ≤ √(enbw h T) := by rw [hval] at hsle; exact hsle
  have hbpos : 0 < 1 / √(2 * T) := by positivity
  have hstep : P_sig / (nepVal * √(enbw h T)) ≤ P_sig / (nepVal * (1 / √(2 * T))) := by
    gcongr
  have hEq : P_sig / (nepVal * (1 / √(2 * T))) = P_sig * √(2 * T) / nepVal := by
    field_simp
  rw [snrChain_independent_of_responsivity hR, ← hEq]
  exact hstep

/-- **The ceiling is SHARP — the matched boxcar attains it exactly.**

Wave 1's floor is saturated by the matched single-shot integrator (`enbw_boxcar`), so the
end-to-end SNR ceiling `P_sig·√(2T)/NEP` is not a lossy bound but the *exact* performance of the
optimal-bandwidth readout. Without this the ceiling could be true and useless; with it, it is
the readout's actual best case, which is what makes a ceiling a ceiling. -/
theorem snrChain_window_ceiling_attained {R P_sig nepVal T : ℝ} (hR : R ≠ 0) (hnep : nepVal ≠ 0)
    (hT : 0 < T) :
    snrChain R P_sig nepVal (enbw (boxcar T) T) = P_sig * √(2 * T) / nepVal := by
  have h2T : (0:ℝ) < 2 * T := by positivity
  have hs2T : 0 < √(2 * T) := Real.sqrt_pos.mpr h2T
  rw [snrChain_independent_of_responsivity hR, enbw_boxcar T hT,
    Real.sqrt_div' 1 h2T.le, Real.sqrt_one]
  field_simp

/-- **The monotonicity family is not vacuous — a certified improvement witness.**

Doubling the integration window (from `T = 1` to `T = 2`, each read out by its own matched
boxcar, Wave 1's floor-saturating filter) strictly improves the end-to-end SNR by more than
**41 %**: `ENBW` halves from `1/2` to `1/4`, so the SNR grows by `√2 > 1.41`
(`sqrt_two_gt_rational`).

Without a witness of this kind, "monotone in each budget term" would be unfalsifiable — the
inequalities could all hold with equality-in-the-limit and never move a real number. Here the
improvement is a rational bound a reader can check by hand. -/
theorem snr_doubling_window_gt_41_percent :
    1.41 * snrChain 1 1 1 (enbw (boxcar 1) 1) < snrChain 1 1 1 (enbw (boxcar 2) 2) := by
  rw [snrChain_independent_of_responsivity one_ne_zero,
    snrChain_independent_of_responsivity one_ne_zero,
    enbw_boxcar 1 one_pos, enbw_boxcar 2 two_pos]
  have e1 : √(1 / (2 * (1:ℝ))) = 1 / √2 := by
    rw [show (1 / (2 * (1:ℝ))) = 1 / 2 by norm_num, Real.sqrt_div' 1 (by norm_num), Real.sqrt_one]
  have e2 : √(1 / (2 * (2:ℝ))) = 1 / 2 := by
    rw [show (1 / (2 * (2:ℝ))) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [e1, e2]
  have hs0 : (0:ℝ) < √2 := by positivity
  have hv : (1:ℝ) / (1 / √2) = √2 := by field_simp
  have hw : (1:ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
  simp only [one_mul]
  rw [hv, hw]
  nlinarith [sqrt_two_gt_rational, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hs0]

end SKEFTHawking.Detection
