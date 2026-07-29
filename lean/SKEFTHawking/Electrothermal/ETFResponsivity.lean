import SKEFTHawking.Electrothermal.ETFModel
import SKEFTHawking.Detection.NEPAlgebra

/-!
# Responsivity with electrothermal-feedback correction (Phase 6EC, Wave 2)

Wave 1 (`Electrothermal.ETFModel`) fixed the linearized bias-point model and proved the stability
dichotomy. This wave answers the question a detector budget actually asks: **how much signal
current does a watt of absorbed power produce, and by how much does ignoring electrothermal
feedback overstate it?**

The answer is a clean factor: the no-feedback ("bare") responsivity is exactly `(1 + ℒ)` times
the ETF-consistent one. For a positive-loop-gain device that is a *sensitivity overclaim* of the
same factor, and — because NEP is output noise divided by responsivity — a corresponding
*understatement of NEP*. That is the citable repair this wave exists to supply.

## What is derived versus what is defined

The correction identity `responsivityBare = (1+ℒ)·responsivityETF` is near-definitional given the two responsivity
definitions, so the substantive load is deliberately placed in theorems that *derive* those
definitions from calculus rather than positing them (project checklist Q5):

* `hasDerivAt_current` — `dI/dT = −V·(dR/dT)/R²` from `HasDerivAt.div` over an **arbitrary**
  differentiable `R`-vs-`T` curve, mirroring Wave 1's `biasPower_hasDerivAt`. The minus sign is
  derived, not asserted.
* `steadyState_deltaT` — `dT/dP = 1/G_eff` from the driven balance at zero time-derivative, and
  `drivenBalance_eq_effectiveConductance_form` shows the driven balance's coefficient **is**
  Wave 1's linearized slope (it calls `linearizedSlope_eq_neg_effectiveConductance`, so `G_eff`
  enters by computation rather than by naming).
* `hasDerivAt_responsivityETF` / `hasDerivAt_responsivityBare` — the two responsivities as
  genuine **chain-rule** derivatives of current-vs-absorbed-power, `HasDerivAt.comp` of the two
  steps above. This is what makes the definitions honest: they are the derivatives, not labels.

Only then are the correction identity and its magnitude/monotonicity corollaries stated.

## Conventions (inherited, not re-chosen)

* **Signed throughout**, per Wave 1's Guardrail 2. Both responsivities carry the sign of
  `−dR/dT`: a positive-TCR element under voltage bias *loses* current as it heats. Magnitude
  statements are separate corollaries, never the primary form — and
  `responsivity_magnitudeOnly_loses_stability_information` refutes reading the pair through
  absolute values.
* **One-sided PSD / NEP** semantics come from 6EB (`Detection.NEPAlgebra`); this wave transfers
  through `nepOfOutput` and never re-chooses a convention.

## Layout

* **Definitions** — `currentTempSlope`, `responsivityBare`, `responsivityETF`.
* **Derivation** — the three bullets above.
* **The correction** — `responsivity_etf_correction`, magnitude and monotonicity corollaries.
* **NEP transfer (6EB seam)** — `nep_bare_understates_by_one_plus_loopGain` and the input-referred
  transfer, with a rational witness quantifying the budget error at a stated `ℒ`.
* **Non-vacuity** — reuses Wave 1's `speedupWitness` (`ℒ = 3`), so the witness is a statement
  about an already-published bias point rather than a fresh convenient one.
* **Degenerate branches, disclosed** — `responsivityETF_of_effectiveConductance_eq_zero`.

**⚠ Guardrail (inherited).** Every statement is about the *stated linearized model* at a bias
point. Identifying a physical detector with an `ETFModel`, and its absorbed-power response with
these derivatives, is the consumer's declared hypothesis and appears in the binder lists. No
large-signal or nonlinear claim is made anywhere.

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology*.
-/

namespace SKEFTHawking.Electrothermal

open SKEFTHawking.Detection

namespace ETFModel

/-! ## Definitions -/

/-- **Small-signal current response to temperature** at the bias point,

    dI/dT = − V · (dR/dT) / R².

Signed: for a positive-TCR element (`dRdT > 0`) under voltage bias the current *falls* as the
element heats. Derived, not posited — `hasDerivAt_current` produces exactly this number as the
derivative of `T ↦ V/R(T)` for any differentiable `R`-vs-`T` curve.

**Degenerate branch, disclosed.** At `R = 0` Lean's total division returns `0`; every statement
reading physics into it carries `0 < R` (or `R ≠ 0`) explicitly. -/
noncomputable def currentTempSlope (m : ETFModel) : ℝ := -(m.V * m.dRdT) / m.R ^ 2

/-- **The bare (no-feedback) DC power-to-current responsivity**

    R_bare = (dI/dT) / G = − V·(dR/dT) / (R²·G).

"Bare" means the temperature rise per unit absorbed power is taken to be `1/G` — the bath
conductance alone, as if the bias power carried no temperature dependence. This is the form that
appears in budgets when electrothermal feedback is overlooked; it is **not** the physical
responsivity of a biased device (that is `responsivityETF`), and the gap between them is exactly
`responsivity_etf_correction`. -/
noncomputable def responsivityBare (m : ETFModel) : ℝ := m.currentTempSlope / m.G

/-- **The ETF-consistent DC power-to-current responsivity**

    R_etf = (dI/dT) / G_eff = − V·(dR/dT) / (R²·G·(1+ℒ)).

Written through Wave 1's `effectiveConductance`, so the `(1+ℒ)` enters as the conductance the
linearized balance actually relaxes with (`linearizedSlope_eq_neg_effectiveConductance`) rather
than as an inserted correction factor. `hasDerivAt_responsivityETF` derives it as a chain-rule
derivative.

**Degenerate branch, disclosed.** At `G_eff = 0` — the *marginal* bias point `ℒ = −1`, which
Wave 1 shows is a real operating boundary (`etf_marginal_of_loopGain_eq_neg_one`) rather than an
impossible one — Lean's total division returns `0`
(`responsivityETF_of_effectiveConductance_eq_zero`). The physical reading there is a *divergent*
response, so the `0` is junk and every quantitative statement carries `G_eff ≠ 0`. -/
noncomputable def responsivityETF (m : ETFModel) : ℝ :=
  m.currentTempSlope / m.effectiveConductance

/-! ## Derivation: the current slope -/

/-- **`HasDerivAt` form of the current-vs-temperature linearization.**

For any resistance curve `Rf` differentiable at the bias temperature with `Rf T = R ≠ 0`,

    d/dT ( V / Rf(T) ) = − V · (dR/dT) / R².

The exact companion of Wave 1's `biasPower_hasDerivAt` (which does the same for `V²/Rf`), and the
minus sign is likewise *derived* from `HasDerivAt.div` rather than asserted. Stated over an
arbitrary differentiable curve, so it constrains every model with the stated bias-point
derivative — not a chosen functional form. -/
theorem hasDerivAt_current (m : ETFModel) (Rf : ℝ → ℝ) {T : ℝ}
    (hR : HasDerivAt Rf m.dRdT T) (hR₀ : Rf T = m.R) (hne : m.R ≠ 0) :
    HasDerivAt (fun τ => m.V / Rf τ) m.currentTempSlope T := by
  have hd : HasDerivAt (fun τ => m.V / Rf τ)
      ((0 * Rf T - m.V * m.dRdT) / Rf T ^ 2) T :=
    HasDerivAt.fun_div (hasDerivAt_const T m.V) hR (by rw [hR₀]; exact hne)
  rw [hR₀] at hd
  unfold currentTempSlope
  convert hd using 1
  ring

/-! ## Derivation: temperature rise per unit absorbed power -/

/-- **The DC-driven linearized heat balance**, `C·δṪ = P_sig − G_eff·δT`.

Wave 1's `SolvesHeatBalance` with a constant absorbed signal power added. The `−G_eff` coefficient
is not a fresh modelling choice: `drivenBalance_eq_effectiveConductance_form` shows it is exactly
Wave 1's linearized right-hand-side slope. -/
def SolvesDrivenBalance (m : ETFModel) (P_sig : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt f ((P_sig - m.effectiveConductance * f t) / m.C) t

/-- **The driven balance's coefficient is Wave 1's linearized slope.**

    P_sig + (d/dT(V²/R(T)) − G)·δT  =  P_sig − G_eff·δT

Content is the *call* to `linearizedSlope_eq_neg_effectiveConductance`: it certifies that
`SolvesDrivenBalance` is the physical linearization (bias power + signal − bath loss) rewritten,
not an independently-postulated ODE. Without this, `G_eff` would enter Wave 2 by naming
convention. -/
theorem drivenBalance_eq_effectiveConductance_form (m : ETFModel) (Rf : ℝ → ℝ) {T δT P_sig : ℝ}
    (hR : HasDerivAt Rf m.dRdT T) (hR₀ : Rf T = m.R) (hRne : m.R ≠ 0) (hGne : m.G ≠ 0) :
    P_sig + (deriv (fun τ => m.V ^ 2 / Rf τ) T - m.G) * δT
      = P_sig - m.effectiveConductance * δT := by
  rw [linearizedSlope_eq_neg_effectiveConductance m Rf hR hR₀ hRne hGne]
  ring

/-- **Steady-state temperature rise per unit absorbed power: `δT = P_sig / G_eff`.**

At a steady state of the driven balance (vanishing time derivative), the temperature offset is
the absorbed power divided by the *effective* conductance — not by `G`. This is the entire
physical origin of the `(1+ℒ)` in `responsivityETF`, and it is derived from the ODE rather than
assumed.

Both `hC` and `hGe` are load-bearing: at `C = 0` the balance degenerates (Lean's division makes
the derivative condition vacuous), and at `G_eff = 0` the steady state does not exist. -/
theorem steadyState_deltaT (m : ETFModel) (hC : m.C ≠ 0) (hGe : m.effectiveConductance ≠ 0)
    {P_sig : ℝ} {f : ℝ → ℝ} {t : ℝ}
    (hsol : SolvesDrivenBalance m P_sig f) (hst : deriv f t = 0) :
    f t = P_sig / m.effectiveConductance := by
  have hd := (hsol t).deriv
  rw [hst] at hd
  have hz : P_sig - m.effectiveConductance * f t = 0 := by
    field_simp at hd
    linarith [hd]
  field_simp
  linarith [hz]

/-! ## Derivation: the responsivities as chain-rule derivatives -/

/-- **The ETF responsivity IS the chain-rule derivative of current with respect to absorbed
power.**

Composing the steady-state temperature map `P ↦ T₀ + P/G_eff` (justified by
`steadyState_deltaT`) with the current curve `T ↦ V/Rf(T)` (differentiated by
`hasDerivAt_current`):

    dI/dP |_{P=0} = (dI/dT)·(1/G_eff) = R_etf.

This is what earns `responsivityETF` its name — it is *the derivative*, not a labelled
expression. -/
theorem hasDerivAt_responsivityETF (m : ETFModel) (Rf : ℝ → ℝ) {T₀ : ℝ}
    (hR : HasDerivAt Rf m.dRdT T₀) (hR₀ : Rf T₀ = m.R) (hne : m.R ≠ 0) :
    HasDerivAt (fun P => m.V / Rf (T₀ + P / m.effectiveConductance))
      m.responsivityETF 0 := by
  have hinner : HasDerivAt (fun P : ℝ => T₀ + P / m.effectiveConductance)
      (1 / m.effectiveConductance) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const m.effectiveConductance).const_add T₀)
  have houter := hasDerivAt_current m Rf hR hR₀ hne
  have hcomp := ((by simpa using houter :
    HasDerivAt (fun τ => m.V / Rf τ) m.currentTempSlope _).comp 0 hinner)
  have hval : m.currentTempSlope * (1 / m.effectiveConductance) = m.responsivityETF := by
    unfold responsivityETF; ring
  rw [← hval]
  exact hcomp

/-- **The bare responsivity is the same chain rule with the no-feedback temperature map**
`P ↦ T₀ + P/G`, i.e. with the bias power's temperature dependence discarded. Shipped alongside
`hasDerivAt_responsivityETF` so that the difference between the two responsivities is visibly a
difference of *modelling step*, not of algebra. -/
theorem hasDerivAt_responsivityBare (m : ETFModel) (Rf : ℝ → ℝ) {T₀ : ℝ}
    (hR : HasDerivAt Rf m.dRdT T₀) (hR₀ : Rf T₀ = m.R) (hne : m.R ≠ 0) :
    HasDerivAt (fun P => m.V / Rf (T₀ + P / m.G)) m.responsivityBare 0 := by
  have hinner : HasDerivAt (fun P : ℝ => T₀ + P / m.G) (1 / m.G) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div_const m.G).const_add T₀)
  have houter := hasDerivAt_current m Rf hR hR₀ hne
  have hcomp := ((by simpa using houter :
    HasDerivAt (fun τ => m.V / Rf τ) m.currentTempSlope _).comp 0 hinner)
  have hval : m.currentTempSlope * (1 / m.G) = m.responsivityBare := by
    unfold responsivityBare; ring
  rw [← hval]
  exact hcomp

/-! ## The ETF correction factor -/

/-- **The correction-factor identity:** `responsivityBare = (1 + ℒ)·responsivityETF`.

The wave's headline algebra. Its *content* is not this line — which is short given the two
definitions — but the two derivations above, which establish that the left side is the derivative
under the no-feedback temperature map and the right side the derivative under the physical one.

**`1 + ℒ ≠ 0` is not decoration — the identity is FALSE without it.** At the marginal bias point
`ℒ = −1` we have `G_eff = 0`, so `responsivityETF` collapses to Lean's junk `0`
(`responsivityETF_of_effectiveConductance_eq_zero`) and the right-hand side is `0 · 0 = 0`, while
the left-hand side `−V·(dR/dT)/(R²·G)` is generally nonzero. The failure is witnessed at a
published bias point by `marginalWitness_correction_fails`. No *sign* or stability hypothesis is
needed beyond that: the identity holds on the unstable branch `ℒ < −1` too, where `1 + ℒ < 0`
and the two responsivities have **opposite signs** (`responsivity_opposite_sign_of_unstable`). -/
theorem responsivity_etf_correction (m : ETFModel) (hGne : m.G ≠ 0)
    (hL : 1 + m.loopGain ≠ 0) :
    m.responsivityBare = (1 + m.loopGain) * m.responsivityETF := by
  unfold responsivityBare responsivityETF effectiveConductance
  field_simp

/-- **The bare form overstates the response by exactly `(1+ℒ)` on the stable, positive-feedback
branch.** For `ℒ > 0` and a live signal path (`dI/dT ≠ 0`), the magnitudes are strictly ordered:

    |R_etf| < |R_bare|.

This is the sensitivity overclaim the wave exists to quantify: a budget written with the bare
responsivity credits the device with more amps per watt than the biased device delivers. -/
theorem abs_responsivityETF_lt_abs_responsivityBare (m : ETFModel) (hGne : m.G ≠ 0)
    (hL : 0 < m.loopGain) (hslope : m.currentTempSlope ≠ 0) :
    |m.responsivityETF| < |m.responsivityBare| := by
  have hRetf : m.responsivityETF ≠ 0 := by
    unfold responsivityETF
    exact div_ne_zero hslope (by
      unfold effectiveConductance
      exact mul_ne_zero hGne (by linarith))
  rw [responsivity_etf_correction m hGne (by intro h; linarith [h]), abs_mul,
    abs_of_pos (by linarith : (0:ℝ) < 1 + m.loopGain)]
  have : 0 < |m.responsivityETF| := abs_pos.mpr hRetf
  nlinarith

/-- **On the unstable branch the two responsivities have opposite signs.** For `ℒ < −1` — Wave 1's
divergent regime (`etf_diverges_of_loopGain_lt_neg_one`) — the correction factor `1 + ℒ` is
negative, so `responsivityBare` and `responsivityETF` disagree in *direction*, not merely in magnitude.

This is why the correction may never be applied as an absolute value: `|R_bare| = |1+ℒ|·|R_etf|`
is true but throws away the fact that an unstable bias point inverts the sense of the response.
The magnitude-only reading is refuted in
`responsivity_magnitudeOnly_loses_stability_information`. -/
theorem responsivity_opposite_sign_of_unstable (m : ETFModel) (hGne : m.G ≠ 0)
    (hL : m.loopGain < -1) (hslope : m.currentTempSlope ≠ 0) :
    m.responsivityBare * m.responsivityETF < 0 := by
  have hRetf : m.responsivityETF ≠ 0 := by
    unfold responsivityETF
    exact div_ne_zero hslope (by
      unfold effectiveConductance
      exact mul_ne_zero hGne (by intro h; nlinarith))
  have hneg : 1 + m.loopGain < 0 := by linarith
  rw [responsivity_etf_correction m hGne (by intro h; linarith [h])]
  have hsq : 0 < m.responsivityETF ^ 2 := by positivity
  nlinarith [hsq]

/-! ## The 6EB seam: NEP transfer through the two responsivity forms -/

/-- **Using the bare responsivity understates the input-referred NEP by exactly `(1+ℒ)`.**

NEP is output noise referred to the input by *dividing* by the responsivity
(6EB's `nepOfOutput σ R ENBW = σ/(R·√ENBW)`), so an overstated responsivity produces an
understated NEP — the direction that matters, because it makes a detector look *better* than it
is. Composing with `responsivity_etf_correction`:

    NEP(using R_bare) = NEP(using R_etf) / (1 + ℒ).

This **calls** `Detection.nepOfOutput`, so the seam with 6EB is a computation rather than a
docstring reference. -/
theorem nep_bare_understates_by_one_plus_loopGain (m : ETFModel) (hGne : m.G ≠ 0)
    (hL : 1 + m.loopGain ≠ 0) (sigma enbwVal : ℝ) :
    nepOfOutput sigma m.responsivityBare enbwVal
      = nepOfOutput sigma m.responsivityETF enbwVal / (1 + m.loopGain) := by
  unfold nepOfOutput
  rw [responsivity_etf_correction m hGne hL]
  rcases eq_or_ne (Real.sqrt enbwVal) 0 with he | he
  · rw [he]; simp
  · rcases eq_or_ne m.responsivityETF 0 with hr | hr
    · rw [hr]; simp
    · field_simp

/-! ## Non-vacuity: a rational witness at a published bias point -/

/-- Wave 1's `speedupWitness` (`C=G=R=V=1`, `dRdT=3`) has loop gain `3`. Wave 1 publishes this
witness's time constants and speedup verdict but not its loop gain, so it is computed here. -/
theorem speedupWitness_loopGain : speedupWitness.loopGain = 3 := by
  unfold loopGain speedupWitness
  norm_num

/-- Wave 1's `speedupWitness` (`C=G=R=V=1`, `dRdT=3`) has loop gain `3`, hence correction factor
`4`. Reusing an *already-published* Wave-1 witness rather than minting a convenient new one keeps
the quantitative claim tied to a bias point whose stability verdict is already a theorem. -/
theorem speedupWitness_responsivities :
    speedupWitness.responsivityBare = -3 ∧ speedupWitness.responsivityETF = -3 / 4 := by
  refine ⟨?_, ?_⟩
  · unfold responsivityBare currentTempSlope speedupWitness
    norm_num
  · unfold responsivityETF currentTempSlope effectiveConductance loopGain speedupWitness
    norm_num

/-- **The budget error, as a rational number.** At the published `ℒ = 3` bias point the bare
responsivity is **4×** the physical one, so a NEP budget written with it reports a noise floor
four times *lower* than the device delivers — a 300 % sensitivity overclaim.

Falsifiable as stated, with no floating point anywhere: a measured responsivity agreeing with
`responsivityBare` at this bias point would refute either the linearized model or the
identification of the device with `speedupWitness`. -/
theorem speedupWitness_bare_overstates_fourfold :
    speedupWitness.responsivityBare = 4 * speedupWitness.responsivityETF := by
  obtain ⟨hb, he⟩ := speedupWitness_responsivities
  rw [hb, he]
  norm_num

/-- **The NEP consequence at the published bias point**, stated in 6EB's own functional: the
bare-responsivity NEP is a quarter of the ETF-consistent one, for *every* output noise level and
*every* ENBW. -/
theorem speedupWitness_nep_quarter (sigma enbwVal : ℝ) :
    nepOfOutput sigma speedupWitness.responsivityBare enbwVal
      = nepOfOutput sigma speedupWitness.responsivityETF enbwVal / 4 := by
  have h := nep_bare_understates_by_one_plus_loopGain speedupWitness (by
    unfold speedupWitness; norm_num) (by
    rw [speedupWitness_loopGain]; norm_num) sigma enbwVal
  rw [h, speedupWitness_loopGain]
  norm_num

/-! ## Frequency rolloff (UNKNOWN-1, resolved past the Pareto floor)

6EE consumes only DC forms, which *permitted* deferring this — see the roadmap's UNKNOWN-1
resolution. It is built anyway, by the prescribed route: an explicit sinusoidal steady-state
particular solution verified with `HasDerivAt`, no Fourier machinery and no transfer-function
formalism. -/

/-- **The sinusoidal steady-state temperature response** to absorbed power `P₀·cos(ωt)`:

    δT(t) = P₀ · (G_eff·cos(ωt) + C·ω·sin(ωt)) / (G_eff² + C²ω²).

Written as an explicit real combination of `cos` and `sin` rather than through a complex transfer
function, so the verification (`thermalResponse_solves`) is a `HasDerivAt` computation. At `ω = 0`
it collapses to the DC steady state `P₀/G_eff` of `steadyState_deltaT`. -/
noncomputable def thermalResponse (m : ETFModel) (ω P₀ : ℝ) : ℝ → ℝ := fun t =>
  (P₀ * m.effectiveConductance * Real.cos (ω * t) + P₀ * m.C * ω * Real.sin (ω * t))
    / (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2)

/-- **Amplitude of the sinusoidal steady-state response**, `P₀/√(G_eff² + C²ω²)`. Equal to
`√(a² + b²)` for the `cos`/`sin` coefficients of `thermalResponse`; the single-pole form is
`thermalResponseAmplitude_eq_singlePole`. -/
noncomputable def thermalResponseAmplitude (m : ETFModel) (ω P₀ : ℝ) : ℝ :=
  P₀ / Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2)

/-- **The explicit sinusoidal steady state solves the driven balance**, at every time:

    C · δṪ(t) = P₀·cos(ωt) − G_eff · δT(t).

`HasDerivAt` verification of an explicit solution — the `etf_perturbation_solves` /
`dampedTwoLevel_population_solves_rate` pattern, no ODE-existence machinery. This is the
substantive content of the rolloff: the amplitude formula below is algebra *once this holds*. -/
theorem thermalResponse_solves (m : ETFModel) (hC : m.C ≠ 0) {ω : ℝ} (P₀ : ℝ)
    (hD : m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2 ≠ 0) (t : ℝ) :
    HasDerivAt (m.thermalResponse ω P₀)
      ((P₀ * Real.cos (ω * t) - m.effectiveConductance * m.thermalResponse ω P₀ t) / m.C) t := by
  have harg : HasDerivAt (fun τ : ℝ => ω * τ) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hcos : HasDerivAt (fun τ : ℝ => Real.cos (ω * τ)) (-Real.sin (ω * t) * ω) t :=
    (Real.hasDerivAt_cos (ω * t)).comp t harg
  have hsin : HasDerivAt (fun τ : ℝ => Real.sin (ω * τ)) (Real.cos (ω * t) * ω) t :=
    (Real.hasDerivAt_sin (ω * t)).comp t harg
  have hd : HasDerivAt (m.thermalResponse ω P₀)
      ((P₀ * m.effectiveConductance * (-Real.sin (ω * t) * ω)
          + P₀ * m.C * ω * (Real.cos (ω * t) * ω))
        / (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2)) t := by
    unfold thermalResponse
    exact (((hcos.const_mul (P₀ * m.effectiveConductance)).fun_add
      (hsin.const_mul (P₀ * m.C * ω))).div_const _)
  refine hd.congr_deriv ?_
  unfold thermalResponse
  -- Clear the two denominators by hand: `field_simp` reorders the quadratic denominator so that
  -- `hD` no longer matches it, leaving an uncancelled inverse that `ring` cannot discharge.
  rw [eq_div_iff hC, div_mul_eq_mul_div, div_eq_iff hD, sub_mul,
    mul_assoc m.effectiveConductance, div_mul_cancel₀ _ hD]
  ring

/-- **The single-pole rolloff.** The steady-state amplitude is the DC response divided by the
familiar single-pole factor built from the *effective* time constant:

    amplitude(ω) = (P₀ / G_eff) / √(1 + (ω·τ_eff)²),   τ_eff = C/G_eff.

Note the `τ_eff`, not `τ`: electrothermal feedback moves the pole, which is exactly why Wave 1's
`effectiveTimeConstant` had to exist before this statement could be made. -/
theorem thermalResponseAmplitude_eq_singlePole (m : ETFModel)
    (hGe : 0 < m.effectiveConductance) (ω P₀ : ℝ) :
    m.thermalResponseAmplitude ω P₀
      = (P₀ / m.effectiveConductance) / Real.sqrt (1 + (ω * m.effectiveTimeConstant) ^ 2) := by
  unfold thermalResponseAmplitude effectiveTimeConstant
  have hGne : m.effectiveConductance ≠ 0 := ne_of_gt hGe
  have hrw : 1 + (ω * (m.C / m.effectiveConductance)) ^ 2
      = (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) / m.effectiveConductance ^ 2 := by
    field_simp
  have hsq : Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [hrw, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hGe.le]
  field_simp

/-- **DC limit.** At `ω = 0` the sinusoidal amplitude is the DC steady state of
`steadyState_deltaT`, so the rolloff factor is normalized to `1` at zero frequency rather than to
an arbitrary constant. -/
theorem thermalResponseAmplitude_zero (m : ETFModel) (hGe : 0 < m.effectiveConductance) (P₀ : ℝ) :
    m.thermalResponseAmplitude 0 P₀ = P₀ / m.effectiveConductance := by
  unfold thermalResponseAmplitude
  rw [show m.effectiveConductance ^ 2 + m.C ^ 2 * (0:ℝ) ^ 2 = m.effectiveConductance ^ 2 by ring,
    Real.sqrt_sq hGe.le]

/-- **The rolloff is a genuine rolloff: strictly decreasing in frequency.** For `P₀ > 0` on the
stable branch with nonzero heat capacity, a higher modulation frequency yields a strictly smaller
response. Without this the "single-pole factor" would be compatible with a flat response — this is
the statement that makes the factor bite. -/
theorem thermalResponseAmplitude_strictAnti (m : ETFModel) (hGe : 0 < m.effectiveConductance)
    (hC : m.C ≠ 0) {P₀ : ℝ} (hP : 0 < P₀) {ω ω' : ℝ} (hω : 0 ≤ ω) (hlt : ω < ω') :
    m.thermalResponseAmplitude ω' P₀ < m.thermalResponseAmplitude ω P₀ := by
  unfold thermalResponseAmplitude
  have hCsq : 0 < m.C ^ 2 := by positivity
  have hd : m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2
      < m.effectiveConductance ^ 2 + m.C ^ 2 * ω' ^ 2 := by
    have : ω ^ 2 < ω' ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  exact div_lt_div_of_pos_left hP hpos (Real.sqrt_lt_sqrt (by positivity) hd)

/-- **The AC's `responsivity_frequency_rolloff`.** The *current* response amplitude at modulation
frequency `ω` is the DC ETF responsivity times the single-pole factor:

    |dI/dT| · amplitude(ω) = |R_etf| · P₀ / √(1 + (ω·τ_eff)²).

Stated as an identity between the physically measurable current amplitude (left) and the
budget-facing form (right), so it is a bridge rather than a restatement of a definition.

Carries **no** sign hypothesis on `P₀`: the identity is algebraic and holds for every drive
amplitude, so a `0 ≤ P₀` binder would be dead weight. -/
theorem responsivity_frequency_rolloff (m : ETFModel) (hGe : 0 < m.effectiveConductance)
    (P₀ ω : ℝ) :
    |m.currentTempSlope| * m.thermalResponseAmplitude ω P₀
      = |m.responsivityETF| * P₀ / Real.sqrt (1 + (ω * m.effectiveTimeConstant) ^ 2) := by
  have hGne : m.effectiveConductance ≠ 0 := ne_of_gt hGe
  rw [thermalResponseAmplitude_eq_singlePole m hGe]
  have habs : |m.responsivityETF| = |m.currentTempSlope| / m.effectiveConductance := by
    unfold responsivityETF
    rw [abs_div, abs_of_pos hGe]
  rw [habs]
  field_simp

/-! ## Degenerate branches, disclosed -/

/-- **The marginal bias point is a junk branch, and is disclosed as such.** At `G_eff = 0`
(`ℒ = −1`, Wave 1's `etf_marginal_of_loopGain_eq_neg_one`) the physical response *diverges*, but
Lean's total division reports `0`. Every quantitative statement above therefore carries a
non-vanishing hypothesis rather than relying on this value. -/
theorem responsivityETF_of_effectiveConductance_eq_zero (m : ETFModel)
    (h : m.effectiveConductance = 0) : m.responsivityETF = 0 := by
  unfold responsivityETF
  rw [h, div_zero]

/-- **The magnitude-only reading of the correction is unsound** — the Wave-2 analogue of Wave 1's
`magnitudeOnly_criterion_unsound`, and the reason `responsivity_etf_correction` is stated signed.

Two bias points share the identical magnitude relation `|R_bare| = |1+ℒ|·|R_etf|` while sitting
on **opposite sides** of the stability dichotomy: `speedupWitness` (`ℒ = 3`, stable, responsivities
of the same sign) and `unstableWitness` (`ℒ = −2`, divergent, responsivities of opposite sign).
So `|1+ℒ|` cannot recover the direction of the response, and a budget corrected by magnitude
alone silently accepts a divergent operating point. -/
theorem responsivity_magnitudeOnly_loses_stability_information :
    0 < speedupWitness.responsivityBare * speedupWitness.responsivityETF ∧
      unstableWitness.responsivityBare * unstableWitness.responsivityETF < 0 ∧
      |speedupWitness.responsivityBare|
        = |1 + speedupWitness.loopGain| * |speedupWitness.responsivityETF| ∧
      |unstableWitness.responsivityBare|
        = |1 + unstableWitness.loopGain| * |unstableWitness.responsivityETF| := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hb, he⟩ := speedupWitness_responsivities
    rw [hb, he]; norm_num
  · refine responsivity_opposite_sign_of_unstable unstableWitness (by
      unfold unstableWitness; norm_num) (by rw [unstableWitness_loopGain]; norm_num) ?_
    unfold currentTempSlope unstableWitness
    norm_num
  · rw [responsivity_etf_correction speedupWitness (by unfold speedupWitness; norm_num)
      (by rw [speedupWitness_loopGain]; norm_num), abs_mul]
  · rw [responsivity_etf_correction unstableWitness (by unfold unstableWitness; norm_num)
      (by rw [unstableWitness_loopGain]; norm_num), abs_mul]

/-- **The marginal bias point refutes the unrestricted correction identity.**

At Wave 1's `marginalWitness` (`C=G=R=1`, `V=2`, `dR/dT=−1/4`, hence `ℒ = −1` and `G_eff = 0`)
the identity `responsivityBare = (1+ℒ)·responsivityETF` **fails**: the right-hand side is `0`, while the left-hand
side is `1/2`. This is why `responsivity_etf_correction` carries `1 + ℒ ≠ 0` — the hypothesis is
load-bearing, not defensive, and this theorem is its witness. -/
theorem marginalWitness_correction_fails :
    marginalWitness.responsivityBare
      ≠ (1 + marginalWitness.loopGain) * marginalWitness.responsivityETF := by
  rw [marginalWitness_loopGain]
  have hb : marginalWitness.responsivityBare = 1 / 2 := by
    unfold responsivityBare currentTempSlope marginalWitness
    norm_num
  rw [hb]
  norm_num

end ETFModel

end SKEFTHawking.Electrothermal
