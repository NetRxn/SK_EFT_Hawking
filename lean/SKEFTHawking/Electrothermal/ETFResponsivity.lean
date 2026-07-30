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
  `solvesDrivenBalance_iff_linearized` shows — **on the predicate**, not on a pair of right-hand
  sides — that solving the driven balance *is* solving the textbook linearization with the
  bias-power slope and the bath conductance separate. It calls
  `linearizedSlope_eq_neg_effectiveConductance`, so `G_eff` enters by computation rather than by
  naming.
* `hasDerivAt_responsivityETF` / `hasDerivAt_responsivityBare` — the two responsivities as
  genuine **chain-rule** derivatives of current-vs-absorbed-power, `HasDerivAt.comp` of the two
  steps above. This is what makes the definitions honest: they are the derivatives, not labels.
* `abs_thermalResponse_le_thermalResponseAmplitude` + `thermalResponseAmplitude_attained` — the
  AC amplitude likewise earns its name: it is the *attained* envelope of `thermalResponse`, not a
  labelled expression the rolloff statements are asserted about.
* `sinusoidal_solution_tendsto_thermalResponse` / `sinusoidal_not_attracting_of_unstable` — and
  the word *steady state* earns its keep too, in both directions: the explicit sinusoidal solution
  attracts every other solution exactly on the stable branch, and repels them on the unstable one.

Only then are the correction identity and its magnitude/monotonicity corollaries stated.

## Conventions (inherited, not re-chosen)

* **Responses are signed throughout**, per Wave 1's Guardrail 2. Both responsivities carry the
  sign of `−dR/dT`: a positive-TCR element under voltage bias *loses* current as it heats.
  Magnitude statements are separate corollaries, never the primary form — and
  `responsivity_magnitudeOnly_loses_stability_information` refutes reading the *correction* pair
  through absolute values.
* **Noise densities are magnitudes**, because 6EB's are: `nepOfPSD S = √S ≥ 0`, and every 6EB
  theorem consuming `nepOfOutput` carries `0 < R`. The NEP-transfer statements here are therefore
  written on `|R_bare|` / `|R_etf|`, matching Wave 3's `johnsonNEP`. Feeding the signed
  responsivity into `nepOfOutput` returns a *negative* "NEP" (`−4/3` at `speedupWitness`), which
  is not a noise density in any convention. *(Corrected 2026-07-29; the two conventions were
  previously mixed across the Wave-2 / Wave-3 seam.)*
* **One-sided PSD / NEP** semantics come from 6EB (`Detection.NEPAlgebra`); this wave transfers
  through `nepOfOutput` and never re-chooses a convention.

## Layout

* **Definitions** — `currentTempSlope`, `responsivityBare`, `responsivityETF`.
* **Derivation** — the bullets above.
* **The correction** — `responsivity_etf_correction` (whose *only* hypothesis is `1 + ℒ ≠ 0`),
  magnitude and monotonicity corollaries.
* **NEP transfer (6EB seam)** — `nep_bare_understates_by_one_plus_loopGain` (the factor) and
  `nep_bare_lt_nep_etf_of_loopGain_pos` (the direction, pinned under its own hypothesis), with a
  rational witness quantifying the budget error at a stated `ℒ`.
* **Frequency rolloff** — the sinusoidal solution, its attractor status, its attained envelope,
  and the single-pole factor.
* **Non-vacuity** — reuses Wave 1's `speedupWitness` (`ℒ = 3`), so the witness is a statement
  about an already-published bias point rather than a fresh convenient one.
* **Degenerate branches, disclosed** — `responsivityETF_of_effectiveConductance_eq_zero`,
  `responsivity_of_G_eq_zero`, `steadyState_C_hypothesis_load_bearing`.

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
is not a fresh modelling choice: `solvesDrivenBalance_iff_linearized` shows that *solving this
predicate* is equivalent to solving the textbook balance written with the bias-power slope and the
bath conductance separate. -/
def SolvesDrivenBalance (m : ETFModel) (P_sig : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt f ((P_sig - m.effectiveConductance * f t) / m.C) t

/-- **`SolvesDrivenBalance` IS the physical linearization — stated ON the predicate.**

    SolvesDrivenBalance m P_sig f
      ↔  ∀ t,  ḟ(t) = ( P_sig + (d/dT(V²/R(T)) − G)·f(t) ) / C

The right-hand side is the driven heat balance written with the **bias-power slope and the bath
conductance kept separate** — the form a reader checks line by line against the textbook — and the
left-hand side is this file's pre-packaged `−G_eff` form. Their equivalence is a *call* to Wave 1's
`linearizedSlope_eq_neg_effectiveConductance`, so `G_eff` enters Wave 2 by computation rather than
by naming convention. The Wave-2 analogue of Wave 1's `etf_perturbation_solves_linearized`.

Both `hRne` and `hGne` are inherited from the linearization and are load-bearing there (the
factorization divides by `R²` and by `G`).

*(This replaced a congruence wrapper — named, before its removal on 2026-07-29,
drivenBalance_eq_effectiveConductance_form (de-backticked here: it no longer exists).
Adversarial review observed that the wrapper — `(h : a − b = −c) → P + (a−b)·δT = P − c·δT` —
never mentions `SolvesDrivenBalance` in its statement and therefore could not certify anything
about it; the claim now sits on the predicate it is about.)* -/
theorem solvesDrivenBalance_iff_linearized (m : ETFModel) (Rf : ℝ → ℝ) {T : ℝ}
    (hR : HasDerivAt Rf m.dRdT T) (hR₀ : Rf T = m.R) (hRne : m.R ≠ 0) (hGne : m.G ≠ 0)
    (P_sig : ℝ) (f : ℝ → ℝ) :
    m.SolvesDrivenBalance P_sig f
      ↔ ∀ t : ℝ, HasDerivAt f
          ((P_sig + (deriv (fun τ => m.V ^ 2 / Rf τ) T - m.G) * f t) / m.C) t := by
  rw [linearizedSlope_eq_neg_effectiveConductance m Rf hR hR₀ hRne hGne]
  constructor
  · intro h t
    exact (h t).congr_deriv (by ring)
  · intro h t
    exact (h t).congr_deriv (by ring)

/-- **Steady-state temperature rise per unit absorbed power: `δT = P_sig / G_eff`.**

At a steady state of the driven balance (vanishing time derivative), the temperature offset is
the absorbed power divided by the *effective* conductance — not by `G`. This is the entire
physical origin of the `(1+ℒ)` in `responsivityETF`, and it is derived from the ODE rather than
assumed.

Both `hC` and `hGe` are load-bearing. At `G_eff = 0` the steady state does not exist. At `C = 0`
Lean's total division collapses the balance to `∀ t, HasDerivAt f 0 t` — which is **not vacuous**;
it is *under-determined*, satisfied by every constant function, and a constant need not equal
`P_sig/G_eff`. `steadyState_C_hypothesis_load_bearing` exhibits exactly that failure. -/
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

/-- **`hC` cannot be dropped from `steadyState_deltaT`** — and *not* because the `C = 0` balance
is vacuous.

At `C = 0` Lean's total division turns the driven balance into `∀ t, HasDerivAt f 0 t`. That
condition is satisfied by **every constant function**, so it does not pin the trajectory at all;
`steadyState_deltaT`'s conclusion then fails for any constant other than `P_sig/G_eff`. Witness:
`C = 0`, `G = R = 1`, `V = dR/dT = 0` (hence `G_eff = 1 ≠ 0`, so `hGe` still holds), `P_sig = 0`
and the constant trajectory `f ≡ 5` — it solves the degenerate balance with vanishing derivative,
yet `f t = 5 ≠ 0 = P_sig/G_eff`.

*(Added 2026-07-29 after adversarial review: the original docstring called the `C = 0` derivative
condition "vacuous". It is *under-determined*, which is a different — and the actual — reason the
hypothesis is load-bearing. Same shape as Wave 1's `loopGain_R_hypothesis_load_bearing`.)* -/
theorem steadyState_C_hypothesis_load_bearing :
    ¬ ∀ (m : ETFModel), m.effectiveConductance ≠ 0 → ∀ (P_sig : ℝ) (f : ℝ → ℝ) (t : ℝ),
        SolvesDrivenBalance m P_sig f → deriv f t = 0 →
          f t = P_sig / m.effectiveConductance := by
  intro h
  have hm : (⟨0, 1, 1, 0, 0⟩ : ETFModel).effectiveConductance = 1 := by
    unfold effectiveConductance loopGain; norm_num
  have hbal : SolvesDrivenBalance ⟨0, 1, 1, 0, 0⟩ 0 (fun _ => (5:ℝ)) := by
    intro t
    rw [show ((0:ℝ) - (⟨0, 1, 1, 0, 0⟩ : ETFModel).effectiveConductance * 5)
        / (⟨0, 1, 1, 0, 0⟩ : ETFModel).C = 0 by rw [hm]; norm_num]
    exact hasDerivAt_const t (5:ℝ)
  have hval := h ⟨0, 1, 1, 0, 0⟩ (by rw [hm]; norm_num) 0 (fun _ => (5:ℝ)) 0 hbal (by simp)
  rw [hm] at hval
  norm_num at hval

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
and the two responsivities have **opposite signs** (`responsivity_opposite_sign_of_unstable`).

**And `1 + ℒ ≠ 0` is the ONLY hypothesis.** An earlier version also carried `G ≠ 0`; that binder
was dead weight for truth and is dropped (2026-07-29, adversarial review). At `G = 0` both
responsivities independently collapse to Lean's total-division `0`
(`responsivity_of_G_eq_zero`), so the identity survives there as a junk-value coincidence.
Carrying the binder would have wrongly suggested the correction is a claim about a live bath
conductance — the same objection Wave 1's `effectiveTimeConstant_eq_div` raises against unused
positivity. The degenerate branch is disclosed by a theorem instead of by a hypothesis. -/
theorem responsivity_etf_correction (m : ETFModel) (hL : 1 + m.loopGain ≠ 0) :
    m.responsivityBare = (1 + m.loopGain) * m.responsivityETF := by
  rcases eq_or_ne m.G 0 with hG | hG
  · unfold responsivityBare responsivityETF effectiveConductance
    rw [hG]
    simp
  · unfold responsivityBare responsivityETF effectiveConductance
    field_simp

/-- **The ETF responsivity is non-zero at a live bias point off the marginal boundary.** All three
hypotheses are exactly the non-vanishing of the three factors in
`R_etf = (dI/dT)/(G·(1+ℒ))`. Extracted because three statements below need precisely this, each
deriving `1 + ℒ ≠ 0` from a different condition on the loop gain. -/
theorem responsivityETF_ne_zero (m : ETFModel) (hGne : m.G ≠ 0) (hL : 1 + m.loopGain ≠ 0)
    (hslope : m.currentTempSlope ≠ 0) : m.responsivityETF ≠ 0 := by
  unfold responsivityETF
  exact div_ne_zero hslope (by
    unfold effectiveConductance
    exact mul_ne_zero hGne hL)

/-- **The bare form overstates the response by exactly `(1+ℒ)` on the stable, positive-feedback
branch.** For `ℒ > 0` and a live signal path (`dI/dT ≠ 0`), the magnitudes are strictly ordered:

    |R_etf| < |R_bare|.

This is the sensitivity overclaim the wave exists to quantify: a budget written with the bare
responsivity credits the device with more amps per watt than the biased device delivers. -/
theorem abs_responsivityETF_lt_abs_responsivityBare (m : ETFModel) (hGne : m.G ≠ 0)
    (hL : 0 < m.loopGain) (hslope : m.currentTempSlope ≠ 0) :
    |m.responsivityETF| < |m.responsivityBare| := by
  have hRetf : m.responsivityETF ≠ 0 :=
    m.responsivityETF_ne_zero hGne (by intro h; linarith [h]) hslope
  rw [responsivity_etf_correction m (by intro h; linarith [h]), abs_mul,
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
  have hneg : 1 + m.loopGain < 0 := by linarith
  have hRetf : m.responsivityETF ≠ 0 :=
    m.responsivityETF_ne_zero hGne (by intro h; linarith [h]) hslope
  rw [responsivity_etf_correction m (by intro h; linarith [h])]
  have hsq : 0 < m.responsivityETF ^ 2 := by positivity
  nlinarith [hsq]

/-! ## The 6EB seam: NEP transfer through the two responsivity forms

**Convention seam, fixed explicitly (corrected 2026-07-29).** 6EB's NEP is a **magnitude**: the
spectral form is `nepOfPSD S = √S ≥ 0`, and every 6EB theorem consuming `nepOfOutput` carries
`0 < R`. This file's responsivities are **signed** (Guardrail 2). Feeding a signed responsivity
straight into `nepOfOutput` therefore produces a *negative* "NEP" — at Wave 1's published
`speedupWitness` (`ℒ = 3`), `nepOfOutput 1 R_etf 1 = −4/3` — which is not a noise density in any
convention. The transfers below are consequently stated on `|R_bare|` and `|R_etf|`, matching
Wave 3's `johnsonNEP`, which already refers through `|responsivityETF|`.

Taking absolute values *here* loses nothing that Guardrail 2 protects: the sign of the
responsivity is a statement about the **response**, kept signed in
`responsivity_etf_correction` and `responsivity_opposite_sign_of_unstable`, whereas an
input-referred noise density is intrinsically non-negative. What must never be done is the
converse — reading the *correction* through absolute values, which
`responsivity_magnitudeOnly_loses_stability_information` refutes. -/

/-- **The two input-referred NEPs differ by exactly the factor `|1 + ℒ|`.**

NEP is output noise referred to the input by *dividing* by the responsivity
(6EB's `nepOfOutput σ R ENBW = σ/(R·√ENBW)`), so the `(1+ℒ)` responsivity overclaim reappears
here as

    NEP(using |R_bare|) = NEP(using |R_etf|) / |1 + ℒ|.

Stated on **magnitudes**, per the section note above: 6EB's `nepOfOutput` contract is a
non-negative density, and the signed form returns negative "NEP" values.

**The direction is a separate theorem, deliberately.** "An overstated responsivity understates
the NEP" is true exactly when `|1 + ℒ| > 1`, which is a condition on the bias point — it holds on
the whole stable positive-feedback branch `ℒ > 0` and is where the budget error is dangerous, but
it *fails* for `−2 < ℒ < 0`, where the bare form **overstates** the NEP instead. So the direction
is pinned by `nep_bare_lt_nep_etf_of_loopGain_pos` under its own hypothesis rather than asserted
in this docstring. *(The earlier signed statement's "an overstated responsivity understates NEP"
narrative was wrong-worded for `1 + ℒ < 0`; corrected 2026-07-29 after adversarial review.)*

This **calls** `Detection.nepOfOutput`, so the seam with 6EB is a computation rather than a
docstring reference. -/
theorem nep_bare_understates_by_one_plus_loopGain (m : ETFModel)
    (hL : 1 + m.loopGain ≠ 0) (sigma enbwVal : ℝ) :
    nepOfOutput sigma |m.responsivityBare| enbwVal
      = nepOfOutput sigma |m.responsivityETF| enbwVal / |1 + m.loopGain| := by
  unfold nepOfOutput
  rw [responsivity_etf_correction m hL, abs_mul]
  have hL' : |1 + m.loopGain| ≠ 0 := abs_ne_zero.mpr hL
  rcases eq_or_ne (Real.sqrt enbwVal) 0 with he | he
  · rw [he]; simp
  · rcases eq_or_ne |m.responsivityETF| 0 with hr | hr
    · rw [hr]; simp
    · field_simp

/-- **The dangerous direction, pinned: on the stable positive-feedback branch the bare
responsivity makes the detector look quieter than it is.**

For `ℒ > 0`, a live signal path and a live readout, the NEP computed with the bare responsivity
is **strictly below** the ETF-consistent one:

    NEP(using |R_bare|)  <  NEP(using |R_etf|).

This is the falsifiable form of the claim the previous theorem's docstring can only *describe*:
a budget written without electrothermal awareness reports a noise floor the device does not
achieve. It consumes `abs_responsivityETF_lt_abs_responsivityBare`, so the direction descends
from the responsivity ordering rather than from a re-derivation.

`0 < ℒ` is load-bearing for the direction (not merely for the proof): at `−2 < ℒ < 0` the factor
`|1 + ℒ| < 1` and the inequality **reverses**. -/
theorem nep_bare_lt_nep_etf_of_loopGain_pos (m : ETFModel) (hGne : m.G ≠ 0)
    (hL : 0 < m.loopGain) (hslope : m.currentTempSlope ≠ 0)
    {sigma enbwVal : ℝ} (hσ : 0 < sigma) (henbw : 0 < enbwVal) :
    nepOfOutput sigma |m.responsivityBare| enbwVal
      < nepOfOutput sigma |m.responsivityETF| enbwVal := by
  have hRetf : m.responsivityETF ≠ 0 :=
    m.responsivityETF_ne_zero hGne (by intro h; linarith [h]) hslope
  have hpos : 0 < |m.responsivityETF| := abs_pos.mpr hRetf
  have hlt : |m.responsivityETF| < |m.responsivityBare| :=
    m.abs_responsivityETF_lt_abs_responsivityBare hGne hL hslope
  have hs : 0 < Real.sqrt enbwVal := Real.sqrt_pos.mpr henbw
  unfold nepOfOutput
  exact div_lt_div_of_pos_left hσ (by positivity) (by nlinarith)

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

/-- **The NEP consequence at the published bias point**, stated in 6EB's own functional and on
6EB's own (non-negative) NEP contract: the bare-responsivity NEP is a **quarter** of the
ETF-consistent one, for *every* output noise level and *every* ENBW.

A quarter of a magnitude, not of a signed quantity — the signed form at this bias point would
report `nepOfOutput 1 R_etf 1 = −4/3`, which is not a noise density. See the section note. -/
theorem speedupWitness_nep_quarter (sigma enbwVal : ℝ) :
    nepOfOutput sigma |speedupWitness.responsivityBare| enbwVal
      = nepOfOutput sigma |speedupWitness.responsivityETF| enbwVal / 4 := by
  have h := nep_bare_understates_by_one_plus_loopGain speedupWitness (by
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
it collapses to the DC steady state `P₀/G_eff` of `steadyState_deltaT`.

**"Steady state" is a claim, and it is only true on the stable branch.** What is verified
unconditionally is that this is *a* solution of the driven sinusoidal balance
(`thermalResponse_solves`). That it is the one a physical detector settles into requires the
other solutions to approach it, which holds exactly when `ℒ > −1`
(`sinusoidal_solution_tendsto_thermalResponse`) and **fails** on the unstable branch, where every
other solution runs away from it (`sinusoidal_not_attracting_of_unstable`). Read this definition
as "the particular sinusoidal solution", and reach for the qualifier "steady state" only under
`etf_stable_iff`. *(Qualification added 2026-07-29 after adversarial review.)* -/
noncomputable def thermalResponse (m : ETFModel) (ω P₀ : ℝ) : ℝ → ℝ := fun t =>
  (P₀ * m.effectiveConductance * Real.cos (ω * t) + P₀ * m.C * ω * Real.sin (ω * t))
    / (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2)

/-- **Amplitude of the sinusoidal response**, `|P₀|/√(G_eff² + C²ω²)`.

An *amplitude*, hence `|P₀|` — and the absolute value is not cosmetic. Under the earlier signed
definition this quantity was **negative** for `P₀ < 0` (at Wave 1's `speedupWitness`,
`thermalResponseAmplitude 0 (−1) = −1/4`) while `|δT(t)|` is not; the name was false, the envelope
bound below would have failed, and the docstring's `√(a²+b²)` claim was wrong (the quadrature sum
of the `cos`/`sin` coefficients is `|P₀|/√D`, never `P₀/√D`). *(Corrected 2026-07-29 after
adversarial review.)*

**Linked to the object it names by theorems, not by its name** — the file's own Q5 standard:
`abs_thermalResponse_le_thermalResponseAmplitude` (it bounds `|thermalResponse|` at every time)
and `thermalResponseAmplitude_attained` (the bound is *attained*, so it is the least such bound —
the response's envelope, not merely an envelope). The single-pole form is
`thermalResponseAmplitude_eq_singlePole`. -/
noncomputable def thermalResponseAmplitude (m : ETFModel) (ω P₀ : ℝ) : ℝ :=
  |P₀| / Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2)

/-- **The sinusoidally driven linearized heat balance**, `C·δṪ = P₀·cos(ωt) − G_eff·δT` — the AC
analogue of `SolvesDrivenBalance`.

Named as a predicate rather than left inline in `thermalResponse_solves` because "steady state" is
a statement about *all* solutions, not about the one that was written down: it is meaningful only
if the others approach it. With the predicate in hand that becomes provable in both directions
(`sinusoidal_solution_tendsto_thermalResponse`, `sinusoidal_not_attracting_of_unstable`) — the
same move Wave 1 makes with `SolvesHeatBalance` and `solution_unique`. -/
def SolvesSinusoidalBalance (m : ETFModel) (ω P₀ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt f ((P₀ * Real.cos (ω * t) - m.effectiveConductance * f t) / m.C) t

/-- **The explicit sinusoidal solution solves the driven balance**, at every time:

    C · δṪ(t) = P₀·cos(ωt) − G_eff · δT(t).

`HasDerivAt` verification of an explicit solution — the `etf_perturbation_solves` /
`dampedTwoLevel_population_solves_rate` pattern, no ODE-existence machinery. This is the
substantive content of the rolloff: the amplitude formula below is algebra *once this holds*. -/
theorem thermalResponse_solves (m : ETFModel) (hC : m.C ≠ 0) {ω : ℝ} (P₀ : ℝ)
    (hD : m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2 ≠ 0) :
    m.SolvesSinusoidalBalance ω P₀ (m.thermalResponse ω P₀) := by
  intro t
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

/-! ### Is it a *steady state*? Only on the stable branch — both directions -/

/-- Two solutions of the same sinusoidally driven balance differ by a solution of Wave 1's
**homogeneous** balance: the drive cancels. The bridge that lets the stability dichotomy decide
whether `thermalResponse` is an attractor. -/
theorem solvesHeatBalance_sub_of_solvesSinusoidal (m : ETFModel) {ω P₀ : ℝ} {f g : ℝ → ℝ}
    (hf : m.SolvesSinusoidalBalance ω P₀ f) (hg : m.SolvesSinusoidalBalance ω P₀ g) :
    m.SolvesHeatBalance (fun t => f t - g t) := by
  intro t
  exact ((hf t).sub (hg t)).congr_deriv (by ring)

/-- **On the stable branch `thermalResponse` really IS the steady state**: *every* solution of the
sinusoidally driven balance converges to it.

    ℒ > −1  ⟹  f(t) − δT_ss(t) → 0   for every solution f.

This is what licenses the word "steady state" in the definitions above, and it is a genuine
composition rather than a restatement: the difference of two solutions solves Wave 1's homogeneous
balance (`solvesHeatBalance_sub_of_solvesSinusoidal`), and Wave 1's dichotomy `etf_stable_iff`
then sends it to zero. Without it the rolloff would be a statement about one particular solution
among infinitely many.

Note what is *not* needed: no non-degeneracy binder on `G_eff² + C²ω²`, because on the stable
branch `0 < G_eff` supplies it. -/
theorem sinusoidal_solution_tendsto_thermalResponse (m : ETFModel) (hC : 0 < m.C) (hG : 0 < m.G)
    (hL : -1 < m.loopGain) {ω P₀ : ℝ} {f : ℝ → ℝ} (hf : m.SolvesSinusoidalBalance ω P₀ f) :
    Filter.Tendsto (fun t => f t - m.thermalResponse ω P₀ t) Filter.atTop (nhds 0) := by
  have hGe : 0 < m.effectiveConductance := (m.effectiveConductance_pos_iff hG).mpr hL
  have hD : m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2 ≠ 0 := by
    have h1 : 0 < m.effectiveConductance ^ 2 := pow_pos hGe 2
    have h2 : (0:ℝ) ≤ m.C ^ 2 * ω ^ 2 := by positivity
    exact ne_of_gt (by linarith)
  exact (m.etf_stable_iff hC hG).mpr hL _
    (m.solvesHeatBalance_sub_of_solvesSinusoidal hf (m.thermalResponse_solves (ne_of_gt hC) P₀ hD))

/-- **On the unstable branch it is never reached** — the other half, so the qualification is not
one-sided prose.

For `ℒ < −1`, any solution that does not start *exactly* on `thermalResponse` runs away from it
without bound: `|f(t) − δT_ss(t)| → ∞`. So on that branch `thermalResponse` is a particular
solution and nothing more — calling it "the steady state" there would be wrong, not merely
imprecise. Consumes Wave 1's `etf_diverges_of_loopGain_lt_neg_one`. -/
theorem sinusoidal_not_attracting_of_unstable (m : ETFModel) (hC : 0 < m.C) (hG : 0 < m.G)
    (hL : m.loopGain < -1) {ω P₀ : ℝ} {f : ℝ → ℝ} (hf : m.SolvesSinusoidalBalance ω P₀ f)
    (hne : f 0 ≠ m.thermalResponse ω P₀ 0) :
    Filter.Tendsto (fun t => |f t - m.thermalResponse ω P₀ t|) Filter.atTop Filter.atTop := by
  have hGe : m.effectiveConductance < 0 := by
    unfold effectiveConductance
    exact mul_neg_of_pos_of_neg hG (by linarith)
  have hD : m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2 ≠ 0 := by
    have h1 : 0 < m.effectiveConductance ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (ne_of_lt hGe)))
    have h2 : (0:ℝ) ≤ m.C ^ 2 * ω ^ 2 := by positivity
    exact ne_of_gt (by linarith)
  exact m.etf_diverges_of_loopGain_lt_neg_one hC hG hL
    (m.solvesHeatBalance_sub_of_solvesSinusoidal hf
      (m.thermalResponse_solves (ne_of_gt hC) P₀ hD)) (sub_ne_zero.mpr hne)

/-! ### The amplitude is the response's envelope — the link, not the label -/

/-- **`thermalResponseAmplitude` bounds `|thermalResponse|` at every time.**

    |δT(t)| ≤ |P₀| / √(G_eff² + C²ω²)   for all t.

The Cauchy–Schwarz step `(a·cos θ + b·sin θ)² ≤ a² + b²` — with the deficit
`(a·sin θ − b·cos θ)² ≥ 0` — applied to the two quadrature coefficients of `thermalResponse`.

This is the theorem the amplitude's *name* previously stood in for. Without it (and its companion
`thermalResponseAmplitude_attained`) the rolloff statements below would be assertions about a
labelled expression rather than about the response the rest of the section derives. -/
theorem abs_thermalResponse_le_thermalResponseAmplitude (m : ETFModel) (ω P₀ : ℝ)
    (hD : 0 < m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) (t : ℝ) :
    |m.thermalResponse ω P₀ t| ≤ m.thermalResponseAmplitude ω P₀ := by
  have hcs : Real.sin (ω * t) ^ 2 + Real.cos (ω * t) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hCS : (m.effectiveConductance * Real.cos (ω * t) + m.C * ω * Real.sin (ω * t)) ^ 2
      ≤ m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2 := by
    nlinarith [sq_nonneg (m.effectiveConductance * Real.sin (ω * t)
      - m.C * ω * Real.cos (ω * t)), hcs]
  have hAnn : 0 ≤ m.thermalResponseAmplitude ω P₀ := by
    unfold thermalResponseAmplitude; positivity
  have hkey : m.thermalResponse ω P₀ t ^ 2 ≤ m.thermalResponseAmplitude ω P₀ ^ 2 := by
    unfold thermalResponse thermalResponseAmplitude
    rw [div_pow, div_pow, Real.sq_sqrt hD.le, sq_abs, div_le_div_iff₀ (by positivity) hD]
    nlinarith [mul_le_mul_of_nonneg_left hCS (mul_nonneg (sq_nonneg P₀) hD.le)]
  calc |m.thermalResponse ω P₀ t|
      = Real.sqrt (m.thermalResponse ω P₀ t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (m.thermalResponseAmplitude ω P₀ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = m.thermalResponseAmplitude ω P₀ := Real.sqrt_sq hAnn

/-- **The envelope is attained — so it is the response's amplitude, not merely an upper bound.**

There is a time at which `|δT(t)|` equals `thermalResponseAmplitude ω P₀` exactly. Together with
`abs_thermalResponse_le_thermalResponseAmplitude` this says the amplitude is the *least* bound on
the excursion, which is what the word means; a bound that were never attained would leave the
single-pole rolloff below a statement about a strictly conservative envelope.

The witnessing phase is `ω·t = arccos(G_eff/√D)`, with the sign of the drive's quadrature
component `C·ω` choosing the branch; at `ω = 0` every time works and `t = 0` is taken. -/
theorem thermalResponseAmplitude_attained (m : ETFModel) (ω P₀ : ℝ)
    (hD : 0 < m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) :
    ∃ t : ℝ, |m.thermalResponse ω P₀ t| = m.thermalResponseAmplitude ω P₀ := by
  have hsD : 0 < Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) :=
    Real.sqrt_pos.mpr hD
  have hsq : Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) ^ 2
      = m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2 := Real.sq_sqrt hD.le
  -- the normalized quadrature coefficient, and the phase realizing it
  set r := Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) with hr
  have hrne : r ≠ 0 := ne_of_gt hsD
  have habs : |m.effectiveConductance| ≤ r := by
    rw [← Real.sqrt_sq_eq_abs, hr]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (m.C * ω)])
  have hle1 : m.effectiveConductance / r ≤ 1 :=
    (div_le_one hsD).mpr (le_trans (le_abs_self _) habs)
  have hge1 : -1 ≤ m.effectiveConductance / r :=
    (le_div_iff₀ hsD).mpr (by
      have := neg_abs_le m.effectiveConductance
      linarith)
  set θ := if 0 ≤ m.C * ω then Real.arccos (m.effectiveConductance / r)
    else -Real.arccos (m.effectiveConductance / r) with hθ
  have hcosθ : Real.cos θ = m.effectiveConductance / r := by
    rw [hθ]
    split
    · exact Real.cos_arccos hge1 hle1
    · rw [Real.cos_neg]; exact Real.cos_arccos hge1 hle1
  have hsinθ : Real.sin θ = m.C * ω / r := by
    have hbase : Real.sin (Real.arccos (m.effectiveConductance / r))
        = Real.sqrt (1 - (m.effectiveConductance / r) ^ 2) := Real.sin_arccos _
    have hval : Real.sqrt (1 - (m.effectiveConductance / r) ^ 2) = |m.C * ω| / r := by
      rw [div_pow, hsq, show 1 - m.effectiveConductance ^ 2
          / (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2)
          = (m.C * ω) ^ 2 / (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) by
        field_simp; ring,
        Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, ← hr]
    rw [hθ]
    split
    · rename_i hpos
      rw [hbase, hval, abs_of_nonneg hpos]
    · rename_i hneg
      rw [Real.sin_neg, hbase, hval, abs_of_neg (not_le.mp hneg), neg_div, neg_neg]
  -- the response at the realizing phase, in closed form
  have hnum : P₀ * m.effectiveConductance * (m.effectiveConductance / r)
      + P₀ * m.C * ω * (m.C * ω / r) = P₀ * r := by
    have h1 : P₀ * m.effectiveConductance * (m.effectiveConductance / r)
        + P₀ * m.C * ω * (m.C * ω / r)
        = P₀ * (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) / r := by
      field_simp
    rw [h1, ← hsq]
    field_simp
  rcases eq_or_ne ω 0 with hω | hω
  · subst hω
    refine ⟨0, ?_⟩
    have hGne : m.effectiveConductance ≠ 0 := by
      intro h; rw [h] at hD; norm_num at hD
    have hane : |m.effectiveConductance| ≠ 0 := abs_ne_zero.mpr hGne
    unfold thermalResponse thermalResponseAmplitude
    rw [show (0:ℝ) * (0:ℝ) = 0 by ring, Real.cos_zero, Real.sin_zero,
      show m.effectiveConductance ^ 2 + m.C ^ 2 * (0:ℝ) ^ 2 = m.effectiveConductance ^ 2 by ring,
      Real.sqrt_sq_eq_abs,
      show P₀ * m.effectiveConductance * 1 + P₀ * m.C * 0 * 0 = P₀ * m.effectiveConductance by
        ring,
      abs_div, abs_mul, abs_pow]
    field_simp
  · refine ⟨θ / ω, ?_⟩
    have hmul : ω * (θ / ω) = θ := by field_simp
    unfold thermalResponse thermalResponseAmplitude
    rw [← hr, hmul, hcosθ, hsinθ, hnum, ← hsq,
      show P₀ * r / r ^ 2 = P₀ / r by field_simp, abs_div, abs_of_pos hsD]

/-- **The single-pole rolloff.** The response amplitude is the DC amplitude divided by the
familiar single-pole factor built from the *effective* time constant:

    amplitude(ω) = (|P₀| / G_eff) / √(1 + (ω·τ_eff)²),   τ_eff = C/G_eff.

Note the `τ_eff`, not `τ`: electrothermal feedback moves the pole, which is exactly why Wave 1's
`effectiveTimeConstant` had to exist before this statement could be made.

`0 < G_eff` **is** load-bearing in this form (it is not merely a route requirement): the
right-hand side is written over the signed `G_eff`, so on the unstable branch it is negative while
the left-hand side is not. The generalization that survives `G_eff < 0` divides by `|G_eff|`
instead, and `responsivity_frequency_rolloff` below is stated in exactly that generality. -/
theorem thermalResponseAmplitude_eq_singlePole (m : ETFModel)
    (hGe : 0 < m.effectiveConductance) (ω P₀ : ℝ) :
    m.thermalResponseAmplitude ω P₀
      = (|P₀| / m.effectiveConductance) / Real.sqrt (1 + (ω * m.effectiveTimeConstant) ^ 2) := by
  unfold thermalResponseAmplitude effectiveTimeConstant
  have hGne : m.effectiveConductance ≠ 0 := ne_of_gt hGe
  have hrw : 1 + (ω * (m.C / m.effectiveConductance)) ^ 2
      = (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) / m.effectiveConductance ^ 2 := by
    field_simp
  have hsq : Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [hrw, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hGe.le]
  field_simp

/-- **DC limit.** At `ω = 0` the amplitude is the magnitude of the DC steady state of
`steadyState_deltaT`, so the rolloff factor is normalized to `1` at zero frequency rather than to
an arbitrary constant. -/
theorem thermalResponseAmplitude_zero (m : ETFModel) (hGe : 0 < m.effectiveConductance) (P₀ : ℝ) :
    m.thermalResponseAmplitude 0 P₀ = |P₀| / m.effectiveConductance := by
  unfold thermalResponseAmplitude
  rw [show m.effectiveConductance ^ 2 + m.C ^ 2 * (0:ℝ) ^ 2 = m.effectiveConductance ^ 2 by ring,
    Real.sqrt_sq hGe.le]

/-- **The rolloff is a genuine rolloff: strictly decreasing in frequency.** For any non-zero drive
on the stable branch with non-zero heat capacity, a higher modulation frequency yields a strictly
smaller response. Without this the "single-pole factor" would be compatible with a flat response —
this is the statement that makes the factor bite.

`P₀ ≠ 0` rather than `0 < P₀`: with the amplitude taken on `|P₀|` the drive's sign is irrelevant
and only its non-vanishing matters (at `P₀ = 0` both sides are `0` and the inequality fails). -/
theorem thermalResponseAmplitude_strictAnti (m : ETFModel) (hGe : 0 < m.effectiveConductance)
    (hC : m.C ≠ 0) {P₀ : ℝ} (hP : P₀ ≠ 0) {ω ω' : ℝ} (hω : 0 ≤ ω) (hlt : ω < ω') :
    m.thermalResponseAmplitude ω' P₀ < m.thermalResponseAmplitude ω P₀ := by
  unfold thermalResponseAmplitude
  have hCsq : 0 < m.C ^ 2 := by positivity
  have hd : m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2
      < m.effectiveConductance ^ 2 + m.C ^ 2 * ω' ^ 2 := by
    have : ω ^ 2 < ω' ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  exact div_lt_div_of_pos_left (abs_pos.mpr hP) hpos (Real.sqrt_lt_sqrt (by positivity) hd)

/-- **The AC's `responsivity_frequency_rolloff`.** The *current* response amplitude at modulation
frequency `ω` is the DC ETF responsivity magnitude times the single-pole factor:

    |dI/dT| · amplitude(ω) = |R_etf| · |P₀| / √(1 + (ω·τ_eff)²).

Stated as an identity between the physically measurable current amplitude (left) and the
budget-facing form (right), so it is a bridge rather than a restatement of a definition. The left
factor is `|thermalResponse|`'s attained envelope
(`abs_thermalResponse_le_thermalResponseAmplitude`, `thermalResponseAmplitude_attained`), so both
sides are magnitudes of measurable excursions.

**Carries only `G_eff ≠ 0`**, not `0 < G_eff`. Restricting to the stable branch would silently
exclude the unstable operating points Guardrail 2 exists to keep visible — and the identity is
simply true there, since every quantity in it is a magnitude. *(Weakened from `0 < G_eff`
2026-07-29 after adversarial review.)* A `0 ≤ P₀` binder would likewise be dead weight: the
identity holds for every drive amplitude. -/
theorem responsivity_frequency_rolloff (m : ETFModel) (hGe : m.effectiveConductance ≠ 0)
    (P₀ ω : ℝ) :
    |m.currentTempSlope| * m.thermalResponseAmplitude ω P₀
      = |m.responsivityETF| * |P₀| / Real.sqrt (1 + (ω * m.effectiveTimeConstant) ^ 2) := by
  have hGsq : (0:ℝ) < m.effectiveConductance ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hGe))
  have hane : |m.effectiveConductance| ≠ 0 := by simpa using hGe
  have hsq : Real.sqrt (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  unfold thermalResponseAmplitude responsivityETF effectiveTimeConstant
  have hrw : 1 + (ω * (m.C / m.effectiveConductance)) ^ 2
      = (m.effectiveConductance ^ 2 + m.C ^ 2 * ω ^ 2) / m.effectiveConductance ^ 2 := by
    field_simp
  rw [hrw, Real.sqrt_div' _ (by positivity), Real.sqrt_sq_eq_abs, abs_div]
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

/-- **The thermally-isolated branch is junk in BOTH responsivities, and is disclosed as such.**

At `G = 0` — no bath conductance, so no temperature-per-power at all — Lean's total division
sends `responsivityBare` and `responsivityETF` *both* to `0`. This is what makes `G ≠ 0` dead
weight in `responsivity_etf_correction`: the identity `0 = (1 + 0)·0` holds there, but as a
coincidence of junk values rather than as physics. The disclosure lives here, in a theorem, so
that dropping the binder does not drop the information — the pattern Wave 1 uses for
`loopGain_of_G_eq_zero`.

Every *quantitative* statement in this file that reads physics into the responsivities
(`abs_responsivityETF_lt_abs_responsivityBare`, `responsivity_opposite_sign_of_unstable`,
`nep_bare_lt_nep_etf_of_loopGain_pos`) therefore carries `G ≠ 0` explicitly, and each one is
false at `G = 0`. -/
theorem responsivity_of_G_eq_zero (m : ETFModel) (h : m.G = 0) :
    m.responsivityBare = 0 ∧ m.responsivityETF = 0 := by
  refine ⟨?_, ?_⟩
  · unfold responsivityBare
    rw [h, div_zero]
  · refine m.responsivityETF_of_effectiveConductance_eq_zero ?_
    unfold effectiveConductance
    rw [h, zero_mul]

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
  · rw [responsivity_etf_correction speedupWitness
      (by rw [speedupWitness_loopGain]; norm_num), abs_mul]
  · rw [responsivity_etf_correction unstableWitness
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
