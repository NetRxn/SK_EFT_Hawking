import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import SKEFTHawking.QuantumNetwork.NumericalBounds

/-!
# Phase 6EC Wave 1 — the linearized electrothermal model and the stability dichotomy

**Publication target: bundle D12** (*Kernel-Verified Detector & Readout Metrology*).

A thermal detector (bolometer / calorimeter / TES-class sensor) held at a bias point obeys the
heat balance `C·Ṫ = P_bias(T) + P_signal − G·(T − T_bath)`. Under **voltage bias** the Joule term
is `P_bias(T) = V²/R(T)`, and its temperature slope feeds back on the thermal relaxation. This
file builds that feedback layer exactly: the loop gain, the effective conductance, the explicit
solution of the linearized heat balance, and the stability dichotomy as an **iff**.

## What is proved

* `biasPower_linearization` — `d/dT (V²/R(T)) = −V²·(dR/dT)/R²`, the **sign-carrying** step, taken
  from `deriv` rather than asserted.
* `linearizedSlope_eq_neg_effectiveConductance` — the total temperature slope of the heat-balance
  right-hand side is exactly `−G_eff` with `G_eff = G·(1 + ℒ)`, `ℒ = V²·(dR/dT)/(R²·G)`. This is
  where the definition of `loopGain` earns its keep: it is not a naming convention, it is the
  quantity that makes the slope factor.
* `etf_perturbation_solves` + `solution_unique` — `δT(t) = δT₀·exp(−t/τ_eff)` solves the
  linearized balance (`HasDerivAt`, explicit solution, no ODE-existence machinery — the
  `SKEFTHawking.OpenSystems.dampedTwoLevel_population_solves_rate` pattern), **and every solution
  is of this form**. Uniqueness is what lets the stability predicate quantify over all solutions
  instead of over one chosen trajectory.
* `etf_stable_iff` — **the dichotomy**: every solution of the linearized balance relaxes to zero
  **iff** `ℒ > −1`. Both directions are substantive (see "The decay predicate" below).
* `etf_diverges_of_loopGain_lt_neg_one` / `etf_marginal_of_loopGain_eq_neg_one` — the other two
  branches: runaway `|δT| → ∞` for every non-zero initial perturbation when `ℒ < −1`, and a
  frozen perturbation exactly at `ℒ = −1`. The trichotomy is complete, not one-sided.
* `etf_timeConstant_speedup` / `etf_timeConstant_slowdown` — `τ_eff = τ/(1+ℒ)`, faster than the
  bare thermal time constant for `ℒ > 0` and slower for `−1 < ℒ < 0`; and
  `effectiveTimeConstant_neg_of_unstable` — on the unstable branch `τ_eff` is *negative*, so
  reading it through an absolute value inverts the physics.
* `etf_perturbation_solves_linearized` — the same ODE fact written with the bias-power slope and
  the bath conductance kept **separate**, so it can be checked line by line against the textbook
  heat balance rather than against the derived `G_eff`.
* `loopGain_eq_irwinHilton` — agreement with the instrument literature's `ℒ = P_J·α/(G·T)`
  convention, as a theorem rather than as a comment.

## GUARDRAIL 1 — the linearized model IS the object

Every statement below is about the **stated small-signal model at a bias point**: a five-real-
number record `ETFModel` and the first-order linear ODE it defines. No theorem is a claim about
a physical device. A physical detector realizes this model only inside a validity neighbourhood
of its bias point, and *that identification is the consumer's declared hypothesis*, never
smuggled in here. Large-signal and nonlinear behaviour is out of scope: nothing below constrains
a device driven outside its linear regime, and `biasPower_linearization` is a statement about the
derivative of `V²/R(T)` at one temperature, not about the Joule power over any interval.

## GUARDRAIL 2 — signs are physics, and they are kept signed

`dRdT` is **signed**, and its sign carries the whole stability story: under voltage bias a
positive temperature coefficient (`dR/dT > 0`) gives `ℒ > 0` — heating raises `R`, which *lowers*
`V²/R`, which cools: stabilizing negative electrothermal feedback — while `dR/dT < 0` gives
`ℒ < 0` and can destabilize (`unstable_imp_dRdT_neg`: instability under voltage bias *requires*
negative `dR/dT`). Three commitments enforce this rather than merely describing it:

1. The dichotomy is an **iff** (`etf_stable_iff`), not a sufficient condition, so no theorem can
   be read as "positive loop gain is what stability means".
2. `loopGain_pos_iff_dRdT_pos` states the sign transfer as a biconditional.
3. `magnitudeOnly_criterion_unsound` **refutes** the magnitude-only shortcut at the input: there
   is a model that is unstable while the model obtained by replacing `dRdT` with `|dRdT|` is
   stable, so a criterion phrased on `|dR/dT|` reports the opposite verdict.
4. `absLoopGain_criterion_unsound` refutes it at the derived quantity: two bias points with the
   *same* `|ℒ| = 2` sit on opposite sides of the dichotomy, so an `|ℒ| ≤ ℒ_max` budget is not
   conservative — it is wrong in both directions.
5. `effectiveTimeConstant_neg_of_unstable` blocks the third sign-erasure route: on the unstable
   branch `τ_eff` is *negative*, so reporting `|τ_eff|` turns a runaway point into a "fast"
   detector.

Items 3–5 are the specific defect this phase's Definition of Done audits for, discharged as
theorems instead of as review instructions.

## The decay predicate — why `etf_stable_iff` is not a restatement

`PerturbationsDecay m` is **not** an alias for `0 < G_eff`. It says: *every* function `f`
satisfying the linearized heat balance (`SolvesHeatBalance`, an `∀ t, HasDerivAt …` condition on
the actual trajectory) satisfies `Tendsto f atTop (𝓝 0)`. Neither direction of the iff is
definitional:

* `←` needs `solution_unique` (an arbitrary solution must first be identified with the explicit
  exponential) and then the limit `exp(−rt) → 0` for `r > 0`.
* `→` needs a **witness**: `perturbation 1` is a solution (`etf_perturbation_solves`) which, when
  `ℒ ≤ −1`, satisfies `perturbation 1 t ≥ 1` for all `t ≥ 0` and hence cannot tend to `0`.

The predicate is also non-vacuous by construction — solutions always exist
(`etf_perturbation_solves`) — so `PerturbationsDecay` is never true for want of a trajectory.

## Total division, and which hypotheses are load-bearing

Lean's total division sends `x/0` to `0`, so a model with `R = 0` or `G = 0` reports
`loopGain = 0` — the *stable* verdict — no matter how destabilizing `dRdT` is
(`loopGain_of_R_eq_zero`, `loopGain_R_hypothesis_load_bearing`). And `0 < G` is load-bearing in
`etf_stable_iff` itself: at `G < 0` the criterion **inverts**
(`stability_G_hypothesis_load_bearing` exhibits a model with `ℒ > −1` that does not decay).
Positivity is therefore carried in binder lists per theorem — minimal, explicit, and witnessed
non-droppable — rather than bundled into the structure where it would be invisible at use sites.

## References

- `docs/roadmaps/Phase6EC_Roadmap.md` — Wave 1 acceptance criteria and both guardrails.
- `SKEFTHawking.OpenSystems.dampedTwoLevel_population_solves_rate` — the explicit-solution +
  `HasDerivAt`-verification pattern this file's ODE layer follows.
- `SKEFTHawking.QuantumNetwork.expNeg_enclosure` — the rational-enclosure pattern used by
  `stableWitness_decay_enclosure` (a real call, not a docstring reference).

Invariants (Phase 6EC): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no
new project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.Electrothermal

open Filter
open scoped Topology

/-! ## The bias-point model -/

/-- **A linearized electrothermal bias point under voltage bias.**

Five real numbers, and nothing else:

* `C` — heat capacity of the thermal element `[J/K]`;
* `G` — thermal conductance to the bath `[W/K]`;
* `R` — resistance **at the bias point** `[Ω]`;
* `V` — bias voltage `[V]` (only `V²` ever enters, so its sign is immaterial — and `V = 0`, the
  unbiased point, is deliberately admissible: it gives `ℒ = 0`, the no-feedback limit);
* `dRdT` — the **signed** derivative `dR/dT` at the bias point `[Ω/K]`.

**Positivity is deliberately *not* a field.** `0 < C`, `0 < G`, `0 < R` are carried in the binder
list of each theorem that needs them, which (i) keeps every statement's hypotheses minimal and
visible at the use site, and (ii) makes the degenerate branches *statable*, so their
non-droppability can be witnessed by theorems (`loopGain_R_hypothesis_load_bearing`,
`stability_G_hypothesis_load_bearing`) instead of asserted in prose.

Per Guardrail 1: this record *is* the object of every theorem below. Identifying a physical
detector's bias point with a particular `ETFModel` is the consumer's declared hypothesis. -/
structure ETFModel where
  /-- Heat capacity of the thermal element `[J/K]`. -/
  C : ℝ
  /-- Thermal conductance to the bath `[W/K]`. -/
  G : ℝ
  /-- Resistance at the bias point `[Ω]`. -/
  R : ℝ
  /-- Bias voltage `[V]`; only `V²` enters. -/
  V : ℝ
  /-- Signed temperature derivative `dR/dT` at the bias point `[Ω/K]`. -/
  dRdT : ℝ

namespace ETFModel

/-- **Electrothermal feedback loop gain under voltage bias**

    ℒ = V² · (dR/dT) / (R² · G).

Signed, by construction: `V²`, `R²` and `G` are non-negative at any admissible bias point, so
`sign ℒ = sign (dR/dT)` (`loopGain_pos_iff_dRdT_pos`). This is Guardrail 2 at the definitional
level — there is no `|dRdT|` anywhere in this file's forward direction, and the magnitude-only
alternative is refuted in `magnitudeOnly_criterion_unsound`.

Agreement with the Irwin–Hilton convention `ℒ = P_J·α/(G·T)` (with `P_J = V²/R` the Joule power
and `α = (T/R)·(dR/dT)` the dimensionless temperature sensitivity) is a theorem, not a comment:
`loopGain_eq_irwinHilton`.

**Degenerate branch, disclosed.** At `R = 0` or `G = 0` the quotient is undefined and Lean returns
`0` — the "no feedback / stable" verdict (`loopGain_of_R_eq_zero`, `loopGain_of_G_eq_zero`). Every
statement that reads a physical meaning into `ℒ` therefore carries `0 < R` / `0 < G` explicitly. -/
noncomputable def loopGain (m : ETFModel) : ℝ := m.V ^ 2 * m.dRdT / (m.R ^ 2 * m.G)

/-- **Effective (electrothermal) thermal conductance** `G_eff = G·(1 + ℒ)`.

The conductance that actually governs relaxation once the bias power's temperature dependence is
folded in — proved to be exactly the negated slope of the linearized heat-balance right-hand side
in `linearizedSlope_eq_neg_effectiveConductance`. -/
noncomputable def effectiveConductance (m : ETFModel) : ℝ := m.G * (1 + m.loopGain)

/-- The **bare** thermal time constant `τ = C/G` (no electrothermal feedback). -/
noncomputable def timeConstant (m : ETFModel) : ℝ := m.C / m.G

/-- The **effective** thermal time constant `τ_eff = C/G_eff`; equals `τ/(1+ℒ)` unconditionally
(`effectiveTimeConstant_eq_div`). It is **positive on the stable branch and negative on the
unstable one** (`effectiveTimeConstant_neg_of_unstable`) — the sign is load-bearing, so this is
not a quantity to read through an absolute value. -/
noncomputable def effectiveTimeConstant (m : ETFModel) : ℝ := m.C / m.effectiveConductance

/-- Joule power dissipated at the bias point under voltage bias, `P_J = V²/R`. -/
noncomputable def joulePower (m : ETFModel) : ℝ := m.V ^ 2 / m.R

/-- The dimensionless logarithmic temperature sensitivity `α = (T/R)·(dR/dT)` at bath-referred
temperature `T`. Signed, like `dRdT`: `α > 0` is the positive-TCR (thermistor-in-the-metallic-
sense / TES) case, `α < 0` the semiconductor-thermistor case. -/
noncomputable def alphaTCR (m : ETFModel) (T : ℝ) : ℝ := T * m.dRdT / m.R

/-! ## The bias-power linearization — the sign-carrying step -/

/-- **`HasDerivAt` form of the voltage-bias Joule-power linearization.**

For any resistance-vs-temperature curve `Rf` differentiable at the bias temperature `T` with
`Rf T = R₀ ≠ 0`,

    d/dT ( V² / Rf(T) ) = − V² · (dR/dT) / R₀².

The **minus sign is the physics** and it is *derived*, from `HasDerivAt.div`, not asserted:
raising the temperature of a positive-TCR element under voltage bias *reduces* the delivered
Joule power. Everything downstream — the sign of `ℒ`, which side of the dichotomy a bias point
lands on — descends from this one sign. -/
theorem biasPower_hasDerivAt (V : ℝ) (Rf : ℝ → ℝ) {T R' R₀ : ℝ}
    (hR : HasDerivAt Rf R' T) (hR₀ : Rf T = R₀) (hne : R₀ ≠ 0) :
    HasDerivAt (fun τ => V ^ 2 / Rf τ) (-(V ^ 2 * R') / R₀ ^ 2) T := by
  have hd : HasDerivAt (fun τ => V ^ 2 / Rf τ)
      ((0 * Rf T - V ^ 2 * R') / Rf T ^ 2) T :=
    HasDerivAt.fun_div (hasDerivAt_const T (V ^ 2)) hR (by rw [hR₀]; exact hne)
  rw [hR₀] at hd
  convert hd using 1
  ring

/-- **The bias-power linearization** `d(V²/R(T))/dT = −V²·(dR/dT)/R²`, in `deriv` form.

This is the roadmap's sign-carrying Wave-1 brick. Stated over an arbitrary differentiable
resistance curve `Rf`, so it constrains *every* model whose `R`-vs-`T` behaviour has the stated
derivative at the bias point — not a chosen functional form. -/
theorem biasPower_linearization (V : ℝ) (Rf : ℝ → ℝ) {T R' R₀ : ℝ}
    (hR : HasDerivAt Rf R' T) (hR₀ : Rf T = R₀) (hne : R₀ ≠ 0) :
    deriv (fun τ => V ^ 2 / Rf τ) T = -(V ^ 2 * R') / R₀ ^ 2 :=
  (biasPower_hasDerivAt V Rf hR hR₀ hne).deriv

/-- **Why `loopGain` is the right grouping.** The total temperature slope of the linearized
heat-balance right-hand side `P_bias(T) − G·(T − T_bath)` is exactly `−G_eff`:

    d/dT ( V²/R(T) ) − G  =  −G·(1 + ℒ)  =  −G_eff.

The proof **calls** `biasPower_linearization`, so the definition `ℒ = V²·(dR/dT)/(R²·G)` is
justified by a computation rather than by a naming convention: `ℒ` is precisely the dimensionless
ratio that makes the slope factor through `G`. Both `hRne` and `hGne` are used (the factorization
divides by `R²` and by `G`). -/
theorem linearizedSlope_eq_neg_effectiveConductance (m : ETFModel) (Rf : ℝ → ℝ) {T : ℝ}
    (hR : HasDerivAt Rf m.dRdT T) (hR₀ : Rf T = m.R) (hRne : m.R ≠ 0) (hGne : m.G ≠ 0) :
    deriv (fun τ => m.V ^ 2 / Rf τ) T - m.G = -m.effectiveConductance := by
  rw [biasPower_linearization m.V Rf hR hR₀ hRne]
  unfold effectiveConductance loopGain
  field_simp
  ring

/-! ## Loop-gain algebra: signs and conventions -/

/-- **Degenerate branch, disclosed.** At `R = 0` Lean's total division reports loop gain `0` —
the "no feedback, therefore stable" verdict — regardless of `dRdT`. Consumed by
`unstable_imp_dRdT_neg` (to discharge the `R = 0` case as vacuous) and by
`loopGain_R_hypothesis_load_bearing` (to show the resulting verdict is junk, not physics). -/
theorem loopGain_of_R_eq_zero (m : ETFModel) (hR : m.R = 0) : m.loopGain = 0 := by
  unfold loopGain; rw [hR]; simp

/-- **Degenerate branch, disclosed.** At `G = 0` Lean's total division reports loop gain `0`. A
thermally isolated element has no bath conductance to normalize the feedback against, so `ℒ` has
no meaning there; the `0` is a junk value, not the no-feedback limit. -/
theorem loopGain_of_G_eq_zero (m : ETFModel) (hG : m.G = 0) : m.loopGain = 0 := by
  unfold loopGain; rw [hG]; simp

/-- **Agreement with the Irwin–Hilton loop-gain convention.**

    ℒ = P_J · α / (G · T),   P_J = V²/R,   α = (T/R)·(dR/dT).

The instrument literature writes the loop gain in the dimensionless-sensitivity form; this file
writes it in the directly-measurable `V, R, dR/dT` form. They agree — so a reader can check this
file's `ℒ` against the citation graph's `ℒ` without a units argument. Not an unfolding lemma: the
two expressions differ by a genuine cancellation of `T` and one power of `R`.

Hypothesis disclosure. `hTne` is load-bearing for **truth**: at `T = 0` the right-hand side is the
junk `0` while the left-hand side is not. `hRne` is load-bearing for the **proof and the meaning**
but not for truth — at `R = 0` both sides independently collapse to Lean's total-division `0`, so
the identity would survive as a junk-value coincidence carrying no physics. It is kept because
`joulePower = V²/R` and `alphaTCR = T·(dR/dT)/R` are undefined there, and a reader should see the
domain on which the two conventions are being compared. -/
theorem loopGain_eq_irwinHilton (m : ETFModel) {T : ℝ} (hRne : m.R ≠ 0) (hTne : T ≠ 0) :
    m.loopGain = m.joulePower * m.alphaTCR T / (m.G * T) := by
  unfold loopGain joulePower alphaTCR
  rcases eq_or_ne m.G 0 with hG | hG
  · simp [hG]
  · field_simp

/-- **Guardrail 2, as a biconditional: the sign of the loop gain is the sign of `dR/dT`.**

At an admissible bias point (`0 < R`, `0 < G`) with non-zero bias, `ℒ > 0` **iff** `dR/dT > 0`.
So "positive temperature coefficient under voltage bias" and "stabilizing feedback" are the same
statement, and the destabilizing case is exactly the negative-TCR case. The `hV` hypothesis is
load-bearing in the forward-reading direction: at `V = 0` there is no feedback at all (`ℒ = 0`)
whatever `dR/dT` is. -/
theorem loopGain_pos_iff_dRdT_pos (m : ETFModel) (hR : 0 < m.R) (hG : 0 < m.G) (hV : m.V ≠ 0) :
    0 < m.loopGain ↔ 0 < m.dRdT := by
  have hden : 0 < m.R ^ 2 * m.G := by positivity
  have hV2 : 0 < m.V ^ 2 := by positivity
  unfold loopGain
  rw [div_pos_iff_of_pos_right hden]
  exact mul_pos_iff_of_pos_left hV2

/-- The stability boundary in terms of the effective conductance: `G_eff > 0` **iff** `ℒ > −1`.

The algebraic hinge between the *conductance* reading of stability (positive net restoring
conductance) and the *loop-gain* reading (`ℒ > −1`). `0 < G` is load-bearing and its omission
inverts the equivalence — see `stability_G_hypothesis_load_bearing`. -/
theorem effectiveConductance_pos_iff (m : ETFModel) (hG : 0 < m.G) :
    0 < m.effectiveConductance ↔ -1 < m.loopGain := by
  unfold effectiveConductance
  rw [mul_pos_iff_of_pos_left hG]
  constructor <;> intro h <;> linarith

/-! ## The linearized heat balance and its explicit solution -/

/-- **`f` solves the linearized electrothermal heat balance.**

In normalized form `δṪ = −(G_eff/C)·δT`, i.e. `C·δṪ = −G_eff·δT` (see `heatBalance_of_solves`
for that reading, which needs `C ≠ 0`). This is the small-signal balance obtained by expanding
`C·Ṫ = V²/R(T) − G·(T − T_bath)` to first order about the bias point: the right-hand side's
temperature slope is `−G_eff` by `linearizedSlope_eq_neg_effectiveConductance`.

Quantifying the stability predicate over *this* predicate — rather than over the single chosen
exponential — is what makes `etf_stable_iff` a statement about the model rather than about one
trajectory; `solution_unique` shows the two agree. -/
def SolvesHeatBalance (m : ETFModel) (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt f (-(m.effectiveConductance / m.C) * f t) t

/-- The explicit small-signal trajectory `δT(t) = δT₀ · exp(−(G_eff/C)·t)`, i.e.
`δT₀ · exp(−t/τ_eff)` (`perturbation_eq_exp_neg_div_effectiveTimeConstant`).

Written with the *rate* `G_eff/C` rather than with `τ_eff` because `0 < C` is a real hypothesis of
every bias point while `G_eff` may legitimately vanish (the marginal case `ℒ = −1`), where the
`τ_eff` form would divide by zero. The two agree unconditionally nonetheless. -/
noncomputable def perturbation (m : ETFModel) (δT₀ : ℝ) : ℝ → ℝ :=
  fun t => δT₀ * Real.exp (-(m.effectiveConductance / m.C * t))

/-- **The explicit solution is the `τ_eff` form of the roadmap's AC**, unconditionally:

    δT₀ · exp(−(G_eff/C)·t)  =  δT₀ · exp(−t/τ_eff),   τ_eff = C/G_eff.

No hypotheses: Lean's total division makes both sides agree even on the degenerate branches
(`C = 0` or `G_eff = 0`), where both collapse to the constant `δT₀`. -/
theorem perturbation_eq_exp_neg_div_effectiveTimeConstant (m : ETFModel) (δT₀ t : ℝ) :
    m.perturbation δT₀ t = δT₀ * Real.exp (-(t / m.effectiveTimeConstant)) := by
  unfold perturbation effectiveTimeConstant
  rw [div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm t m.effectiveConductance]

/-- **The explicit solution solves the linearized heat balance** (`HasDerivAt` verification,
explicit solution — the `dampedTwoLevel_population_solves_rate` pattern, no ODE-existence
machinery).

Also the **non-vacuity certificate** for `PerturbationsDecay`: solutions always exist, so that
`∀`-quantified predicate is never true for want of a trajectory. -/
theorem etf_perturbation_solves (m : ETFModel) (δT₀ : ℝ) :
    m.SolvesHeatBalance (m.perturbation δT₀) := by
  intro t
  have h : HasDerivAt (fun τ : ℝ => -(m.effectiveConductance / m.C * τ))
      (-(m.effectiveConductance / m.C)) t := by
    simpa using ((hasDerivAt_id t).const_mul (m.effectiveConductance / m.C)).neg
  have h2 := (h.exp).const_mul δT₀
  unfold perturbation
  convert h2 using 1
  ring

/-- The heat balance in its unnormalized, physical reading: `C · δṪ(t) = −G_eff · δT(t)`. -/
theorem heatBalance_of_solves (m : ETFModel) {f : ℝ → ℝ} (hf : m.SolvesHeatBalance f)
    (hC : m.C ≠ 0) (t : ℝ) :
    m.C * deriv f t = -(m.effectiveConductance * f t) := by
  rw [(hf t).deriv]
  field_simp

/-- **The roadmap's Wave-1 ODE statement, with the heat balance spelled out in physical terms.**

    C · d/dt [ δT₀·exp(−t/τ_eff) ]  =  ( d/dT(V²/R(T)) − G ) · δT₀·exp(−t/τ_eff)

— i.e. the explicit solution satisfies the linearized balance written with the **bias-power slope
and the bath conductance separately**, not pre-packaged into `G_eff`. This is the statement a
reader can check against the textbook heat balance line by line, and it is a genuine three-way
bridge: the proof calls `linearizedSlope_eq_neg_effectiveConductance` (which itself calls
`biasPower_linearization`) and `heatBalance_of_solves` (which calls `etf_perturbation_solves`).

The `τ_eff` reading of the left-hand side is
`perturbation_eq_exp_neg_div_effectiveTimeConstant`. -/
theorem etf_perturbation_solves_linearized (m : ETFModel) (Rf : ℝ → ℝ) {T : ℝ}
    (hR : HasDerivAt Rf m.dRdT T) (hR₀ : Rf T = m.R) (hRne : m.R ≠ 0) (hGne : m.G ≠ 0)
    (hC : m.C ≠ 0) (δT₀ t : ℝ) :
    m.C * deriv (m.perturbation δT₀) t
      = (deriv (fun τ => m.V ^ 2 / Rf τ) T - m.G) * m.perturbation δT₀ t := by
  rw [m.linearizedSlope_eq_neg_effectiveConductance Rf hR hR₀ hRne hGne,
    heatBalance_of_solves m (m.etf_perturbation_solves δT₀) hC t]
  ring

/-- **Uniqueness: every solution of the linearized heat balance is the explicit exponential.**

`f t = f 0 · exp(−(G_eff/C)·t)` for any `f` satisfying `SolvesHeatBalance`. Proved by the
elementary integrating-factor argument (`f(t)·exp(rt)` has vanishing derivative, hence is
constant) — no Picard–Lindelöf, no Grönwall.

This is what upgrades `etf_stable_iff` from a statement about one chosen trajectory to a
statement about the model: with uniqueness in hand, quantifying over *all* solutions costs
nothing, and the resulting stability predicate cannot be dismissed as a property of the
particular exponential family that was written down. -/
theorem solution_unique (m : ETFModel) {f : ℝ → ℝ} (hf : m.SolvesHeatBalance f) (t : ℝ) :
    f t = m.perturbation (f 0) t := by
  set r : ℝ := m.effectiveConductance / m.C with hr
  have hg : ∀ s : ℝ, HasDerivAt (fun u : ℝ => f u * Real.exp (r * u)) 0 s := by
    intro s
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (r * u)) (Real.exp (r * s) * (r * 1)) s :=
      (HasDerivAt.const_mul r (hasDerivAt_id s)).exp
    have hmul := (hf s).mul hexp
    convert hmul using 1
    ring
  have hdiff : Differentiable ℝ (fun u : ℝ => f u * Real.exp (r * u)) :=
    fun s => (hg s).differentiableAt
  have hzero : ∀ s : ℝ, deriv (fun u : ℝ => f u * Real.exp (r * u)) s = 0 :=
    fun s => (hg s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero t 0
  simp only [mul_zero, Real.exp_zero, mul_one] at hconst
  have hne : Real.exp (r * t) ≠ 0 := Real.exp_ne_zero _
  unfold perturbation
  rw [← hr]
  rw [← hconst, Real.exp_neg, mul_comm r t]
  field_simp

/-! ## The stability dichotomy -/

/-- **Every solution of the linearized heat balance relaxes to zero.**

Not an alias for `0 < G_eff`: this is a `Tendsto … atTop (𝓝 0)` condition on the actual
trajectories, quantified over every function satisfying `SolvesHeatBalance`. See the module
docstring ("The decay predicate") for why neither direction of `etf_stable_iff` is definitional,
and `etf_perturbation_solves` for non-vacuity. -/
def PerturbationsDecay (m : ETFModel) : Prop :=
  ∀ f : ℝ → ℝ, m.SolvesHeatBalance f → Tendsto f atTop (𝓝 0)

/-- Limit engine for the stable branch: a positive relaxation rate drives the explicit solution
to zero. -/
theorem tendsto_perturbation_of_pos (m : ETFModel) (hr : 0 < m.effectiveConductance / m.C)
    (δT₀ : ℝ) : Tendsto (m.perturbation δT₀) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => m.effectiveConductance / m.C * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hr tendsto_id
  have h2 : Tendsto (fun t : ℝ => -(m.effectiveConductance / m.C * t)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  have h3 := (Real.tendsto_exp_atBot.comp h2).const_mul δT₀
  simpa [perturbation] using h3

/-- **Non-decay engine for the unstable and marginal branches.** A non-positive effective
conductance makes the unit-amplitude explicit solution satisfy `δT(t) ≥ 1` for every `t ≥ 0`, so
it cannot tend to `0` — hence `PerturbationsDecay` fails.

Extracted because *two* results need exactly this argument: the forward direction of
`etf_stable_iff` (where `0 < G` converts `ℒ ≤ −1` into `G_eff ≤ 0`) and
`stability_G_hypothesis_load_bearing` (where `G < 0` produces `G_eff ≤ 0` from `ℒ > −1` — the
sign inversion). Stating it on `G_eff` rather than on `ℒ` is what makes it serve both. -/
theorem not_perturbationsDecay_of_effectiveConductance_nonpos (m : ETFModel) (hC : 0 < m.C)
    (hGeff : m.effectiveConductance ≤ 0) : ¬ m.PerturbationsDecay := by
  intro hdec
  have hrate : m.effectiveConductance / m.C ≤ 0 := div_nonpos_of_nonpos_of_nonneg hGeff hC.le
  have htend := hdec _ (m.etf_perturbation_solves 1)
  have hge : ∀ᶠ t : ℝ in atTop, (1 : ℝ) ≤ m.perturbation 1 t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h0 : 0 ≤ -(m.effectiveConductance / m.C * t) := by
      have := mul_nonpos_of_nonpos_of_nonneg hrate ht
      linarith
    simpa [perturbation] using Real.one_le_exp h0
  have := ge_of_tendsto htend hge
  linarith

/-- **THE DICHOTOMY — an iff, not a sufficient condition.**

Every solution of the linearized electrothermal heat balance relaxes to zero **if and only if**
the loop gain exceeds `−1`:

    (all perturbations decay)  ↔  ℒ > −1.

Equivalently `G_eff = G·(1+ℒ) > 0` (`effectiveConductance_pos_iff`). An operating point with
`ℒ ≤ −1` is unphysical *as modelled*: `etf_diverges_of_loopGain_lt_neg_one` shows the trajectories
run away, and `etf_marginal_of_loopGain_eq_neg_one` shows the boundary case is frozen.

**Both hypotheses are load-bearing.** `0 < C` gives a well-posed relaxation rate; `0 < G` is what
makes `G_eff > 0` equivalent to `ℒ > −1` at all, and its omission *inverts* the criterion
(`stability_G_hypothesis_load_bearing`). Neither direction is a restatement: `←` routes through
`solution_unique`, `→` through the explicit non-decaying witness `perturbation 1`. -/
theorem etf_stable_iff (m : ETFModel) (hC : 0 < m.C) (hG : 0 < m.G) :
    m.PerturbationsDecay ↔ -1 < m.loopGain := by
  constructor
  · intro hdec
    by_contra hcon
    rw [not_lt] at hcon
    have hGeff : m.effectiveConductance ≤ 0 := by
      unfold effectiveConductance
      have h1 : 1 + m.loopGain ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos hG.le h1
    exact m.not_perturbationsDecay_of_effectiveConductance_nonpos hC hGeff hdec
  · intro hL f hf
    have hGeff : 0 < m.effectiveConductance := (m.effectiveConductance_pos_iff hG).mpr hL
    have hr : 0 < m.effectiveConductance / m.C := div_pos hGeff hC
    have hfe : f = m.perturbation (f 0) := funext fun t => m.solution_unique hf t
    rw [hfe]
    exact m.tendsto_perturbation_of_pos hr (f 0)

/-- **The unstable branch, with its physical content: thermal runaway.**

When `ℒ < −1`, every solution with a non-zero initial perturbation has `|δT(t)| → ∞`. This is
strictly stronger than "does not decay" (the bare negation of `etf_stable_iff`): the excursion
grows without bound, which is what makes such an operating point unphysical *as modelled* rather
than merely marginal. -/
theorem etf_diverges_of_loopGain_lt_neg_one (m : ETFModel) (hC : 0 < m.C) (hG : 0 < m.G)
    (hL : m.loopGain < -1) {f : ℝ → ℝ} (hf : m.SolvesHeatBalance f) (hf0 : f 0 ≠ 0) :
    Tendsto (fun t => |f t|) atTop atTop := by
  have hGeff : m.effectiveConductance < 0 := by
    unfold effectiveConductance
    exact mul_neg_of_pos_of_neg hG (by linarith)
  have hr : 0 < -(m.effectiveConductance / m.C) := by
    have : m.effectiveConductance / m.C < 0 := div_neg_of_neg_of_pos hGeff hC
    linarith
  have h1 : Tendsto (fun t : ℝ => -(m.effectiveConductance / m.C * t)) atTop atTop := by
    simp_rw [← neg_mul]
    exact Filter.Tendsto.const_mul_atTop hr tendsto_id
  have h2 : Tendsto (fun t : ℝ => Real.exp (-(m.effectiveConductance / m.C * t))) atTop atTop :=
    Real.tendsto_exp_atTop.comp h1
  have habs : (fun t => |f t|)
      = fun t => |f 0| * Real.exp (-(m.effectiveConductance / m.C * t)) := by
    funext t
    rw [m.solution_unique hf t]
    unfold perturbation
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [habs]
  exact Filter.Tendsto.const_mul_atTop (abs_pos.mpr hf0) h2

/-- **The boundary is frozen, not merely non-decaying.** Exactly at `ℒ = −1` the effective
conductance vanishes and every solution is *constant*: `δT(t) = δT₀` for all `t`. Completing the
trichotomy this way is what makes `etf_stable_iff`'s strict inequality the right cut — the
boundary belongs to neither branch by accident, it is a distinct, exactly characterized regime.

No positivity hypotheses are needed: `G_eff = G·(1 + (−1)) = 0` identically. -/
theorem etf_marginal_of_loopGain_eq_neg_one (m : ETFModel) (hL : m.loopGain = -1)
    {f : ℝ → ℝ} (hf : m.SolvesHeatBalance f) (t : ℝ) : f t = f 0 := by
  have hGeff : m.effectiveConductance = 0 := by
    unfold effectiveConductance; rw [hL]; ring
  rw [m.solution_unique hf t]
  simp [perturbation, hGeff]

/-! ## Time-constant modification -/

/-- **`τ_eff = τ/(1+ℒ)`** — the electrothermal modification of the thermal time constant.

Stated **without hypotheses**: an earlier draft carried `0 < G` and `−1 < ℒ`, but neither is used
— `C/(G·(1+ℒ)) = (C/G)/(1+ℒ)` is `div_div`, and Lean's total division makes it hold on the
degenerate branches too (at `ℒ = −1` both sides are `0`, consistently with
`etf_marginal_of_loopGain_eq_neg_one`'s frozen solution). Carrying unused positivity here would
have been decoration, and would have wrongly suggested the identity is a stability fact. The
*inequality* consequences below (`etf_timeConstant_speedup`, `etf_timeConstant_slowdown`) are
where positivity genuinely bites. -/
theorem effectiveTimeConstant_eq_div (m : ETFModel) :
    m.effectiveTimeConstant = m.timeConstant / (1 + m.loopGain) := by
  unfold effectiveTimeConstant timeConstant effectiveConductance
  rw [div_div]

/-- **Speed-up under stabilizing feedback:** a positive loop gain (equivalently, positive
`dR/dT` under voltage bias — `loopGain_pos_iff_dRdT_pos`) makes the detector strictly *faster*
than its bare thermal time constant, `τ_eff < τ`. -/
theorem etf_timeConstant_speedup (m : ETFModel) (hC : 0 < m.C) (hG : 0 < m.G)
    (hL : 0 < m.loopGain) : m.effectiveTimeConstant < m.timeConstant := by
  have hτ : 0 < m.timeConstant := div_pos hC hG
  rw [m.effectiveTimeConstant_eq_div]
  exact div_lt_self hτ (by linarith)

/-- **Slow-down under destabilizing (but still stable) feedback**, the signed dual: for
`−1 < ℒ < 0` — a negative `dR/dT` too weak to destabilize — the detector is strictly *slower*,
`τ < τ_eff`. Together with `etf_timeConstant_speedup` this makes the direction of the time-constant
shift a signed consequence of `dR/dT`, so no magnitude-only reading of the loop gain can predict
it. -/
theorem etf_timeConstant_slowdown (m : ETFModel) (hC : 0 < m.C) (hG : 0 < m.G)
    (hL : -1 < m.loopGain) (hL0 : m.loopGain < 0) : m.timeConstant < m.effectiveTimeConstant := by
  have hτ : 0 < m.timeConstant := div_pos hC hG
  have h1 : (0 : ℝ) < 1 + m.loopGain := by linarith
  rw [m.effectiveTimeConstant_eq_div]
  rw [lt_div_iff₀ h1]
  nlinarith

/-- **The unstable branch's `τ_eff` is NEGATIVE — a sign, not a small magnitude.**

At `ℒ < −1` the effective time constant `τ_eff = C/G_eff = τ/(1+ℒ)` comes out *negative*. That is
the correct signature: `exp(−t/τ_eff)` with `τ_eff < 0` **grows**
(`etf_diverges_of_loopGain_lt_neg_one`). A consumer that reports `|τ_eff|` — a very natural
"response time" reduction — would read a strongly unstable bias point as a *fast* detector, which
is the magnitude-only inversion Guardrail 2 forbids. Stated so that mistake is checkable.

Note the interaction with `etf_timeConstant_speedup`: a *small* `τ_eff` is desirable only on the
stable branch, and `0 < τ_eff` there is exactly what `etf_stable_iff` certifies. -/
theorem effectiveTimeConstant_neg_of_unstable (m : ETFModel) (hC : 0 < m.C) (hG : 0 < m.G)
    (hL : m.loopGain < -1) : m.effectiveTimeConstant < 0 := by
  have h1 : 1 + m.loopGain < 0 := by linarith
  have hGeff : m.effectiveConductance < 0 := mul_neg_of_pos_of_neg hG h1
  exact div_neg_of_pos_of_neg hC hGeff

/-! ## Guardrail 2 discharged: signs decide, magnitudes do not -/

/-- **Instability under voltage bias requires a negative temperature coefficient.**

If the model is not stable then `dR/dT < 0`. So the runaway branch is not reachable from a
positive-TCR element under voltage bias at all — the stabilizing/destabilizing dichotomy is
governed by the *sign* of `dR/dT`, exactly as Guardrail 2 requires.

Note the hypothesis list: no `V ≠ 0` is needed, because `V = 0` forces `ℒ = 0 > −1`, i.e. an
unbiased element is automatically stable. -/
theorem unstable_imp_dRdT_neg (m : ETFModel) (hC : 0 < m.C) (hG : 0 < m.G)
    (hun : ¬ m.PerturbationsDecay) : m.dRdT < 0 := by
  have hL : m.loopGain ≤ -1 := not_lt.mp fun h => hun ((m.etf_stable_iff hC hG).mpr h)
  rcases eq_or_ne m.R 0 with hR | hR
  · rw [m.loopGain_of_R_eq_zero hR] at hL
    linarith
  · have hLneg : m.loopGain < 0 := by linarith
    have hR2 : 0 < m.R ^ 2 := by positivity
    have hden : 0 < m.R ^ 2 * m.G := mul_pos hR2 hG
    unfold loopGain at hLneg
    have hnum : m.V ^ 2 * m.dRdT < 0 := by
      have h := (div_lt_iff₀ hden).mp hLneg
      linarith
    nlinarith [sq_nonneg m.V]

/-- **A magnitude-only stability criterion is UNSOUND — the phase's target defect, refuted.**

There is a model that is **unstable**, and whose `|dR/dT|` twin — identical in `C`, `G`, `R`, `V`
and in the *magnitude* of `dR/dT` — is **stable**. So any criterion phrased on `|dR/dT|`, or on
any quantity that discards the sign of `dR/dT`, returns the *opposite* verdict on this model: not
a loose bound, an inverted one.

Witness: `C = G = R = 1`, `V = 2`, `dR/dT = −1/2` gives `ℒ = −2 < −1` (unstable), while
`dR/dT = +1/2` gives `ℒ = +2 > −1` (stable, and in fact *faster* than the bare time constant).

This is Guardrail 2 ("no magnitude-only shortcuts") discharged as a theorem rather than left as a
review instruction; `absLoopGain_criterion_unsound` closes the same guardrail one level
downstream, on `|ℒ|` itself. -/
theorem magnitudeOnly_criterion_unsound :
    ∃ m : ETFModel, 0 < m.C ∧ 0 < m.G ∧ 0 < m.R ∧
      ¬ m.PerturbationsDecay ∧ ({ m with dRdT := |m.dRdT| } : ETFModel).PerturbationsDecay := by
  refine ⟨⟨1, 1, 1, 2, -(1/2)⟩, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [etf_stable_iff _ (by norm_num) (by norm_num)]
    unfold loopGain
    norm_num
  · rw [etf_stable_iff _ (by norm_num) (by norm_num)]
    unfold loopGain
    norm_num

/-- **`|ℒ|` cannot decide stability either — the same guardrail, one level downstream.**

Two admissible bias points with *exactly the same* `|ℒ| = 2` land on **opposite** sides of the
dichotomy: `ℒ = −2` runs away, `ℒ = +2` relaxes (four times faster than its bare `τ`, in fact).
So a screen of the form "`|ℒ| ≤ ℒ_max` ⟹ safe operating point" — a natural-looking magnitude
budget — is not conservative; it is simply wrong, in both directions.

Distinct from `magnitudeOnly_criterion_unsound`, which refutes sign-erasure at the *input*
(`dR/dT`); this refutes it at the *derived quantity* a consumer is most likely to tabulate. -/
theorem absLoopGain_criterion_unsound :
    ∃ m m' : ETFModel, |m.loopGain| = |m'.loopGain| ∧
      ¬ m.PerturbationsDecay ∧ m'.PerturbationsDecay := by
  refine ⟨⟨1, 1, 1, 2, -(1/2)⟩, ⟨1, 1, 1, 2, 1/2⟩, ?_, ?_, ?_⟩
  · unfold loopGain
    norm_num
  · rw [etf_stable_iff _ (by norm_num) (by norm_num)]
    unfold loopGain
    norm_num
  · rw [etf_stable_iff _ (by norm_num) (by norm_num)]
    unfold loopGain
    norm_num

/-! ## Load-bearing hypotheses: the degenerate branches, disclosed -/

/-- **The `0 < R` hypothesis cannot be dropped by a consumer.**

A model with `R = 0` and a strongly destabilizing `dR/dT < 0` nonetheless reports `ℒ = 0` and is
certified *stable* by `etf_stable_iff` — a junk verdict produced by Lean's total division, not by
physics. Any consuming statement that reads a physical meaning into `ℒ` must therefore carry
`0 < R` explicitly. (Physically there is no resistive bias point at `R = 0`: the voltage-biased
Joule power `V²/R` is not defined there.) -/
theorem loopGain_R_hypothesis_load_bearing :
    ∃ m : ETFModel, m.R = 0 ∧ m.dRdT < 0 ∧ m.loopGain = 0 ∧ m.PerturbationsDecay := by
  refine ⟨⟨1, 1, 0, 2, -(1/2)⟩, rfl, by norm_num, ?_, ?_⟩
  · unfold loopGain; norm_num
  · rw [etf_stable_iff _ (by norm_num) (by norm_num)]
    unfold loopGain
    norm_num

/-- **The `0 < G` hypothesis of `etf_stable_iff` cannot be dropped — dropping it INVERTS the
criterion.**

Exhibits a model with `0 < C` and `ℒ > −1` — the "stable" side of the dichotomy — that
nonetheless fails to decay, because `G < 0` flips the sign of `G_eff = G·(1+ℒ)`. So `0 < G` is not
decoration on `etf_stable_iff`: without it the biconditional is false in the strongest sense (the
loop-gain test reports the opposite verdict).

Witness: `C = 1`, `G = −1`, `R = 1`, `V = 0`, `dR/dT = 0`, so `ℒ = 0 > −1` while `G_eff = −1 < 0`
and the constant-`1` initial perturbation grows like `exp(t)`. -/
theorem stability_G_hypothesis_load_bearing :
    ∃ m : ETFModel, 0 < m.C ∧ m.G < 0 ∧ -1 < m.loopGain ∧ ¬ m.PerturbationsDecay := by
  refine ⟨⟨1, -1, 1, 0, 0⟩, by norm_num, by norm_num, ?_, ?_⟩
  · unfold loopGain; norm_num
  · refine not_perturbationsDecay_of_effectiveConductance_nonpos _ (by norm_num) ?_
    unfold effectiveConductance loopGain
    norm_num

/-! ## Worked operating points: both sides of the dichotomy boundary -/

/-- Worked bias point on the **stable** side, `ℒ = −1/2`: a mildly negative-TCR element whose
feedback is too weak to destabilize. `G_eff = 1/2`, so `τ_eff = 2 > τ = 1` (slowed down). -/
noncomputable def stableWitness : ETFModel := ⟨1, 1, 1, 1, -(1/2)⟩

/-- Worked bias point **exactly on** the boundary, `ℒ = −1`: `G_eff = 0` and the perturbation is
frozen. -/
noncomputable def marginalWitness : ETFModel := ⟨1, 1, 1, 2, -(1/4)⟩

/-- Worked bias point on the **unstable** side, `ℒ = −2`: `G_eff = −1` and every non-zero
perturbation runs away. -/
noncomputable def unstableWitness : ETFModel := ⟨1, 1, 1, 2, -(1/2)⟩

/-- Worked bias point with **stabilizing** feedback, `ℒ = +3` (positive `dR/dT`): `G_eff = 4`, so
`τ_eff = 1/4`, a fourfold speed-up over the bare `τ = 1`. -/
noncomputable def speedupWitness : ETFModel := ⟨1, 1, 1, 1, 3⟩

/-- `norm_num` witness, stable side: `ℒ = −1/2 > −1` and the model decays. -/
theorem stableWitness_loopGain : stableWitness.loopGain = -(1/2) := by
  unfold loopGain stableWitness; norm_num

/-- `norm_num` witness, stable side of the boundary: perturbations decay. -/
theorem stableWitness_decays : stableWitness.PerturbationsDecay := by
  rw [etf_stable_iff _ (by norm_num [stableWitness]) (by norm_num [stableWitness])]
  rw [stableWitness_loopGain]; norm_num

/-- `norm_num` witness, unstable side: `ℒ = −2 < −1`. -/
theorem unstableWitness_loopGain : unstableWitness.loopGain = -2 := by
  unfold loopGain unstableWitness; norm_num

/-- `norm_num` witness, unstable side of the boundary: perturbations do **not** decay. Together
with `stableWitness_decays` this straddles the dichotomy boundary with concrete, checkable
numbers — the boundary is not an artefact of the abstract statement. -/
theorem unstableWitness_not_decays : ¬ unstableWitness.PerturbationsDecay := by
  rw [etf_stable_iff _ (by norm_num [unstableWitness]) (by norm_num [unstableWitness])]
  rw [unstableWitness_loopGain]; norm_num

/-- `norm_num` witness **exactly at** the boundary: `ℒ = −1`, so every solution is frozen at its
initial value. Pins the dichotomy's strict inequality to a concrete model. -/
theorem marginalWitness_loopGain : marginalWitness.loopGain = -1 := by
  unfold loopGain marginalWitness; norm_num

/-- At the boundary witness every solution is constant — the third branch, witnessed. -/
theorem marginalWitness_frozen {f : ℝ → ℝ} (hf : marginalWitness.SolvesHeatBalance f) (t : ℝ) :
    f t = f 0 :=
  etf_marginal_of_loopGain_eq_neg_one _ marginalWitness_loopGain hf t

/-- `norm_num` witness of the speed-up: at `ℒ = 3` the effective time constant is `1/4` of the
bare thermal time constant `τ = 1`. Quantitative, not qualitative: the value is named, so the
statement is falsifiable by arithmetic. -/
theorem speedupWitness_timeConstants :
    speedupWitness.timeConstant = 1 ∧ speedupWitness.effectiveTimeConstant = 1/4 := by
  constructor
  · unfold timeConstant speedupWitness; norm_num
  · unfold effectiveTimeConstant effectiveConductance loopGain speedupWitness; norm_num

/-- The speed-up theorem, instantiated: `τ_eff < τ` at the worked positive-`dR/dT` point. -/
theorem speedupWitness_speedup :
    speedupWitness.effectiveTimeConstant < speedupWitness.timeConstant := by
  refine etf_timeConstant_speedup _ (by norm_num [speedupWitness]) (by norm_num [speedupWitness]) ?_
  unfold loopGain speedupWitness; norm_num

/-- **Rational enclosure of the relaxation, no floating-point `exp`.**

At the stable worked point (`G_eff = 1/2`, `C = 1`) one bare thermal time constant after a unit
perturbation, the remaining excursion is `e^{−1/2}`, bracketed by the project's Bernoulli
enclosure `SKEFTHawking.QuantumNetwork.expNeg_enclosure` at `r = 1/2`:

    1/2  ≤  δT(1)  ≤  2/3.

A real call to the cited brick (not a docstring reference), following the `NumericalBounds`
rational-enclosure pattern and matching
`SKEFTHawking.OpenSystems.dampedTwoLevel_decay_envelope_half`. -/
theorem stableWitness_decay_enclosure :
    (1/2 : ℝ) ≤ stableWitness.perturbation 1 1 ∧ stableWitness.perturbation 1 1 ≤ 2/3 := by
  have hval : stableWitness.perturbation 1 1 = Real.exp (-(1/2 : ℝ)) := by
    unfold perturbation effectiveConductance loopGain stableWitness
    norm_num
  have h := SKEFTHawking.QuantumNetwork.expNeg_enclosure (r := (1/2 : ℝ)) (by norm_num)
  rw [hval]
  constructor
  · linarith [h.1]
  · linarith [h.2]

end ETFModel

end SKEFTHawking.Electrothermal
