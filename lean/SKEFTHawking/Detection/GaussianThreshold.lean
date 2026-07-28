import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound

/-!
# Gaussian threshold discrimination algebra (Phase 6EA, Wave 2)

Exact error algebra for two-Gaussian threshold classification at common variance, with honest
tail enclosures replacing the un-formalized Q-function, and the separation-budget error floor
every downstream readout ceiling consumes.

**Mathlib carries no `erf` / `erfc` / Gaussian CDF / Q-function at pin `5e932f97`** (verified by
declaration-level grep, 2026-07-27; re-verified 2026-07-28). The upper-tail probability
`gaussianQ` is therefore defined here, project-locally, as the tail integral of Mathlib's
`ProbabilityTheory.gaussianPDFReal 0 1`; every bound below is proved about *that* definition,
whose normalization is pinned to Mathlib's own Gaussian integral by `gaussianQ_zero`.

## Layout

* **Definitions** — `gaussianQ`, and the two branch errors `thrErr0` / `thrErr1` of a threshold
  classifier with baseline mean `μ₀`, signal mean `μ₁`, common standard deviation `σ > 0`,
  threshold `t`.
* **Standard-normal pdf helpers** — closed form, evenness, antitonicity in `x²`, integrability.
* **Structural lemmas** — `gaussianQ_zero` (`= 1/2`, from `Real.integral_gaussian_Ioi`),
  `gaussianQ_sub` (the interval-integral workhorse), monotonicity, reflection, range.
* **Tail bounds** — the lower tails `gaussianTail_ge_window` (global, parametric window) and
  `gaussianTail_birnbaum` (sharp), and the upper tails `gaussianTail_mills`,
  `gaussianTail_chernoff`. `gaussianPDF_moment_Ioi` (`∫_{(z,∞)} x·φ(x) dx = φ(z)`) is the shared
  workhorse for Mills and Birnbaum.
* **Rational witnesses** — `gaussianQ_two_le_rational` / `gaussianQ_two_ge_rational` bracket
  `Q(2)` between two rationals with no floating-point `exp`, in the project's
  `NumericalBounds` rational-enclosure style; `gaussianQ_two_le_rational` consumes
  `SKEFTHawking.QuantumNetwork.expNeg_enclosure` directly.
* **Threshold algebra** — conservativity in `σ`, the ROC tradeoff in `t`, midpoint symmetry.
* **Error floors** — `avgError_ge_gaussianQ_sharp`, stated in the project's canonical error
  functional `SKEFTHawking.QuantumNetwork.avgAssignmentError`.

## Statement-freeze deviations (all in the strengthening direction)

* **Lower tail (Stage-2 `UNKNOWN-2`).** The interval-restricted rational form
  `Q z ≥ 1/2 − z/√(2π)` is **settled-dead for this phase**: it is negative — hence vacuous —
  for `z > √(2π)/2 ≈ 1.2533`, which is exactly where every consumer operates. It is not
  re-derived here. The must-ship is `gaussianTail_ge_window`; the sharp Birnbaum/Feller form
  `gaussianTail_birnbaum` also closed and is shipped alongside it.
* **Chernoff (Stage-2 `D7`).** The frozen fallback was the narrowed `0.8 ≤ z` form. The full
  `0 ≤ z` statement closed and is what ships as `gaussianTail_chernoff`; the narrowed form is
  not shipped, since it would be a strictly weaker restatement of a proved theorem.
* **Threshold floor (Stage-2 `D10`).** The accepted must-ship constant was `½·Q(z₀)`. The sharp
  `Q(z₀)` form closed, so only `avgError_ge_gaussianQ_sharp` ships: at an identical hypothesis
  list, the half form would be a strictly weaker restatement provable in one `linarith` from the
  sharp one — the identity-wrapper pattern the strengthening checklist forbids. See the note at
  the end of this file. This strengthens the AC rather than descoping it.

**⚠ Guardrail (inherited).** Everything below is a floor or screen on *any* threshold detector,
stated over abstract means and an abstract noise scale. No device claim, no hardware model, no
platform assertion. Physically identifying `μ₀`, `μ₁`, `σ` with measured quantities is the
consuming phase's declared hypothesis and is never smuggled into these statements.

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology*.
-/

namespace SKEFTHawking.Detection

open ProbabilityTheory Real MeasureTheory SKEFTHawking.QuantumNetwork

/-! ## Definitions -/

/-- **Standard-normal upper-tail probability** `Q(z) = ∫_{(z,∞)} φ`. Mathlib carries no
`erf` / `erfc` / Gaussian CDF / Q-function at pin `5e932f97` (verified 2026-07-27), so this is
necessarily project-local; `gaussianQ_zero` pins its normalization to Mathlib's own
`Real.integral_gaussian_Ioi`. -/
noncomputable def gaussianQ (z : ℝ) : ℝ := ∫ x in Set.Ioi z, gaussianPDFReal 0 1 x

/-- False-alarm branch error of a threshold classifier with baseline mean `μ₀`, common standard
deviation `σ`, and threshold `t`: the probability that a baseline draw lands above `t`. -/
noncomputable def thrErr0 (μ₀ σ t : ℝ) : ℝ := gaussianQ ((t - μ₀) / σ)

/-- Miss branch error of the same classifier with signal mean `μ₁`: the probability that a
signal draw lands below `t`. -/
noncomputable def thrErr1 (μ₁ σ t : ℝ) : ℝ := gaussianQ ((μ₁ - t) / σ)

/-! ## Standard-normal pdf helpers -/

/-- Closed form of the standard normal pdf: `φ(x) = (2π)^(−1/2)·exp(−x²/2)`. -/
theorem gaussianPDF_std (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- `gaussianPDF_std` with the exponent in the `-b·x²` shape Mathlib's Gaussian-integral API
expects (`b = 1/2`). -/
theorem gaussianPDF_std' (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  rw [gaussianPDF_std]
  ring_nf

/-- The standard normal pdf is even. -/
theorem gaussianPDF_neg (x : ℝ) : gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp [gaussianPDF_std]

/-- The standard normal pdf is antitone in the square of its argument. This single statement
carries both "antitone on `[0,∞)`" and the shifted comparison `|y − 2h| ≤ |y| ⟹ φ(y) ≤ φ(y−2h)`
used by the sharp threshold floor. -/
theorem gaussianPDF_le_of_sq_le {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) :
    gaussianPDFReal 0 1 b ≤ gaussianPDFReal 0 1 a := by
  rw [gaussianPDF_std, gaussianPDF_std]
  have hpos : (0 : ℝ) < (√(2 * π))⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hpos.le

/-- The standard normal pdf is integrable on every set (it is globally integrable). -/
theorem gaussianPDF_integrableOn (s : Set ℝ) : IntegrableOn (gaussianPDFReal 0 1) s :=
  (integrable_gaussianPDFReal 0 1).integrableOn

/-! ## Structural lemmas for `gaussianQ` -/

/-- **`Q(0) = 1/2`.** This is what pins the project-local `gaussianQ` to Mathlib's own Gaussian
normalization: it is `Real.integral_gaussian_Ioi` at `b = 1/2`, so no independent normalization
constant is introduced anywhere in this file. -/
theorem gaussianQ_zero : gaussianQ 0 = 1 / 2 := by
  rw [gaussianQ]
  simp_rw [gaussianPDF_std']
  rw [integral_const_mul, integral_gaussian_Ioi]
  rw [show π / (1 / 2 : ℝ) = 2 * π by ring]
  have hpos : (0:ℝ) < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- Ordered form of the interval-integral workhorse: `Q(a) − Q(b) = ∫_a^b φ` for `a ≤ b`. -/
theorem gaussianQ_sub_of_le {a b : ℝ} (hab : a ≤ b) :
    gaussianQ a - gaussianQ b = ∫ x in a..b, gaussianPDFReal 0 1 x := by
  have hdisj : Disjoint (Set.Ioc a b) (Set.Ioi b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.mpr hx')
  have hsplit : gaussianQ a = (∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x) + gaussianQ b := by
    rw [gaussianQ, gaussianQ, ← Set.Ioc_union_Ioi_eq_Ioi hab]
    exact setIntegral_union hdisj measurableSet_Ioi (gaussianPDF_integrableOn _)
      (gaussianPDF_integrableOn _)
  rw [hsplit, intervalIntegral.integral_of_le hab]
  ring

/-- **The interval-integral workhorse**: `Q(a) − Q(b) = ∫_a^b φ`, for arbitrary `a`, `b`. Every
structural lemma below and the sharp threshold floor route through this identity, which converts
tail differences into interval integrals where Mathlib's comparison API applies. -/
theorem gaussianQ_sub (a b : ℝ) :
    gaussianQ a - gaussianQ b = ∫ x in a..b, gaussianPDFReal 0 1 x := by
  rcases le_total a b with hab | hab
  · exact gaussianQ_sub_of_le hab
  · rw [intervalIntegral.integral_symm, ← gaussianQ_sub_of_le hab]
    ring

/-- `0 ≤ Q z`. -/
theorem gaussianQ_nonneg (z : ℝ) : 0 ≤ gaussianQ z :=
  setIntegral_nonneg measurableSet_Ioi fun x _ => gaussianPDFReal_nonneg 0 1 x

/-- **`Q` is antitone**: the tail mass shrinks as the cut moves right. -/
theorem gaussianQ_antitone : Antitone gaussianQ := by
  intro a b hab
  have h := gaussianQ_sub_of_le hab
  have hpos : 0 ≤ ∫ x in a..b, gaussianPDFReal 0 1 x :=
    intervalIntegral.integral_nonneg hab fun x _ => gaussianPDFReal_nonneg 0 1 x
  linarith

/-- **Reflection**: `Q(−z) = 1 − Q(z)`. Needed to write the miss branch as a `Q` value. -/
theorem gaussianQ_neg (z : ℝ) : gaussianQ (-z) = 1 - gaussianQ z := by
  have h1 : gaussianQ (-z) - gaussianQ 0 = ∫ x in (-z)..(0:ℝ), gaussianPDFReal 0 1 x :=
    gaussianQ_sub _ _
  have h2 : gaussianQ 0 - gaussianQ z = ∫ x in (0:ℝ)..z, gaussianPDFReal 0 1 x :=
    gaussianQ_sub _ _
  have h3 : (∫ x in (0:ℝ)..z, gaussianPDFReal 0 1 x)
      = ∫ x in (-z)..(0:ℝ), gaussianPDFReal 0 1 x := by
    have hc := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := z) (gaussianPDFReal 0 1)
    simpa [gaussianPDF_neg] using hc
  rw [gaussianQ_zero] at h1 h2
  linarith [h1, h2, h3]

/-- `Q z ≤ 1/2` for `z ≥ 0`. -/
theorem gaussianQ_le_half {z : ℝ} (hz : 0 ≤ z) : gaussianQ z ≤ 1 / 2 := by
  rw [← gaussianQ_zero]
  exact gaussianQ_antitone hz

/-- `Q(a) = 1/2 − ∫_0^a φ`, the centred form of `gaussianQ_sub`. -/
theorem gaussianQ_eq_half_sub (z : ℝ) :
    gaussianQ z = 1 / 2 - ∫ x in (0:ℝ)..z, gaussianPDFReal 0 1 x := by
  have h := gaussianQ_sub 0 z
  rw [gaussianQ_zero] at h
  linarith

/-! ## Tail bounds -/

/-- **Window lower bound on the Gaussian upper tail.** For every `z ≥ 0` and every window width
`c > 0`, `Q z ≥ c·φ(z + c)`. Global in `z`, parametric in `c`, no side condition: each consumer
picks its own `c`. The exponential order `exp(−z²/2)` is exact; only a bounded constant is lost
against the sharp bound (at `z = 3`, `c = 1/3` the bound returns `5.14e−4` against the true
`1.35e−3`). This replaces the Stage-2-rejected interval-restricted rational form, which is
vacuous for `z > √(2π)/2 ≈ 1.2533` — inside every consumer's operating range. -/
theorem gaussianTail_ge_window {z c : ℝ} (hz : 0 ≤ z) (hc : 0 < c) :
    c * gaussianPDFReal 0 1 (z + c) ≤ gaussianQ z := by
  have hzc : z ≤ z + c := by linarith
  have hmono : (∫ _x in z..(z + c), gaussianPDFReal 0 1 (z + c))
      ≤ ∫ x in z..(z + c), gaussianPDFReal 0 1 x := by
    refine intervalIntegral.integral_mono_on hzc intervalIntegrable_const
      (integrable_gaussianPDFReal 0 1).intervalIntegrable ?_
    intro x hx
    exact gaussianPDF_le_of_sq_le (by nlinarith [hx.1, hx.2])
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hsub := gaussianQ_sub_of_le hzc
  have hnn := gaussianQ_nonneg (z + c)
  have hcc : z + c - z = c := by ring
  rw [hcc] at hmono
  linarith

/-- `−φ` is an antiderivative of `x·φ(x)`: `(−φ)'(x) = x·φ(x)`. -/
theorem hasDerivAt_neg_gaussianPDF (x : ℝ) :
    HasDerivAt (fun y => -gaussianPDFReal 0 1 y) (x * gaussianPDFReal 0 1 x) x := by
  have hfun : (fun y => -gaussianPDFReal 0 1 y)
      = fun y => -((√(2 * π))⁻¹ * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) := by
    funext y; rw [gaussianPDF_std']
  rw [hfun]
  have h1 : HasDerivAt (fun y : ℝ => -(1 / 2 : ℝ) * y ^ 2) (-x) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul (-(1 / 2 : ℝ))
  have h3 := ((h1.exp).const_mul ((√(2 * π))⁻¹)).neg
  convert h3 using 1
  rw [gaussianPDF_std']
  ring

/-- `x ↦ x·φ(x)` is globally integrable. -/
theorem integrable_mul_gaussianPDF :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hfun : (fun x : ℝ => x * gaussianPDFReal 0 1 x)
      = fun x : ℝ => (√(2 * π))⁻¹ * (x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    funext x; rw [gaussianPDF_std']; ring
  rw [hfun]
  exact (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul _

/-- `−φ(x) → 0` as `x → ∞`. -/
theorem tendsto_neg_gaussianPDF_atTop :
    Filter.Tendsto (fun x => -gaussianPDFReal 0 1 x) Filter.atTop (nhds 0) := by
  have hsq : Filter.Tendsto (fun x : ℝ => (1/2 : ℝ) * x ^ 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) (Filter.tendsto_pow_atTop two_ne_zero)
  have h1 : Filter.Tendsto (fun x : ℝ => -((1/2 : ℝ) * x ^ 2)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hsq
  have h2 : Filter.Tendsto (fun x : ℝ => Real.exp (-((1/2 : ℝ) * x ^ 2))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h1
  have h3 := (h2.const_mul ((√(2 * π))⁻¹)).neg
  simp only [mul_zero, neg_zero] at h3
  refine h3.congr fun x => ?_
  rw [gaussianPDF_std']
  ring_nf

/-- **The shared tail-moment workhorse**: `∫_{(z,∞)} x·φ(x) dx = φ(z)`, from FTC-2 on a
half-infinite interval with antiderivative `−φ`. Both `gaussianTail_mills` and
`gaussianTail_birnbaum` are consequences of this identity. -/
theorem gaussianPDF_moment_Ioi (z : ℝ) :
    ∫ x in Set.Ioi z, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 z := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun x => -gaussianPDFReal 0 1 x) (f' := fun x => x * gaussianPDFReal 0 1 x)
    (a := z) (m := 0) (fun x _ => hasDerivAt_neg_gaussianPDF x)
    integrable_mul_gaussianPDF.integrableOn tendsto_neg_gaussianPDF_atTop
  simpa using h

/-- **Mills' ratio upper bound**: `Q z ≤ φ(z)/z` for `z > 0`. Proof: `φ(x) ≤ (x/z)·φ(x)` on
`(z,∞)`, then `gaussianPDF_moment_Ioi`. -/
theorem gaussianTail_mills {z : ℝ} (hz : 0 < z) :
    gaussianQ z ≤ gaussianPDFReal 0 1 z / z := by
  have hint : IntegrableOn (fun x : ℝ => z⁻¹ * (x * gaussianPDFReal 0 1 x)) (Set.Ioi z) :=
    (integrable_mul_gaussianPDF.const_mul z⁻¹).integrableOn
  have hmono : (∫ x in Set.Ioi z, gaussianPDFReal 0 1 x)
      ≤ ∫ x in Set.Ioi z, z⁻¹ * (x * gaussianPDFReal 0 1 x) := by
    refine setIntegral_mono_on (gaussianPDF_integrableOn _) hint measurableSet_Ioi ?_
    intro x hx
    have hx' : z ≤ x := le_of_lt hx
    have h1 : 1 ≤ z⁻¹ * x := by
      rw [show z⁻¹ * x = x / z by ring, le_div_iff₀ hz]
      linarith
    nlinarith [gaussianPDFReal_nonneg 0 1 x]
  rw [integral_const_mul, gaussianPDF_moment_Ioi] at hmono
  rw [gaussianQ, div_eq_inv_mul]
  exact hmono

/-- **Chernoff upper tail, unrestricted in `z`**: `Q z ≤ ½·exp(−z²/2)` for every `z ≥ 0`.

The Stage-2 freeze specified a narrowed `0.8 ≤ z` fallback because the exact constant near the
origin was expected to need a monotone-derivative argument. It does not: splitting at the exact
crossover `z = 2/√(2π)` (where Mills' `1/(z√(2π)) ≤ 1/2` turns over) makes the two branches meet
with no numerical slack and no `π` estimate at all.

* For `z ≥ 2/√(2π)` the claim is Mills' ratio plus `2 ≤ z·√(2π)`.
* For `z ≤ 2/√(2π)` it is the pointwise density comparison `(x/2)·exp(−x²/2) ≤ φ(x)` on `[0, z]`
  — valid exactly while `x ≤ 2/√(2π)` — integrated against `Q z = 1/2 − ∫_0^z φ`, using that
  `x ↦ −½·exp(−x²/2)` is an antiderivative of `(x/2)·exp(−x²/2)`. -/
theorem gaussianTail_chernoff {z : ℝ} (hz : 0 ≤ z) :
    gaussianQ z ≤ (1 / 2) * Real.exp (-z ^ 2 / 2) := by
  have hs : (0:ℝ) < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  rcases le_total z (2 / √(2 * π)) with hcase | hcase
  · -- Small-`z` branch: pointwise density comparison on `[0, z]`.
    have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -(1/2 : ℝ) * Real.exp (-y ^ 2 / 2))
        ((x / 2) * Real.exp (-x ^ 2 / 2)) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
        simpa [neg_div] using ((hasDerivAt_pow 2 x).neg.div_const 2)
      have h2 := (h1.exp).const_mul (-(1/2 : ℝ))
      convert h2 using 1
      ring
    have hcont : Continuous (fun x : ℝ => (x / 2) * Real.exp (-x ^ 2 / 2)) := by fun_prop
    have hval : (∫ x in (0:ℝ)..z, (x / 2) * Real.exp (-x ^ 2 / 2))
        = 1 / 2 - (1 / 2) * Real.exp (-z ^ 2 / 2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        (hcont.intervalIntegrable 0 z)]
      simp
      ring
    have hkey : (∫ x in (0:ℝ)..z, (x / 2) * Real.exp (-x ^ 2 / 2))
        ≤ ∫ x in (0:ℝ)..z, gaussianPDFReal 0 1 x := by
      refine intervalIntegral.integral_mono_on hz (hcont.intervalIntegrable 0 z)
        (integrable_gaussianPDFReal 0 1).intervalIntegrable ?_
      intro x hx
      rw [gaussianPDF_std]
      have hxz : x ≤ 2 / √(2 * π) := le_trans hx.2 hcase
      have hxs : x * √(2 * π) ≤ 2 := by rwa [le_div_iff₀ hs] at hxz
      have hinv : (√(2 * π))⁻¹ * √(2 * π) = 1 := inv_mul_cancel₀ (ne_of_gt hs)
      have hhalf : x / 2 ≤ (√(2 * π))⁻¹ := by nlinarith [inv_pos.mpr hs]
      nlinarith [Real.exp_pos (-x ^ 2 / 2)]
    rw [gaussianQ_eq_half_sub]
    linarith
  · -- Large-`z` branch: Mills' ratio.
    have hzpos : 0 < z := lt_of_lt_of_le (by positivity) hcase
    have hkey : 2 ≤ z * √(2 * π) := by rwa [div_le_iff₀ hs] at hcase
    have hE : (0:ℝ) < Real.exp (-z ^ 2 / 2) := Real.exp_pos _
    have hmills := gaussianTail_mills hzpos
    rw [gaussianPDF_std] at hmills
    refine hmills.trans ?_
    rw [div_le_iff₀ hzpos]
    have hinv : (√(2 * π))⁻¹ * √(2 * π) = 1 := inv_mul_cancel₀ (ne_of_gt hs)
    have h2 : (√(2 * π))⁻¹ ≤ z / 2 := by nlinarith [inv_pos.mpr hs]
    nlinarith

/-- `φ(x)/x²` is integrable on `(z,∞)` for `z > 0`, by domination by `φ(x)/z²`. -/
theorem integrableOn_gaussianPDF_div_sq {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun x : ℝ => gaussianPDFReal 0 1 x / x ^ 2) (Set.Ioi z) := by
  have hg : IntegrableOn (fun x : ℝ => gaussianPDFReal 0 1 x / z ^ 2) (Set.Ioi z) := by
    simpa [div_eq_mul_inv] using ((gaussianPDF_integrableOn (Set.Ioi z)).mul_const (z ^ 2)⁻¹)
  refine hg.mono' ?_ ?_
  · exact ((measurable_gaussianPDFReal 0 1).div (measurable_id.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans hz hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (gaussianPDFReal_nonneg 0 1 x) (sq_nonneg x))]
    gcongr
    · exact gaussianPDFReal_nonneg 0 1 x
    · exact le_of_lt hx

/-- `−φ(x)/x` is an antiderivative of `φ(x)·(1 + 1/x²)` on `(0,∞)`. -/
theorem hasDerivAt_mills {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -gaussianPDFReal 0 1 y / y)
      (gaussianPDFReal 0 1 x + gaussianPDFReal 0 1 x / x ^ 2) x := by
  have hd1 : HasDerivAt (fun y : ℝ => -gaussianPDFReal 0 1 y) (x * gaussianPDFReal 0 1 x) x :=
    hasDerivAt_neg_gaussianPDF x
  have hd2 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h := hd1.div hd2 (ne_of_gt hx)
  convert h using 1
  field_simp
  ring

/-- `−φ(y)/y → 0` as `y → ∞`. -/
theorem tendsto_mills_atTop :
    Filter.Tendsto (fun y : ℝ => -gaussianPDFReal 0 1 y / y) Filter.atTop (nhds 0) :=
  tendsto_neg_gaussianPDF_atTop.div_atTop Filter.tendsto_id

/-- **Birnbaum/Feller sharp lower tail**: `Q z ≥ (z/(1+z²))·φ(z)` for `z > 0`. At `z = 3` this
returns `1.3296e−3` against the true `1.3499e−3` (ratio `0.985`), versus the window bound's
factor-2.6 constant loss. Substituting this for `gaussianTail_ge_window` in a consumer requires
no restatement: both are lower bounds on the same `gaussianQ`.

Proof: `∫_{(z,∞)} φ(x)(1 + 1/x²) dx = φ(z)/z` by FTC-2 with antiderivative `−φ(x)/x`; then
`1/x² ≤ 1/z²` on `(z,∞)` gives `∫_{(z,∞)} φ/x² ≤ Q z / z²`, so `Q z·(1 + 1/z²) ≥ φ(z)/z`. -/
theorem gaussianTail_birnbaum {z : ℝ} (hz : 0 < z) :
    z / (1 + z ^ 2) * gaussianPDFReal 0 1 z ≤ gaussianQ z := by
  have hz2 : (0:ℝ) < z ^ 2 := by positivity
  have hint1 : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi z) := gaussianPDF_integrableOn _
  have hint2 : IntegrableOn (fun x : ℝ => gaussianPDFReal 0 1 x / x ^ 2) (Set.Ioi z) :=
    integrableOn_gaussianPDF_div_sq hz
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun y : ℝ => -gaussianPDFReal 0 1 y / y)
    (f' := fun x : ℝ => gaussianPDFReal 0 1 x + gaussianPDFReal 0 1 x / x ^ 2)
    (a := z) (m := 0) (fun x hx => hasDerivAt_mills (lt_of_lt_of_le hz hx))
    (hint1.add hint2) tendsto_mills_atTop
  rw [integral_add hint1 hint2] at hftc
  have hbound : (∫ x in Set.Ioi z, gaussianPDFReal 0 1 x / x ^ 2)
      ≤ (∫ x in Set.Ioi z, gaussianPDFReal 0 1 x) / z ^ 2 := by
    rw [← integral_div]
    refine setIntegral_mono_on hint2 ?_ measurableSet_Ioi ?_
    · simpa [div_eq_mul_inv] using ((gaussianPDF_integrableOn (Set.Ioi z)).mul_const (z ^ 2)⁻¹)
    · intro x hx
      gcongr
      · exact gaussianPDFReal_nonneg 0 1 x
      · exact le_of_lt hx
  rw [gaussianQ]
  set Q := ∫ x in Set.Ioi z, gaussianPDFReal 0 1 x with hQ
  have hkey : gaussianPDFReal 0 1 z / z ≤ Q + Q / z ^ 2 := by
    have hrw : (0:ℝ) - -gaussianPDFReal 0 1 z / z = gaussianPDFReal 0 1 z / z := by ring
    rw [hrw] at hftc
    linarith
  have h3 : (gaussianPDFReal 0 1 z / z) * z ^ 2 = z * gaussianPDFReal 0 1 z := by
    field_simp
  have h4 : (Q + Q / z ^ 2) * z ^ 2 = Q * (1 + z ^ 2) := by field_simp; ring
  have hp := mul_le_mul_of_nonneg_right hkey (le_of_lt hz2)
  rw [h3, h4] at hp
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 1 + z ^ 2)]
  linarith

/-! ## Rational witnesses (non-vacuity, `NumericalBounds` enclosure style) -/

/-- **The upper tail is never vacuously zero**: `Q z > 0` at every `z`. Consequently no floor
below that is stated in terms of `Q` can degenerate to the trivial `0 ≤ ·`. Proved from
`gaussianTail_ge_window` at unit window width for `z ≥ 0`, and from `Q(0) = 1/2` otherwise. -/
theorem gaussianQ_pos (z : ℝ) : 0 < gaussianQ z := by
  rcases le_total 0 z with hz | hz
  · have hw := gaussianTail_ge_window hz (by norm_num : (0:ℝ) < 1)
    have hp : 0 < gaussianPDFReal 0 1 (z + 1) := gaussianPDFReal_pos 0 1 _ one_ne_zero
    linarith
  · have hq := gaussianQ_antitone hz
    rw [gaussianQ_zero] at hq
    linarith

/-- **Rational upper enclosure at the `z = 2` operating point**: `Q(2) ≤ 1/6`. The constant is
rational with no floating-point `exp`: `gaussianTail_chernoff` gives `Q(2) ≤ ½·e^{−2}`, and
`SKEFTHawking.QuantumNetwork.expNeg_enclosure` at `r = 2` gives `e^{−2} ≤ 1/3`. (True value
`Q(2) = 2.275e−2`.) This is the Wave-2 consumption of the roadmap's named `expNeg_enclosure`
brick — a call, not a docstring reference. -/
theorem gaussianQ_two_le_rational : gaussianQ 2 ≤ 1 / 6 := by
  have hch := gaussianTail_chernoff (z := 2) (by norm_num)
  have hex := (expNeg_enclosure (by norm_num : (0:ℝ) ≤ 2)).2
  norm_num at hch hex
  linarith

/-- **Rational lower enclosure at the `z = 2` operating point**: `Q(2) ≥ 1/125`. This is the
load-bearing direction (a lower bound on error is a ceiling on fidelity), certified with a
rational constant and no floating-point `exp`. Route: `gaussianTail_ge_window` at `c = 1/2`
gives `Q(2) ≥ ½·φ(5/2)`; then `√(2π) ≤ 2.51` from `Real.pi_lt_d2`, `e^{−3} ≥ 1/20.09` from
`Real.exp_one_lt_d9`, and `e^{−1/8} ≥ 7/8` from `Real.add_one_le_exp`. The certified bracket
`1/125 ≤ Q(2) ≤ 1/6` is non-degenerate (true value `2.275e−2`). -/
theorem gaussianQ_two_ge_rational : (1 : ℝ) / 125 ≤ gaussianQ 2 := by
  have hw := gaussianTail_ge_window (z := 2) (c := 1/2) (by norm_num) (by norm_num)
  rw [gaussianPDF_std, show (2:ℝ) + 1/2 = 5/2 by norm_num,
    show -(5/2:ℝ) ^ 2 / 2 = -3 + -(1/8) by norm_num, Real.exp_add] at hw
  have hspos : (0:ℝ) < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hsle : √(2 * π) ≤ 2.51 := by
    rw [show (2.51:ℝ) = √(2.51 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d2])
  have hA : (1:ℝ) / 2.51 ≤ (√(2 * π))⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hspos hsle
  have hE1 : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpow : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have he3 : Real.exp 3 < 20.09 := by
    rw [hpow]
    nlinarith [Real.exp_pos 1, hE1, sq_nonneg (Real.exp 1)]
  have hB : (1:ℝ) / 20.09 ≤ Real.exp (-3) := by
    rw [Real.exp_neg, ← one_div]
    exact le_of_lt (one_div_lt_one_div_of_lt (Real.exp_pos 3) he3)
  have hC : (7:ℝ) / 8 ≤ Real.exp (-(1/8)) := by
    have h := Real.add_one_le_exp (-(1/8) : ℝ); linarith
  have hprod : (1:ℝ) / 20.09 * (7/8) ≤ Real.exp (-3) * Real.exp (-(1/8)) :=
    mul_le_mul hB hC (by norm_num) (by positivity)
  have hall : (1:ℝ) / 2.51 * ((1:ℝ) / 20.09 * (7/8))
      ≤ (√(2 * π))⁻¹ * (Real.exp (-3) * Real.exp (-(1/8))) :=
    mul_le_mul hA hprod (by norm_num) (by positivity)
  linarith

/-! ## Threshold algebra -/

/-- **Conservativity workhorse (false-alarm branch)**: the false-alarm error increases with the
noise scale `σ` when the threshold sits above the baseline mean. -/
theorem thrErr0_mono_in_sigma {μ₀ σ σ' t : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ σ') (ht : μ₀ < t) :
    thrErr0 μ₀ σ t ≤ thrErr0 μ₀ σ' t := by
  refine gaussianQ_antitone ?_
  gcongr
  linarith

/-- **Conservativity workhorse (miss branch)**: the miss error increases with the noise scale
`σ` when the threshold sits below the signal mean. -/
theorem thrErr1_mono_in_sigma {μ₁ σ σ' t : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ σ') (ht : t < μ₁) :
    thrErr1 μ₁ σ t ≤ thrErr1 μ₁ σ' t := by
  refine gaussianQ_antitone ?_
  gcongr
  linarith

/-- **ROC tradeoff**: moving the threshold right trades false alarm against miss, monotonically
and in opposite directions. The two conjuncts are logically independent (they concern different
branches under different means) and are both needed by a consumer sweeping `t`. -/
theorem offCenter_threshold_tradeoff {μ₀ μ₁ σ t t' : ℝ} (hσ : 0 < σ) (h : t ≤ t') :
    thrErr0 μ₀ σ t' ≤ thrErr0 μ₀ σ t ∧ thrErr1 μ₁ σ t ≤ thrErr1 μ₁ σ t' := by
  constructor
  · exact gaussianQ_antitone (by gcongr)
  · exact gaussianQ_antitone (by gcongr)

/-- **Midpoint symmetry, with the value.** At equal `σ` and the midpoint threshold the two branch
errors are equal *and* equal to `Q` of the half-separation in units of `σ`. Naming the value is
what makes this composable with the error floors below: the bare `e₀ = e₁` form is a
definitional-unfolding tautology and carries no usable content. -/
theorem midpoint_threshold_symmetric {μ₀ μ₁ σ : ℝ} (hσ : 0 < σ) :
    thrErr0 μ₀ σ ((μ₀ + μ₁) / 2) = gaussianQ ((μ₁ - μ₀) / (2 * σ)) ∧
      thrErr1 μ₁ σ ((μ₀ + μ₁) / 2) = gaussianQ ((μ₁ - μ₀) / (2 * σ)) := by
  constructor
  · rw [thrErr0]
    congr 1
    field_simp
    ring
  · rw [thrErr1]
    congr 1
    field_simp
    ring

/-! ## Error floors -/

/-- Ordered case of `gaussianQ_two_le_add`. -/
private theorem gaussianQ_two_le_add_aux {h u : ℝ} (hh : 0 ≤ h) (hu : h ≤ u) :
    2 * gaussianQ h ≤ gaussianQ u + gaussianQ (2 * h - u) := by
  have hint : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have hshift : Integrable (fun y : ℝ => gaussianPDFReal 0 1 (y - 2 * h)) :=
    hint.comp_sub_right (2 * h)
  have hptw : (∫ y in h..u, gaussianPDFReal 0 1 y)
      ≤ ∫ y in h..u, gaussianPDFReal 0 1 (y - 2 * h) := by
    refine intervalIntegral.integral_mono_on hu hint.intervalIntegrable
      hshift.intervalIntegrable ?_
    intro y hy
    exact gaussianPDF_le_of_sq_le
      (by nlinarith [mul_nonneg hh (by linarith [hy.1] : (0:ℝ) ≤ y - h)])
  have hcomp : (∫ y in h..u, gaussianPDFReal 0 1 (y - 2 * h))
      = ∫ x in (-h)..(u - 2 * h), gaussianPDFReal 0 1 x := by
    rw [intervalIntegral.integral_comp_sub_right (gaussianPDFReal 0 1) (2 * h),
      show h - 2 * h = -h by ring]
  have hadd1 : (∫ x in (-h)..(u - 2 * h), gaussianPDFReal 0 1 x)
      + ∫ x in (u - 2 * h)..h, gaussianPDFReal 0 1 x
      = ∫ x in (-h)..h, gaussianPDFReal 0 1 x :=
    intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable
      hint.intervalIntegrable
  have hadd2 : (∫ x in (u - 2 * h)..h, gaussianPDFReal 0 1 x)
      + ∫ x in h..u, gaussianPDFReal 0 1 x
      = ∫ x in (u - 2 * h)..u, gaussianPDFReal 0 1 x :=
    intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable
      hint.intervalIntegrable
  have hQ1 : gaussianQ (u - 2 * h) - gaussianQ u
      = ∫ x in (u - 2 * h)..u, gaussianPDFReal 0 1 x := gaussianQ_sub _ _
  have hQ2 : gaussianQ (-h) - gaussianQ h
      = ∫ x in (-h)..h, gaussianPDFReal 0 1 x := gaussianQ_sub _ _
  have hneg1 : gaussianQ (2 * h - u) = 1 - gaussianQ (u - 2 * h) := by
    have hg := gaussianQ_neg (u - 2 * h)
    rw [show -(u - 2 * h) = 2 * h - u by ring] at hg
    exact hg
  have hneg2 : gaussianQ h = 1 - gaussianQ (-h) := by
    have hg := gaussianQ_neg (-h)
    rwa [neg_neg] at hg
  linarith

/-- **The centred window carries the most Gaussian mass**, in `Q`-form: for `h ≥ 0` and *every*
`u`, `Q(u) + Q(2h − u) ≥ 2·Q(h)`. Equivalently, among all intervals of fixed length `2h` the one
centred at `0` maximizes `∫ φ`. This is the exact statement that makes the midpoint threshold
optimal, and it is what upgrades the threshold floor from `½·Q(z₀)` to `Q(z₀)`.

Proved without any calculus: `gaussianQ_sub` turns both sides into interval integrals, a shift
substitution aligns them over `[h, u]`, and `gaussianPDF_le_of_sq_le` supplies the pointwise
comparison `φ(y) ≤ φ(y − 2h)` there. -/
theorem gaussianQ_two_le_add {h u : ℝ} (hh : 0 ≤ h) :
    2 * gaussianQ h ≤ gaussianQ u + gaussianQ (2 * h - u) := by
  rcases le_total h u with hu | hu
  · exact gaussianQ_two_le_add_aux hh hu
  · have key := gaussianQ_two_le_add_aux hh (show h ≤ 2 * h - u by linarith)
    rw [show 2 * h - (2 * h - u) = u by ring] at key
    linarith

/-- **Separation-budget error floor, uniform over thresholds (sharp constant).** If the mean
separation in units of `σ` is at most `2·z₀`, then NO threshold placement `t` gets the average
branch error below `Q(z₀)`. This is the ceiling-on-fidelity direction, and the constant is
attained (at the midpoint threshold, by `midpoint_threshold_symmetric`). `gaussianQ z₀` is
bounded below by a rational via `gaussianTail_ge_window` / `gaussianTail_birnbaum`, and is
strictly positive by `gaussianQ_pos`, so the floor is never vacuous.

Stated in the project's canonical error functional
`SKEFTHawking.QuantumNetwork.avgAssignmentError`, which this generalizes from the relaxation
model to threshold classification of a Gaussian statistic. -/
theorem avgError_ge_gaussianQ_sharp {μ₀ μ₁ σ t z₀ : ℝ}
    (hσ : 0 < σ) (hμ : μ₀ ≤ μ₁) (hz : (μ₁ - μ₀) / (2 * σ) ≤ z₀) :
    gaussianQ z₀ ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t) := by
  have hhnn : 0 ≤ (μ₁ - μ₀) / (2 * σ) := div_nonneg (by linarith) (by positivity)
  have harg : (μ₁ - t) / σ = 2 * ((μ₁ - μ₀) / (2 * σ)) - (t - μ₀) / σ := by
    field_simp
    ring
  rw [avgAssignmentError, thrErr0, thrErr1, harg]
  have h1 := gaussianQ_two_le_add (h := (μ₁ - μ₀) / (2 * σ)) (u := (t - μ₀) / σ) hhnn
  have h2 : gaussianQ z₀ ≤ gaussianQ ((μ₁ - μ₀) / (2 * σ)) := gaussianQ_antitone hz
  linarith

/-!
### On the roadmap's `avgError_ge_half_gaussianQ` (deliberately NOT shipped)

The Phase-6EA acceptance criteria and the Stage-2 freeze (§7.5, decision D10) name a
factor-2-loose form of the floor, `½·Q(z₀) ≤ avgAssignmentError …`, as the must-ship, with the
sharp `Q(z₀)` form as a stretch. **The sharp form closed**, so the half form was dropped rather
than shipped alongside it.

Rationale (Stage-3a strengthening checklist #1/#4, lead call 2026-07-28): the half form carries
an *identical* hypothesis list to `avgError_ge_gaussianQ_sharp` and a strictly weaker conclusion,
and its only possible proof at that point is `sharp` + `gaussianQ_nonneg` + `linarith`. That is
the identity-wrapper antipattern the pipeline forbids — a weaker restatement of a proved theorem
adds no content and inflates the substantive theorem count. The freeze's own justification for
ordering the half form first ("ship the provable form now; substituting the sharp one later
requires no restatement of any consuming theorem") is discharged, not violated: no consumer needs
restating because none was ever written against the weaker constant.

This is a strengthening of the AC, not a descope — `avgError_ge_gaussianQ_sharp` implies the
roadmap's stated bound pointwise, with the same signature.
-/

end SKEFTHawking.Detection
