import SKEFTHawking.Detection.FilterFloors
import SKEFTHawking.Detection.GaussianThreshold

/-!
# Matched-filter optimality over the admissible single-shot class (Phase 6EB, Wave 3)

The closing layer of Phase 6EB. Wave 1 (`Detection.FilterFloors`) defined the one-sided
equivalent noise bandwidth and proved the single-shot realizability floor `ENBW·T ≥ 1/2`;
Wave 2 (`Detection.NEPAlgebra`) built the NEP / responsivity composition algebra. Both describe
what a *given* filter does. This file bounds what **any** filter can do: over the admissible
class, the deflection-to-noise ratio of a linear single-shot readout is capped by a quantity
depending only on the template energy and the noise PSD, and the cap is attained exactly by the
matched filter.

That is what turns a downstream budget into a *ceiling*: a floor stated against the best
possible linear readout cannot be beaten by a cleverer filter.

## The admissible class, stated explicitly

`IsAdmissibleFilter T s h` — the class quantified over in every optimality statement below:

* `h² ∈ L¹[0, T]` (finite energy **over the window**);
* the deflection integral `∫₀ᵀ h·s` exists.

Both conjuncts are carried in the statement, never in prose. Two points of precision, because this
is the section whose whole purpose is to make the class honest:

* **Window *support* is not encoded, and is not needed.** `IntervalIntegrable` on `[0, T]`
  constrains nothing about `h` outside the window — an everywhere-nonzero `h` is admissible. What
  makes the layer single-shot is that every quantity below reads `h` only through `∫₀ᵀ`, and in
  particular `IsWhiteFilteredVariance` defines the noise from `∫₀ᵀ h²` alone. The bound therefore
  holds on this *larger* class, which is strictly stronger than restricting to supported filters.
* **The second field is genuinely independent, not merely un-derivable at the pin.** It is
  tempting to call it Cauchy–Schwarz for `h, s ∈ L²`, but the first field is `h² ∈ L¹`, which does
  **not** give measurability of `h` (flip the sign of a constant on a non-measurable set and `h²`
  is unchanged). So `h·s` need not be measurable and no lemma could supply the implication.

## Conventions (inherited, not re-chosen)

* **One-sided PSD**, via Wave 1's `IsWhiteFilteredVariance V S₀ T : ∀ h, V h = S₀/2 · ∫₀ᵀ h²`.
  The noise scale of the filtered output is `√(V h)`; the `S₀/2` is the one-sided normalization
  fixed by `GrapheneNoiseFormula` and threaded through this file's statements via `hwhite`.
* **Deflection**, not power: `filteredSNR` is an *amplitude* ratio `(∫ h·s) / √(V h)`. 6EA's
  threshold algebra consumes **half** of it: under this module's identification
  `filteredSNR = (μ₁ − μ₀)/σ`, whereas `avgError_ge_gaussianQ_sharp` takes the midpoint-threshold
  separation `(μ₁ − μ₀)/(2σ) = filteredSNR/2`. That factor of 2 is carried explicitly by
  `matchedBudget_half_eq` and `optimal_z_budget`, never absorbed — and
  `matchedBudget_half_ne_matchedBudget` makes the mix-up detectable, as the phase's
  convention-falsifier fork requires.
* **Sign matters.** The bound is on the signed ratio, and `filteredSNR_neg_matched_eq_neg_budget`
  witnesses that the sign is load-bearing: `h = −s` saturates Cauchy–Schwarz in magnitude yet
  sits at `−matchedBudget`, so the equality characterization's positivity condition cannot be
  dropped.

## Layout

* **Definitions** — `IsAdmissibleFilter`, `filteredSNR`, `matchedBudget`, `admissibleSNRs`.
* **The two-function interval Cauchy–Schwarz** — `integral_sub_smul_sq` (the variance expansion,
  the exact analogue of Wave 1's `integral_sub_const_sq`) and `sq_integral_mul_le`. Route note:
  the same variance route Wave 1 settled on (`0 ≤ ∫(h − c·s)²`), *not* Hölder / `MemLp` — see
  the Phase 6EB notebook's UNKNOWN-1 resolution.
* **Optimality** — `filteredSNR_le_matchedBudget` (the headline), `filteredSNR_matched_eq_budget`
  (attainment), `matchedFilter_isGreatest` (the two combined as a `IsGreatest`), and
  `filteredSNR_eq_budget_iff` (the equality characterization: saturation iff `h` is a.e. a
  **positive** multiple of the template).
* **Budget and error floor** — `matchedBudget_antitone_psd` (the budget is antitone in the noise
  PSD — what lets a downstream consumer state a floor for a single irreducible channel rather
  than for a composed budget), `matchedBudget_half_eq` (the separation budget in closed form),
  `optimal_z_budget`, and `error_floor_from_budget`, which composes the whole layer with
  6EA Wave 2's `avgError_ge_gaussianQ_sharp`.
* **Non-vacuity** — a concrete boxcar template at which the floor is a `norm_num`-checkable
  positive rational (`error_floor_twoBoxcar_witness`).
* **Degenerate branches, disclosed** — `filteredSNR_of_variance_eq_zero`.

## AC deviations (all in the strengthening direction)

* **Optimality** (the roadmap's predicted name for this deliverable was never realized as a
  declaration — see the deviation below). The AC's literal shape is
  `∀ h ∈ class, SNR h ≤ SNR (matched template)`. What ships is strictly stronger:
  `filteredSNR_le_matchedBudget` bounds by a **filter-free, template-only** quantity, and
  `matchedFilter_isGreatest` packages it with attainment as an `IsGreatest`. The AC's form is
  the composition `filteredSNR_le_matchedBudget` ▸ `filteredSNR_matched_eq_budget` and is
  therefore *not* shipped separately — at an identical hypothesis list it would be a weaker
  restatement closable in one `linarith`, the identity-wrapper pattern the strengthening
  checklist forbids. (Precisely: the composition covers `0 < ∫₀ᵀ s²`; at the degenerate template
  energy the AC form additionally needs `filteredSNR_of_variance_eq_zero`, which is shipped, so
  the AC form is derivable at *no* extra hypothesis.) Same call as **6EA** Wave 2's
  `avgError_ge_gaussianQ_sharp` (see `Detection.GaussianThreshold`'s closing note).
* **Equality characterization.** The AC asks for "equality characterization"; what ships is the
  full biconditional `filteredSNR_eq_budget_iff`, including the **positivity** of the scaling
  factor — which `filteredSNR_neg_matched_eq_neg_budget` shows is not removable.
* **`matchedBudget_half_eq` is unconditional.** Both sides collapse to `0` on every degenerate
  branch, so neither a `0 ≤ ∫₀ᵀ s²` binder nor a `0 < S₀` binder is a guard. *(The second was
  still being carried until 2026-07-29, while the docstring boasted about having dropped the
  first — the minimality standard is now applied to both. `0 < S₀` is genuinely load-bearing in
  `matchedBudget_antitone_psd`, and that is now a theorem rather than an assertion:
  `matchedBudget_antitone_psd_S0_hypothesis_load_bearing` exhibits the failure at `S₀ = 0`.
  The accompanying "and that is the only place in this file it appears as a guard rather than as a
  route requirement" was an unproved universal negative over the file; it is retained only as a
  reading aid, not as a claim.)*
* **`optimal_z_budget` ships despite being the headline bound divided by two**, at an identical
  binder list — the one place the identity-wrapper rule is deliberately *not* applied. Its
  docstring states why: it crosses the `z = SNR/2` convention boundary that
  `matchedBudget_half_ne_matchedBudget` proves is detectable, so the division belongs in one
  audited declaration rather than at each consumer.

**⚠ Guardrail (inherited).** Everything below is a bound over an *admissible filter class*. No
claim is made about any physical instrument's implementation; identifying a device's readout
with an `h` in the class, and its output statistics with `μ₀ / μ₁ / σ`, is the consuming phase's
declared hypothesis and appears in the binder list of every consuming statement.

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology*.
-/

namespace SKEFTHawking.Detection

open MeasureTheory Real SKEFTHawking.QuantumNetwork

/-! ## Definitions -/

/-- **The admissible single-shot linear filter class on `[0, T]`, against template `s`.**

A filter is admissible when it has finite energy *over the window* and its deflection integral
against the template exists. Membership is relative to the template because the deflection is;
this is the class the roadmap's Wave-3 AC quantifies over.

**This does NOT encode window support** — `IntervalIntegrable` on `[0, T]` says nothing about `h`
off the window, and indeed `fun x => Real.exp x` is admissible. Single-shot-ness of the *layer*
comes from every statement reading `h` only through `∫₀ᵀ` (and `IsWhiteFilteredVariance` defining
the noise from `∫₀ᵀ h²`), so the bounds below hold on this larger class — strictly stronger than
restricting to supported filters. See the module docstring.

**Both fields are independent.** `mul_integrable` is *not* a derivable consequence of
`sq_integrable` plus `s² ∈ L¹`: `h² ∈ L¹` does not give measurability of `h` (flip a constant's
sign on a non-measurable set), so `h·s` need not be measurable at all. -/
structure IsAdmissibleFilter (T : ℝ) (s h : ℝ → ℝ) : Prop where
  /-- `h² ∈ L¹[0, T]`: the filter has finite energy over the window. -/
  sq_integrable : IntervalIntegrable (fun x => h x ^ 2) volume 0 T
  /-- The deflection integral `∫₀ᵀ h·s` exists. -/
  mul_integrable : IntervalIntegrable (fun x => h x * s x) volume 0 T

/-- **Deflection-to-noise ratio of filter `h` against template `s`.**

    SNR(h) = (∫₀ᵀ h·s) / √(V h)

`V` is the output second-moment functional of Wave 1 (`IsWhiteFilteredVariance`), so the
denominator is the *noise standard deviation of the filtered output* — an amplitude ratio, the
form 6EA's threshold algebra consumes. The numerator is signed: a filter anti-correlated with
the template has negative SNR (`filteredSNR_neg_matched_eq_neg_budget`).

**Degenerate branch, disclosed.** When `V h = 0` (zero-energy filter) Lean's total division
returns `0` (`filteredSNR_of_variance_eq_zero`); the bound below holds there vacuously, and every
*equality* statement carries `0 < ∫₀ᵀ s²` explicitly. -/
noncomputable def filteredSNR (V : (ℝ → ℝ) → ℝ) (T : ℝ) (s h : ℝ → ℝ) : ℝ :=
  (∫ x in (0:ℝ)..T, h x * s x) / √(V h)

/-- **The matched-filter budget** — the ceiling of `filteredSNR` over the admissible class:

    B(S₀, T, s) = √(2 · (∫₀ᵀ s²) / S₀)

Depends only on the template *energy* and the one-sided noise PSD — never on the filter. That
independence is the point: it is what makes a downstream error floor a ceiling rather than a
statement about one particular readout. -/
noncomputable def matchedBudget (S₀ T : ℝ) (s : ℝ → ℝ) : ℝ :=
  √(2 * (∫ x in (0:ℝ)..T, s x ^ 2) / S₀)

/-- The set of deflection-to-noise ratios realizable by an admissible filter — the set
`matchedFilter_isGreatest` exhibits `matchedBudget` as the greatest element of. -/
noncomputable def admissibleSNRs (V : (ℝ → ℝ) → ℝ) (T : ℝ) (s : ℝ → ℝ) : Set ℝ :=
  {r | ∃ h : ℝ → ℝ, IsAdmissibleFilter T s h ∧ filteredSNR V T s h = r}

/-! ## The two-function interval Cauchy–Schwarz -/

/-- **The variance expansion against a template** — the single engine behind both the optimality
bound and its equality case:

    ∫₀ᵀ (h − c·s)² = ∫₀ᵀ h² − 2c·∫₀ᵀ h·s + c²·∫₀ᵀ s²

The exact two-function analogue of Wave 1's `integral_sub_const_sq` (which is this at `s ≡ 1`),
stated separately because both `sq_integral_mul_le` (via non-negativity of the left side) and
`filteredSNR_eq_budget_iff` (via its vanishing) consume it. -/
theorem integral_sub_smul_sq (h s : ℝ → ℝ) (T c : ℝ)
    (hh : IntervalIntegrable (fun x => h x ^ 2) volume 0 T)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    (hhs : IntervalIntegrable (fun x => h x * s x) volume 0 T) :
    (∫ x in (0:ℝ)..T, (h x - c * s x) ^ 2)
      = (∫ x in (0:ℝ)..T, h x ^ 2) - 2 * c * (∫ x in (0:ℝ)..T, h x * s x)
          + c ^ 2 * (∫ x in (0:ℝ)..T, s x ^ 2) := by
  have e1 : (fun x => (h x - c * s x) ^ 2)
      = fun x => (h x ^ 2 - 2 * c * (h x * s x)) + c ^ 2 * s x ^ 2 := by
    funext x; ring
  have hi1 : IntervalIntegrable (fun x => h x ^ 2 - 2 * c * (h x * s x)) volume 0 T :=
    hh.sub (hhs.const_mul _)
  have hi2 : IntervalIntegrable (fun x => c ^ 2 * s x ^ 2) volume 0 T := hs.const_mul _
  rw [e1, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_sub hh (hhs.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- **Cauchy–Schwarz on the window, two-function form:**
`(∫₀ᵀ h·s)² ≤ (∫₀ᵀ h²)·(∫₀ᵀ s²)`.

Mathlib carries the discrete form and the abstract inner-product / `MemLp` forms, but not this
interval-integral shape. Proved — like Wave 1's `sq_integral_le`, which is this at `s ≡ 1` — from
non-negativity of `∫₀ᵀ (h − c·s)²`, with no Hölder, no `rpow`, no `MemLp`.

The degenerate template branch (`∫₀ᵀ s² = 0`) is handled rather than excluded: there the same
non-negativity forces the deflection itself to vanish. -/
theorem sq_integral_mul_le (h s : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hh : IntervalIntegrable (fun x => h x ^ 2) volume 0 T)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    (hhs : IntervalIntegrable (fun x => h x * s x) volume 0 T) :
    (∫ x in (0:ℝ)..T, h x * s x) ^ 2
      ≤ (∫ x in (0:ℝ)..T, h x ^ 2) * (∫ x in (0:ℝ)..T, s x ^ 2) := by
  set A := ∫ x in (0:ℝ)..T, h x ^ 2 with hA
  set B := ∫ x in (0:ℝ)..T, h x * s x with hB
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  have key : ∀ c : ℝ, 0 ≤ A - 2 * c * B + c ^ 2 * C := by
    intro c
    have h0 : 0 ≤ ∫ x in (0:ℝ)..T, (h x - c * s x) ^ 2 :=
      intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)
    rwa [integral_sub_smul_sq h s T c hh hs hhs] at h0
  have hCnn : 0 ≤ C := intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)
  rcases eq_or_lt_of_le hCnn with hC0 | hCpos
  · -- degenerate template: the deflection must vanish
    have hB0 : B = 0 := by
      by_contra hne
      have := key ((A + 1) / (2 * B))
      rw [← hC0] at this
      have hBne : (2 : ℝ) * B ≠ 0 := by
        simpa using hne
      have e : 2 * ((A + 1) / (2 * B)) * B = A + 1 := by
        field_simp
      rw [e] at this
      simp at this
      linarith
    rw [hB0, ← hC0]
    simp
  · have := key (B / C)
    have e1 : 2 * (B / C) * B = 2 * (B ^ 2 / C) := by field_simp
    have e2 : (B / C) ^ 2 * C = B ^ 2 / C := by field_simp
    rw [e1, e2] at this
    have hkey : B ^ 2 / C ≤ A := by linarith
    have := (div_le_iff₀ hCpos).mp hkey
    linarith

/-! ## Matched-filter optimality -/

/-- The matched-filter ratio in closed form: `C / √(S₀/2 · C) = √(2C/S₀)` for `C, S₀ > 0`. The
arithmetic core shared by `filteredSNR_matched_eq_budget` and `filteredSNR_smul_eq_budget`. -/
theorem matched_ratio_eq_sqrt {S₀ C : ℝ} (hS : 0 < S₀) (hC : 0 < C) :
    C / √(S₀ / 2 * C) = √(2 * C / S₀) := by
  have hpos : 0 < S₀ / 2 * C := by positivity
  rw [div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hpos)), ← Real.sqrt_mul (by positivity)]
  have e : 2 * C / S₀ * (S₀ / 2 * C) = C ^ 2 := by field_simp
  rw [e, Real.sqrt_sq hC.le]

/-- **The headline: matched-filter optimality.**

Over the admissible class `IsAdmissibleFilter T s h`, in white noise of one-sided PSD `S₀`
(`hwhite`), every filter's deflection-to-noise ratio is bounded by the template-only budget:

    (∫₀ᵀ h·s) / √(V h) ≤ √(2·(∫₀ᵀ s²)/S₀)

The right-hand side mentions no filter — that is what makes it a ceiling. Cauchy–Schwarz on the
window (`sq_integral_mul_le`); the equality case is `filteredSNR_eq_budget_iff`. -/
theorem filteredSNR_le_matchedBudget {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 ≤ T)
    {s h : ℝ → ℝ} (hadm : IsAdmissibleFilter T s h)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T) :
    filteredSNR V T s h ≤ matchedBudget S₀ T s := by
  set A := ∫ x in (0:ℝ)..T, h x ^ 2 with hA
  set B := ∫ x in (0:ℝ)..T, h x * s x with hB
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  have hCnn : 0 ≤ C := intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)
  have hAnn : 0 ≤ A := intervalIntegral.integral_nonneg hT (fun u _ => sq_nonneg _)
  have hCS : B ^ 2 ≤ A * C := sq_integral_mul_le h s T hT hadm.sq_integrable hs hadm.mul_integrable
  have hVh : V h = S₀ / 2 * A := hwhite h
  unfold filteredSNR matchedBudget
  rw [hVh, ← hB, ← hC]
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · -- zero-energy filter: Lean's total division gives `0`, and the budget is non-negative
    rw [← hA0]
    simp only [mul_zero, Real.sqrt_zero, div_zero]
    positivity
  · have hden : 0 < √(S₀ / 2 * A) := Real.sqrt_pos.mpr (by positivity)
    rw [div_le_iff₀ hden, ← Real.sqrt_mul (by positivity)]
    have e : 2 * C / S₀ * (S₀ / 2 * A) = A * C := by field_simp
    rw [e]
    calc B ≤ |B| := le_abs_self B
      _ = √(B ^ 2) := (Real.sqrt_sq_eq_abs B).symm
      _ ≤ √(A * C) := Real.sqrt_le_sqrt hCS

/-- **Attainment at a positive multiple of the template.** Any `h = c·s` with `c > 0` sits
exactly at the budget — the gain is irrelevant, only the *shape* matters. Specializing to
`c = 1` gives `filteredSNR_matched_eq_budget`; the `c > 0` hypothesis is load-bearing
(`filteredSNR_neg_matched_eq_neg_budget`). -/
theorem filteredSNR_smul_eq_budget {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀)
    {s : ℝ → ℝ} (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) {c : ℝ} (hc : 0 < c) :
    filteredSNR V T s (fun x => c * s x) = matchedBudget S₀ T s := by
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  have hnum : (∫ x in (0:ℝ)..T, (c * s x) * s x) = c * C := by
    rw [hC, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  have hsq : (∫ x in (0:ℝ)..T, (c * s x) ^ 2) = c ^ 2 * C := by
    rw [hC, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  have hVh : V (fun x => c * s x) = S₀ / 2 * (c ^ 2 * C) := by
    rw [hwhite (fun x => c * s x), hsq]
  unfold filteredSNR matchedBudget
  rw [hnum, hVh, ← hC]
  have e : S₀ / 2 * (c ^ 2 * C) = c ^ 2 * (S₀ / 2 * C) := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le,
    mul_div_mul_left _ _ (ne_of_gt hc)]
  exact matched_ratio_eq_sqrt hS hCpos

/-- **The matched filter attains the budget.** `h = s` is admissible-and-optimal: its
deflection-to-noise ratio equals `matchedBudget` exactly. Together with
`filteredSNR_le_matchedBudget` this is what makes the budget a *maximum*, not merely a bound. -/
theorem filteredSNR_matched_eq_budget {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀)
    {s : ℝ → ℝ} (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) :
    filteredSNR V T s s = matchedBudget S₀ T s := by
  have := filteredSNR_smul_eq_budget hwhite hS hCpos (c := 1) one_pos
  simpa using this

/-- **Sign sensitivity — the positivity condition is load-bearing.** The anti-matched filter
`h = −s` saturates Cauchy–Schwarz in *magnitude* yet realizes `−matchedBudget`. So a saturation
characterization phrased only as "`h` is a.e. a multiple of `s`" would be **false**: the sign of
the multiple is part of the content, and `filteredSNR_eq_budget_iff` carries it. -/
theorem filteredSNR_neg_matched_eq_neg_budget {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀)
    {s : ℝ → ℝ} (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) :
    filteredSNR V T s (fun x => -s x) = -(matchedBudget S₀ T s) := by
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  have hnum : (∫ x in (0:ℝ)..T, (-s x) * s x) = -C := by
    rw [hC, ← intervalIntegral.integral_neg]
    congr 1; funext x; ring
  have hsq : (∫ x in (0:ℝ)..T, (-s x) ^ 2) = C := by
    rw [hC]; congr 1; funext x; ring
  have hVh : V (fun x => -s x) = S₀ / 2 * C := by
    rw [hwhite (fun x => -s x), hsq]
  unfold filteredSNR matchedBudget
  rw [hnum, hVh, ← hC, neg_div]
  rw [matched_ratio_eq_sqrt hS hCpos]

/-- **The optimality statement in its sharpest form:** `matchedBudget` is the *greatest*
realizable deflection-to-noise ratio over the admissible class — an upper bound
(`filteredSNR_le_matchedBudget`) that is itself realized (`filteredSNR_matched_eq_budget`).

This is the Wave-3 deliverable in the shape Wave 1 used for its floor
(`enbw_mul_window_isLeast`): a `IsGreatest`, not a one-sided inequality that might be slack. -/
theorem matchedFilter_isGreatest {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 ≤ T)
    {s : ℝ → ℝ} (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) :
    IsGreatest (admissibleSNRs V T s) (matchedBudget S₀ T s) := by
  have hss : IntervalIntegrable (fun x => s x * s x) volume 0 T := by
    simpa [sq] using hs
  constructor
  · exact ⟨s, ⟨hs, hss⟩, filteredSNR_matched_eq_budget hwhite hS hCpos⟩
  · rintro r ⟨h, hadm, rfl⟩
    exact filteredSNR_le_matchedBudget hwhite hS hT hadm hs

/-! ## The equality characterization -/

/-- **Saturation happens exactly at positive multiples of the template (a.e. on the window).**

    SNR(h) = matchedBudget  ↔  ∃ c > 0, h =ᵐ c·s  on `Ioc 0 T`

The forward direction routes through the same variance integral as the bound: equality forces
`∫₀ᵀ (h − c·s)² = 0` at `c = (∫ h·s)/(∫ s²)`, which by
`intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae` forces `h =ᵐ c·s`; positivity of `c`
comes from the deflection being positive at saturation. The `0 < c` is not decoration —
`filteredSNR_neg_matched_eq_neg_budget` exhibits an `h` that is a.e. a multiple of `s` and does
*not* saturate. -/
theorem filteredSNR_eq_budget_iff {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 < T)
    {s h : ℝ → ℝ} (hadm : IsAdmissibleFilter T s h)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) :
    filteredSNR V T s h = matchedBudget S₀ T s ↔
      ∃ c : ℝ, 0 < c ∧ h =ᵐ[volume.restrict (Set.Ioc 0 T)] fun x => c * s x := by
  set A := ∫ x in (0:ℝ)..T, h x ^ 2 with hA
  set B := ∫ x in (0:ℝ)..T, h x * s x with hB
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  have hAnn : 0 ≤ A := intervalIntegral.integral_nonneg hT.le (fun u _ => sq_nonneg _)
  have hVh : V h = S₀ / 2 * A := hwhite h
  have hMB : matchedBudget S₀ T s = √(2 * C / S₀) := by unfold matchedBudget; rw [← hC]
  have hSNR : filteredSNR V T s h = B / √(S₀ / 2 * A) := by
    unfold filteredSNR; rw [hVh, ← hB]
  constructor
  · intro heq
    -- saturation forces `B = √(A·C)`, hence `B > 0` and `B² = A·C`
    have hApos : 0 < A := by
      by_contra hle
      push Not at hle
      have hA0 : A = 0 := le_antisymm hle hAnn
      have hz : filteredSNR V T s h = 0 := by rw [hSNR, hA0]; simp
      have hpos : 0 < matchedBudget S₀ T s := by
        rw [hMB]; exact Real.sqrt_pos.mpr (by positivity)
      rw [hz, hMB] at heq
      rw [hMB] at hpos
      linarith [heq ▸ hpos]
    have hden : 0 < √(S₀ / 2 * A) := Real.sqrt_pos.mpr (by positivity)
    have hBval : B = √(2 * C / S₀) * √(S₀ / 2 * A) := by
      rw [hSNR, hMB] at heq
      exact (div_eq_iff (ne_of_gt hden)).mp heq
    have hprod : √(2 * C / S₀) * √(S₀ / 2 * A) = √(A * C) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    rw [hprod] at hBval
    have hBpos : 0 < B := by rw [hBval]; exact Real.sqrt_pos.mpr (by positivity)
    have hBsq : B ^ 2 = A * C := by
      rw [hBval, Real.sq_sqrt (by positivity)]
    refine ⟨B / C, by positivity, ?_⟩
    have hvar : (∫ x in (0:ℝ)..T, (h x - B / C * s x) ^ 2) = 0 := by
      rw [integral_sub_smul_sq h s T (B / C) hadm.sq_integrable hs hadm.mul_integrable,
        ← hA, ← hB, ← hC]
      have e1 : 2 * (B / C) * B = 2 * (B ^ 2 / C) := by field_simp
      have e2 : (B / C) ^ 2 * C = B ^ 2 / C := by field_simp
      rw [e1, e2, hBsq]
      field_simp
      ring
    have hsub : IntervalIntegrable (fun x => (h x - B / C * s x) ^ 2) volume 0 T := by
      have hrw : (fun x => (h x - B / C * s x) ^ 2)
          = fun x => (h x ^ 2 - 2 * (B / C) * (h x * s x)) + (B / C) ^ 2 * s x ^ 2 := by
        funext x; ring
      rw [hrw]
      exact (hadm.sq_integrable.sub (hadm.mul_integrable.const_mul _)).add (hs.const_mul _)
    have hzero := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le
      (Filter.Eventually.of_forall (fun x => sq_nonneg (h x - B / C * s x))) hsub).mp hvar
    filter_upwards [hzero] with x hx
    have hx0 : (h x - B / C * s x) ^ 2 = 0 := hx
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx0
    linarith
  · rintro ⟨c, hc, hcong⟩
    have key : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0:ℝ) T → h x = c * s x := by
      rw [Set.uIoc_of_le hT.le]
      exact (ae_restrict_iff' measurableSet_Ioc).mp hcong
    have hnum : B = ∫ x in (0:ℝ)..T, (c * s x) * s x := by
      rw [hB]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [key] with x hx
      intro hm
      rw [hx hm]
    have hAeq : A = ∫ x in (0:ℝ)..T, (c * s x) ^ 2 := by
      rw [hA]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [key] with x hx
      intro hm
      rw [hx hm]
    have hVeq : V h = V (fun x => c * s x) := by
      rw [hwhite h, hwhite (fun x => c * s x), ← hA, ← hAeq]
    have hswap : filteredSNR V T s h = filteredSNR V T s (fun x => c * s x) := by
      unfold filteredSNR
      rw [← hB, hnum, hVeq]
    rw [hswap]
    exact filteredSNR_smul_eq_budget hwhite hS hCpos hc

/-! ## The budget's monotonicity in the noise PSD -/

/-- **The budget is antitone in the one-sided noise PSD** — a quieter channel raises the
deflection ceiling:

    S₁ ≤ S₂  ⟹  B(S₂, T, s) ≤ B(S₁, T, s).

This is the lemma that turns a *composed* floor into a floor for an **individual** channel: bound
a detector's total noise PSD from below by the PSD of one irreducible channel, apply this, and the
error floor survives with every other channel removed from the statement. Consumed by
`Electrothermal.ETFModel.phonon_only_error_floor`, where dropping the Johnson channel is exactly
what upgrades "this detector's floor" to "no detector of this class beats the thermal-fluctuation
floor".

Hypotheses are minimal, held to the same standard as `matchedBudget_half_eq` below. `0 < S₁` is
**load-bearing**: at `S₁ = 0` Lean's total division sends the left-hand budget to `√(2·E/0) = 0`,
so the quieter PSD would report the *smaller* budget and the inequality fails at any positive
template energy. Neither `0 ≤ T` nor integrability of `s²` is required — on the reversed-window
branch the template energy is non-positive and **both** budgets are Lean's `√(non-positive) = 0`,
so the ordering holds there as well. -/
theorem matchedBudget_antitone_psd {S₁ S₂ T : ℝ} (hS : 0 < S₁) (h12 : S₁ ≤ S₂) (s : ℝ → ℝ) :
    matchedBudget S₂ T s ≤ matchedBudget S₁ T s := by
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  unfold matchedBudget
  rw [← hC]
  rcases le_or_gt 0 C with hCnn | hCneg
  · apply Real.sqrt_le_sqrt
    gcongr
  · have h2 : 0 < S₂ := lt_of_lt_of_le hS h12
    rw [Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le),
      Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hS.le)]

/-- **`0 < S₁` in `matchedBudget_antitone_psd` is load-bearing — the witness.**

At `S₁ = 0`, `S₂ = 1`, unit template on `[0, 1]`: the template energy is `1`, so
`matchedBudget 1 1 s = √2 > 0` while Lean's total division sends
`matchedBudget 0 1 s = √(2/0) = 0`. The antitonicity conclusion `matchedBudget S₂ ≤ matchedBudget S₁`
would read `√2 ≤ 0`, which is false — so dropping the hypothesis does not merely break the proof,
it breaks the theorem.

The enclosing docstring argued this in prose; this is that argument as a theorem, which is the
standard the file applies to every other necessity claim. *(Added 2026-07-29.)* -/
theorem matchedBudget_antitone_psd_S0_hypothesis_load_bearing :
    ¬ (matchedBudget 1 1 (fun _ => 1) ≤ matchedBudget 0 1 (fun _ => 1)) := by
  have hint : ∫ x in (0:ℝ)..1, (1:ℝ) ^ 2 = 1 := by norm_num
  unfold matchedBudget
  rw [hint]
  simp only [div_zero, div_one, Real.sqrt_zero, not_le]
  positivity

/-! ## The separation budget and the composed error floor -/

/-- **The separation budget in closed form.** Half the matched budget — the quantity 6EA's
threshold algebra consumes as its `z` — is

    matchedBudget / 2 = √((∫₀ᵀ s²) / (2·S₀))

i.e. the roadmap's `√(∫s²/S₀)`-shaped bound with the one-sided constant made explicit.

**Fully unconditional**, and the minimality standard is applied to *both* candidate binders rather
than only to the conspicuous one. Neither a sign hypothesis on the template energy nor `0 < S₀` is
carried: at `S₀ = 0` both sides collapse to Lean's `√0 = 0`, and on the negative branches the two
radicands stay in the same sign class (`2C/S₀` and `C/(2S₀)` differ by a positive factor `4`), so
the identity survives every degenerate combination. *(The `0 < S₀` binder was dropped 2026-07-29
after adversarial review pointed out that this docstring boasted about dropping a dead binder
while carrying another one — `matchedBudget_antitone_psd` above is where `0 < S₀` genuinely
bites.)* -/
theorem matchedBudget_half_eq {S₀ T : ℝ} (s : ℝ → ℝ) :
    matchedBudget S₀ T s / 2 = √((∫ x in (0:ℝ)..T, s x ^ 2) / (2 * S₀)) := by
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  unfold matchedBudget
  rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num,
    ← Real.sqrt_div' _ (by norm_num)]
  congr 1
  ring

/-- **The optimal-`z` budget — filter-independent.** The separation `z = (∫ h·s)/(2√(V h))` that
any admissible single-shot readout can present to a threshold classifier is capped by a quantity
built from the template energy and the noise PSD alone:

    (∫₀ᵀ h·s) / (2·√(V h)) ≤ √((∫₀ᵀ s²) / (2·S₀))

This is `filteredSNR_le_matchedBudget` in the coordinates 6EA works in, and is what
`error_floor_from_budget` feeds to `avgError_ge_gaussianQ_sharp`.

**Why this is shipped although it is `filteredSNR_le_matchedBudget` divided by two, at an
identical binder list.** The AC-deviations section above invokes the identity-wrapper rule to
justify *not* shipping the AC's literal optimality form; consistency demands saying why that rule
does not bite here. It does not, because this statement **crosses the phase's factor-2 convention
boundary**: `filteredSNR` is a deflection-to-noise *amplitude* ratio, while 6EA's threshold
algebra consumes the midpoint separation `z = (μ₁−μ₀)/(2σ) = filteredSNR/2`. The seam is exactly
where the two conventions meet, it is provably detectable
(`matchedBudget_half_ne_matchedBudget` — nearly three orders of magnitude in the resulting error
floor), and the roadmap's Wave-3 AC names this quantity explicitly. Shipping the `/2` form as a
named declaration is therefore convention discipline, not restatement: the division happens once,
in one audited place, instead of at each consumer. -/
theorem optimal_z_budget {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 ≤ T)
    {s h : ℝ → ℝ} (hadm : IsAdmissibleFilter T s h)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T) :
    (∫ x in (0:ℝ)..T, h x * s x) / (2 * √(V h))
      ≤ √((∫ x in (0:ℝ)..T, s x ^ 2) / (2 * S₀)) := by
  have hbound := filteredSNR_le_matchedBudget hwhite hS hT hadm hs
  rw [← matchedBudget_half_eq s]
  unfold filteredSNR at hbound
  rw [show (∫ x in (0:ℝ)..T, h x * s x) / (2 * √(V h))
      = ((∫ x in (0:ℝ)..T, h x * s x) / √(V h)) / 2 by rw [div_div]; ring_nf]
  linarith

/-- **The composed error floor — the layer's payoff.**

Any threshold classifier acting on the output of **any** admissible single-shot linear filter,
under the consumer's declared identification of the deflection (`hμ`) and the noise scale
(`hσV`), has average assignment error at least `Q(matchedBudget/2)` — a bound that mentions no
filter and no threshold.

This is 6EB Wave 3 composed with 6EA Wave 2: `optimal_z_budget` supplies the separation cap and
`SKEFTHawking.Detection.avgError_ge_gaussianQ_sharp` converts it into an error floor. The
docstring's cross-reference is backed by an actual call in the proof below (project checklist
Q3). -/
theorem error_floor_from_budget {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 ≤ T)
    {s h : ℝ → ℝ} (hadm : IsAdmissibleFilter T s h)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    {μ₀ μ₁ σ t : ℝ} (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..T, h x * s x) (hσV : σ = √(V h)) :
    gaussianQ (matchedBudget S₀ T s / 2)
      ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t) := by
  refine avgError_ge_gaussianQ_sharp hσ hμle ?_
  rw [hμ, hσV, matchedBudget_half_eq s]
  exact optimal_z_budget hwhite hS hT hadm hs

/-! ## Non-vacuity: a concrete budget point -/

/-- The scaled boxcar template `2·𝟙[0,2]` is square-integrable on its window. -/
theorem intervalIntegrable_twoBoxcar_sq :
    IntervalIntegrable (fun x => (2 * boxcar 2 x) ^ 2) volume 0 2 := by
  have hrw : (fun x => (2 * boxcar 2 x) ^ 2) = fun x => 4 * (boxcar 2 x ^ 2) := by
    funext x; ring
  rw [hrw]
  exact (intervalIntegrable_boxcar_sq 2 (by norm_num)).const_mul 4

/-- Template energy of `2·𝟙[0,2]` over its own window: `∫₀² (2·𝟙)² = 8`. -/
theorem integral_twoBoxcar_sq : (∫ x in (0:ℝ)..2, (2 * boxcar 2 x) ^ 2) = 8 := by
  have hrw : (fun x => (2 * boxcar 2 x) ^ 2) = fun x => 4 * (boxcar 2 x ^ 2) := by
    funext x; ring
  rw [show (∫ x in (0:ℝ)..2, (2 * boxcar 2 x) ^ 2)
      = ∫ x in (0:ℝ)..2, 4 * (boxcar 2 x ^ 2) by rw [hrw],
    intervalIntegral.integral_const_mul, integral_boxcar_sq 2 (by norm_num)]
  norm_num

/-- **A concrete budget point, checked by `norm_num`.** For the template `2·𝟙[0,2]` in white
noise of one-sided PSD `S₀ = 1`, the matched budget is exactly `4`, so the separation cap is
`z = 2`. Rational, not floating-point: this is the point at which the abstract ceiling becomes a
number a laboratory can be held to. -/
theorem matchedBudget_twoBoxcar : matchedBudget 1 2 (fun x => 2 * boxcar 2 x) = 4 := by
  unfold matchedBudget
  rw [integral_twoBoxcar_sq]
  rw [show (2:ℝ) * 8 / 1 = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **Non-vacuity witness for the composed floor.** At the concrete budget point of
`matchedBudget_twoBoxcar`, *no* admissible single-shot filter and *no* threshold can push the
average assignment error below the rational `1/125`.

Falsifiable as stated: a reported error below `1/125` at this template energy and noise PSD
refutes one of the binders — the declared identification (`hμ`, `hσV`), the whiteness assumption
(`hwhite`), the admissibility of the readout (`hadm`), a non-degenerate noise scale (`hσ`), or the
non-inverted deflection (`hμle`, which excludes negative-deflection readouts; that those are a
real case is the point of `filteredSNR_neg_matched_eq_neg_budget`). What it cannot be is a better
filter. Consumes 6EA's rational Gaussian enclosure `gaussianQ_two_ge_rational`, so no
floating-point `exp` enters anywhere.

That this binder set is *jointly satisfiable* is not left to the reader:
`error_floor_twoBoxcar_closed` exhibits a model and derives the floor with no hypotheses at all. -/
theorem error_floor_twoBoxcar_witness {V : (ℝ → ℝ) → ℝ}
    (hwhite : IsWhiteFilteredVariance V 1 2)
    {h : ℝ → ℝ} (hadm : IsAdmissibleFilter 2 (fun x => 2 * boxcar 2 x) h)
    {μ₀ μ₁ σ t : ℝ} (hσ : 0 < σ) (hμle : μ₀ ≤ μ₁)
    (hμ : μ₁ - μ₀ = ∫ x in (0:ℝ)..2, h x * (2 * boxcar 2 x)) (hσV : σ = √(V h)) :
    (1:ℝ) / 125 ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t) := by
  have hfloor := error_floor_from_budget (t := t) hwhite one_pos (by norm_num) hadm
    intervalIntegrable_twoBoxcar_sq hσ hμle hμ hσV
  rw [matchedBudget_twoBoxcar] at hfloor
  norm_num at hfloor
  exact le_trans gaussianQ_two_ge_rational hfloor

/-- **The unsigned saturation characterization is FALSE — a flat refutation.**

The tempting simplification of `filteredSNR_eq_budget_iff` — "saturation happens exactly when
`h` is a.e. *some* multiple of the template", dropping the positivity of the multiple — does not
merely lose information, it is **false**, and this refutes it directly rather than recording the
fact in prose. The counterexample is `h = −s` at `c = −1`: Cauchy–Schwarz is saturated in
magnitude, yet the realized ratio is `−matchedBudget ≠ matchedBudget`.

Kernel-checked no-go; the settled fork is `6eb-unsigned-matched-saturation-characterization`
(`KERNEL_NOGO_REGISTRY`). Any future restatement of the equality case must carry the sign. -/
theorem unsigned_saturation_characterization_false {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀)
    {s : ℝ → ℝ} (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T)
    (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) :
    ¬ (∀ h : ℝ → ℝ, IsAdmissibleFilter T s h →
        (∃ c : ℝ, h =ᵐ[volume.restrict (Set.Ioc 0 T)] fun x => c * s x) →
        filteredSNR V T s h = matchedBudget S₀ T s) := by
  intro hall
  have hadm : IsAdmissibleFilter T s (fun x => -s x) := by
    refine ⟨?_, ?_⟩
    · have hrw : (fun x => (-s x) ^ 2) = fun x => s x ^ 2 := by funext x; ring
      rw [hrw]; exact hs
    · have hrw : (fun x => (-s x) * s x) = fun x => -(s x ^ 2) := by funext x; ring
      rw [hrw]; exact hs.neg
  have hmem : ∃ c : ℝ, (fun x => -s x) =ᵐ[volume.restrict (Set.Ioc 0 T)] fun x => c * s x :=
    ⟨-1, Filter.Eventually.of_forall (fun x => by ring)⟩
  have hpos : 0 < matchedBudget S₀ T s :=
    Real.sqrt_pos.mpr (by positivity)
  have hneg := filteredSNR_neg_matched_eq_neg_budget hwhite hS hCpos
  rw [hall _ hadm hmem] at hneg
  linarith

/-! ### The power-domain carve-out, kernel-backed rather than asserted -/

/-- **Power (squared) deflection-to-noise ratio** — the quantity in which the *sign* of the filter
genuinely drops out. Shipped only so that the settled fork's power-domain carve-out can be stated
as theorems (`powerSNR_smul_eq_budget_sq`, `power_unsigned_characterization_false`) rather than
trusted as prose. -/
noncomputable def filteredPowerSNR (V : (ℝ → ℝ) → ℝ) (T : ℝ) (s h : ℝ → ℝ) : ℝ :=
  (∫ x in (0:ℝ)..T, h x * s x) ^ 2 / V h

/-- **In the power domain the sign really does drop out — but `c ≠ 0` does not.**

For *any* non-zero multiple of the template, positive or negative, the power SNR equals
`matchedBudget²`. This is the correct form of the carve-out recorded in the settled fork
`6eb-unsigned-matched-saturation-characterization`. -/
theorem powerSNR_smul_eq_budget_sq {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀)
    {s : ℝ → ℝ} (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) {c : ℝ} (hc : c ≠ 0) :
    filteredPowerSNR V T s (fun x => c * s x) = matchedBudget S₀ T s ^ 2 := by
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  have hnum : (∫ x in (0:ℝ)..T, (c * s x) * s x) = c * C := by
    rw [hC, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  have hsq : (∫ x in (0:ℝ)..T, (c * s x) ^ 2) = c ^ 2 * C := by
    rw [hC, ← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  have hVh : V (fun x => c * s x) = S₀ / 2 * (c ^ 2 * C) := by
    rw [hwhite (fun x => c * s x), hsq]
  unfold filteredPowerSNR matchedBudget
  rw [hnum, hVh, ← hC, Real.sq_sqrt (by positivity)]
  have hcsq : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  field_simp

/-- **The power-domain carve-out still needs `c ≠ 0`.**

Dropping the non-vanishing condition makes the *power* characterization false too, for a reason
independent of the sign: the **zero filter** satisfies the unsigned membership condition at
`c = 0` and realizes power SNR `0`, not `matchedBudget²`. Physically `c = 0` is a
**vanishing-responsivity readout chain** — precisely the degenerate branch the downstream
electrothermal phases carry (`Electrothermal.ETFModel.responsivityETF`'s `R = 0` disclosure), so
this is not a pathological corner for these consumers.

Shipped because the settled fork's carve-out sentence would otherwise be prose a consumer could
act on incorrectly; with this theorem the correct scope (`∃ c ≠ 0`) is kernel-checked.

Carries **neither** a whiteness binder nor template integrability: the zero filter defeats the
statement for *any* variance functional `V`, so requiring `IsWhiteFilteredVariance` would only
narrow the refutation. -/
theorem power_unsigned_characterization_false {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ} (hS : 0 < S₀)
    {s : ℝ → ℝ} (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) :
    ¬ (∀ h : ℝ → ℝ, IsAdmissibleFilter T s h →
        (∃ c : ℝ, h =ᵐ[volume.restrict (Set.Ioc 0 T)] fun x => c * s x) →
        filteredPowerSNR V T s h = matchedBudget S₀ T s ^ 2) := by
  intro hall
  have hadm : IsAdmissibleFilter T s (fun _ => (0:ℝ)) := by
    refine ⟨?_, ?_⟩
    · simp
    · simp
  have hmem : ∃ c : ℝ,
      (fun _ => (0:ℝ)) =ᵐ[volume.restrict (Set.Ioc 0 T)] fun x => c * s x :=
    ⟨0, Filter.Eventually.of_forall (fun x => by ring)⟩
  have hzero : filteredPowerSNR V T s (fun _ => (0:ℝ)) = 0 := by
    unfold filteredPowerSNR
    have hnum : (∫ x in (0:ℝ)..T, (0:ℝ) * s x) = 0 := by simp
    rw [hnum]
    simp
  have hbudget : 0 < matchedBudget S₀ T s ^ 2 := by
    unfold matchedBudget
    rw [Real.sq_sqrt (by positivity)]
    positivity
  rw [hall _ hadm hmem] at hzero
  linarith

/-- **The ceiling genuinely discriminates — a strictly sub-optimal admissible filter.**

The linear ramp `h(x) = x` read against the unit boxcar template on `[0,1]` in white noise of
one-sided PSD `S₀ = 2` realizes `√3/2 ≈ 0.866`, strictly below the budget `1`. So
`filteredSNR_le_matchedBudget` is not an inequality that everything saturates: mismatch costs
real SNR, which is what makes `filteredSNR_eq_budget_iff`'s characterization non-empty content.

The exact analogue of Wave 1's `enbw_ramp_gt_half`, and computed on the same ramp. The ramp's
**membership in the admissible class is part of the statement** — without it a "sub-optimal
admissible filter" claim would not establish that the witness lies in the class being bounded. -/
theorem filteredSNR_ramp_lt_budget {V : (ℝ → ℝ) → ℝ}
    (hwhite : IsWhiteFilteredVariance V 2 1) :
    IsAdmissibleFilter 1 (boxcar 1) (fun x => x) ∧
      filteredSNR V 1 (boxcar 1) (fun x => x) < matchedBudget 2 1 (boxcar 1) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (continuous_id.pow 2).intervalIntegrable 0 1
  · exact (continuous_id.intervalIntegrable 0 1).congr
      (fun x hx => by rw [← boxcar_eqOn_uIoc 1 (by norm_num) hx]; simp)
  have hnum : (∫ x in (0:ℝ)..1, x * boxcar 1 x) = 1 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => x)
      (fun x hx => by rw [boxcar_eqOn 1 (by norm_num) hx, mul_one])]
    rw [integral_id]; norm_num
  have hVh : V (fun x => x) = 1 / 3 := by
    rw [hwhite (fun x => x)]
    rw [show (∫ x in (0:ℝ)..1, x ^ 2) = 1 / 3 by rw [integral_pow]; norm_num]
    norm_num
  have hbud : matchedBudget 2 1 (boxcar 1) = 1 := by
    unfold matchedBudget
    rw [integral_boxcar_sq 1 (by norm_num)]
    rw [show (2:ℝ) * 1 / 2 = 1 by norm_num, Real.sqrt_one]
  rw [hbud]
  unfold filteredSNR
  rw [hnum, hVh]
  rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num))]
  have h4 : (1:ℝ) / 2 = √(1 / 4) := by
    rw [show (1:ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The composed floor, closed: no hypotheses at all.**

`error_floor_twoBoxcar_witness` is conditional on six binders, which leaves open the (real)
possibility that they are jointly unsatisfiable and the floor vacuous. They are not: taking the
matched filter `h = s = 2·𝟙[0,2]` against the canonical white variance functional
`V h = ½·∫₀² h²` gives `μ₁ − μ₀ = ∫₀² s² = 8`, `σ = √(V s) = √4 = 2`, and the resulting
average assignment error at any threshold — here the midpoint `t = 4` — is at least `1/125`.

This is the non-vacuity certificate for the whole Wave-3 → 6EA composition: a fully closed,
rational, floating-point-free lower bound on a detector error. -/
theorem error_floor_twoBoxcar_closed :
    (1:ℝ) / 125 ≤ avgAssignmentError (thrErr0 0 2 4) (thrErr1 8 2 4) := by
  set s : ℝ → ℝ := fun x => 2 * boxcar 2 x with hs
  set V : (ℝ → ℝ) → ℝ := fun h => 1 / 2 * ∫ x in (0:ℝ)..2, h x ^ 2 with hV
  have hwhite : IsWhiteFilteredVariance V 1 2 := by
    intro h; rw [hV]
  have hadm : IsAdmissibleFilter 2 s s := by
    refine ⟨intervalIntegrable_twoBoxcar_sq, ?_⟩
    have hrw : (fun x => s x * s x) = fun x => s x ^ 2 := by funext x; rw [sq]
    rw [hrw]; exact intervalIntegrable_twoBoxcar_sq
  have hE : (∫ x in (0:ℝ)..2, s x ^ 2) = 8 := integral_twoBoxcar_sq
  have hdefl : (8:ℝ) - 0 = ∫ x in (0:ℝ)..2, s x * s x := by
    have hrw : (fun x => s x * s x) = fun x => s x ^ 2 := by funext x; rw [sq]
    rw [hrw, hE]; norm_num
  have hVs : V s = 4 := by rw [hV]; simp only []; rw [hE]; norm_num
  have hsig : (2:ℝ) = √(V s) := by
    rw [hVs, show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact error_floor_twoBoxcar_witness (t := 4) hwhite hadm (by norm_num) (by norm_num)
    hdefl hsig

/-! ## The factor-2 seam, made detectable

Wave 1's settled fork `6eb-enbw-convention-falsifier-shape` requires that any falsifier in this
family target a **mixed** pairing rather than asserting a convention is "wrong". Wave 3 introduces
a fresh factor-2 seam — the separation `z = budget/2` against the budget itself — so it owes a
detectability theorem for exactly that mix. -/

/-- **The `budget` / `budget/2` mix is detectable.** Feeding `matchedBudget` to 6EA's threshold
algebra where the midpoint convention wants `matchedBudget/2` is not a harmless relabelling: the
two provably differ whenever the template energy is positive.

At the concrete witness the consequence is large — `Q(2) ≈ 2.3·10⁻²` against
`Q(4) ≈ 3.2·10⁻⁵`, nearly three orders of magnitude in the error floor — so this is the seam most
worth having kernel-checked. -/
theorem matchedBudget_half_ne_matchedBudget {S₀ T : ℝ} (hS : 0 < S₀) {s : ℝ → ℝ}
    (hCpos : 0 < ∫ x in (0:ℝ)..T, s x ^ 2) :
    matchedBudget S₀ T s / 2 ≠ matchedBudget S₀ T s := by
  have hpos : 0 < matchedBudget S₀ T s := Real.sqrt_pos.mpr (by positivity)
  intro h
  linarith

/-- **The layer closes: for a boxcar template the optimal filter is Wave 1's floor-saturating
boxcar.** Matched-filter optimality and the ENBW realizability floor pick out the *same* filter,
so "Wave 3 closes the layer" is a theorem rather than a narrative claim: the filter that attains
the deflection ceiling is exactly the one that attains `ENBW·T = 1/2`. -/
theorem matched_filter_of_boxcar_saturates_enbw_floor {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 < T) :
    filteredSNR V T (boxcar T) (boxcar T) = matchedBudget S₀ T (boxcar T) ∧
      enbw (boxcar T) T * T = 1 / 2 := by
  have hCpos : 0 < ∫ x in (0:ℝ)..T, boxcar T x ^ 2 := by
    rw [integral_boxcar_sq T hT.le]; exact hT
  refine ⟨filteredSNR_matched_eq_budget hwhite hS hCpos, ?_⟩
  rw [enbw_boxcar T hT]
  field_simp

/-! ## Degenerate branches, disclosed -/

/-- **The zero-variance branch is junk, and is disclosed as such.** A filter whose output
variance vanishes has `filteredSNR = 0` by Lean's total division, not `∞`. The optimality bound
holds there vacuously; every *equality* statement above therefore carries `0 < ∫₀ᵀ s²` (and, for
the characterization, derives `0 < ∫₀ᵀ h²`) rather than relying on this branch. -/
theorem filteredSNR_of_variance_eq_zero {V : (ℝ → ℝ) → ℝ} {T : ℝ} {s h : ℝ → ℝ}
    (hV : V h = 0) : filteredSNR V T s h = 0 := by
  unfold filteredSNR
  rw [hV, Real.sqrt_zero, div_zero]

end SKEFTHawking.Detection
