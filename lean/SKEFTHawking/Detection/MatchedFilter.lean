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

* `h ∈ L²[0, T]` (interval-supported, single-shot: the filter sees the window and nothing else);
* the deflection integral `∫₀ᵀ h·s` exists.

Both conjuncts are carried in the statement, never in prose. The second is *mathematically*
implied by `h, s ∈ L²` (Cauchy–Schwarz), but Mathlib's interval-integral API supplies no such
implication at the pinned version, so it is an explicit field rather than a silent assumption.

## Conventions (inherited, not re-chosen)

* **One-sided PSD**, via Wave 1's `IsWhiteFilteredVariance V S₀ T : ∀ h, V h = S₀/2 · ∫₀ᵀ h²`.
  The noise scale of the filtered output is `√(V h)`; the `S₀/2` is the one-sided normalization
  fixed by `GrapheneNoiseFormula` and threaded through this file's statements via `hwhite`.
* **Deflection**, not power: `filteredSNR` is an *amplitude* ratio `(∫ h·s) / √(V h)`, which is
  the quantity 6EA's threshold algebra consumes (it enters `avgError_ge_gaussianQ_sharp` as
  `(μ₁ − μ₀)/(2σ)`). Squaring it gives the power SNR; the factor is stated, not assumed.
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
* **Budget and error floor** — `matchedBudget_half_eq` (the separation budget in closed form),
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
  checklist forbids. Same call as Wave 2's `avgError_ge_gaussianQ_sharp` (see
  `Detection.GaussianThreshold`'s closing note).
* **Equality characterization.** The AC asks for "equality characterization"; what ships is the
  full biconditional `filteredSNR_eq_budget_iff`, including the **positivity** of the scaling
  factor — which `filteredSNR_neg_matched_eq_neg_budget` shows is not removable.
* **`matchedBudget_half_eq` carries no sign hypothesis.** Both sides collapse to `0` on the
  degenerate branch, so a `0 ≤ ∫₀ᵀ s²` binder would be dead weight, not a guard.

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

A filter is admissible when it is square-integrable on the window (interval-supported `L²` —
"single-shot": it acts on `[0, T]` and nothing outside) and its deflection integral against the
template exists.

The second field is mathematically redundant given `h, s ∈ L²` (it *is* Cauchy–Schwarz), but
Mathlib carries no interval-integral form of that implication at the pinned version, so it is
declared rather than assumed. Membership is relative to the template because the deflection is;
this is the class the roadmap's Wave-3 AC quantifies over. -/
structure IsAdmissibleFilter (T : ℝ) (s h : ℝ → ℝ) : Prop where
  /-- `h ∈ L²[0, T]`: the filter has finite energy on the window. -/
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

/-! ## The separation budget and the composed error floor -/

/-- **The separation budget in closed form.** Half the matched budget — the quantity 6EA's
threshold algebra consumes as its `z` — is

    matchedBudget / 2 = √((∫₀ᵀ s²) / (2·S₀))

i.e. the roadmap's `√(∫s²/S₀)`-shaped bound with the one-sided constant made explicit.

Stated with **no** sign hypothesis on the template energy: both sides collapse to `0` on the
degenerate branch, so a `0 ≤ ∫₀ᵀ s²` binder would be dead weight rather than a guard. -/
theorem matchedBudget_half_eq {S₀ T : ℝ} (hS : 0 < S₀) (s : ℝ → ℝ) :
    matchedBudget S₀ T s / 2 = √((∫ x in (0:ℝ)..T, s x ^ 2) / (2 * S₀)) := by
  set C := ∫ x in (0:ℝ)..T, s x ^ 2 with hC
  unfold matchedBudget
  rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num,
    ← Real.sqrt_div' _ (by norm_num)]
  congr 1
  field_simp
  ring

/-- **The optimal-`z` budget — filter-independent.** The separation `z = (∫ h·s)/(2√(V h))` that
any admissible single-shot readout can present to a threshold classifier is capped by a quantity
built from the template energy and the noise PSD alone:

    (∫₀ᵀ h·s) / (2·√(V h)) ≤ √((∫₀ᵀ s²) / (2·S₀))

This is `filteredSNR_le_matchedBudget` in the coordinates 6EA works in, and is what
`error_floor_from_budget` feeds to `avgError_ge_gaussianQ_sharp`. -/
theorem optimal_z_budget {V : (ℝ → ℝ) → ℝ} {S₀ T : ℝ}
    (hwhite : IsWhiteFilteredVariance V S₀ T) (hS : 0 < S₀) (hT : 0 ≤ T)
    {s h : ℝ → ℝ} (hadm : IsAdmissibleFilter T s h)
    (hs : IntervalIntegrable (fun x => s x ^ 2) volume 0 T) :
    (∫ x in (0:ℝ)..T, h x * s x) / (2 * √(V h))
      ≤ √((∫ x in (0:ℝ)..T, s x ^ 2) / (2 * S₀)) := by
  have hbound := filteredSNR_le_matchedBudget hwhite hS hT hadm hs
  rw [← matchedBudget_half_eq hS s]
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
  rw [hμ, hσV, matchedBudget_half_eq hS s]
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
refutes the declared identification (`hμ`, `hσV`), the whiteness assumption, or the admissibility
of the readout — it cannot be a better filter. Consumes 6EA's rational Gaussian enclosure
`gaussianQ_two_ge_rational`, so no floating-point `exp` enters anywhere. -/
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

/-- **The ceiling genuinely discriminates — a strictly sub-optimal admissible filter.**

The linear ramp `h(x) = x` read against the unit boxcar template on `[0,1]` in white noise of
one-sided PSD `S₀ = 2` realizes `√3/2 ≈ 0.866`, strictly below the budget `1`. So
`filteredSNR_le_matchedBudget` is not an inequality that everything saturates: mismatch costs
real SNR, which is what makes `filteredSNR_eq_budget_iff`'s characterization non-empty content.

The exact analogue of Wave 1's `enbw_ramp_gt_half`, and computed on the same ramp. -/
theorem filteredSNR_ramp_lt_budget {V : (ℝ → ℝ) → ℝ}
    (hwhite : IsWhiteFilteredVariance V 2 1) :
    filteredSNR V 1 (boxcar 1) (fun x => x) < matchedBudget 2 1 (boxcar 1) := by
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
