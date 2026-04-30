/-
Copyright (c) 2026 SK-EFT-Hawking project. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

Phase 6g.2-curve-theoretic Wave 9 Session 1 — Curve-pullback Riccati
comparison bridge.

Discharges the parked Mathlib-PR-style follow-on from Phase 6g.2-curve-
theoretic Wave (2026-04-30): the `riccati_compare` hypothesis of
`IsCurveTheoreticPenroseHypothesis` is derived substantively from a
Raychaudhuri-curve hypothesis `dθ/dλ ≤ -θ²/3` plus initial condition
`θ(0) = θ₀ < 0` and the focal-time identity `lam_focus = -3/θ₀`.

The substantive content is the **Riccati comparison theorem**: under the
Raychaudhuri-curve hypothesis on `[0, lam_focus)`, the curve-level
expansion `θ(λ)` is bounded above by the Riccati closed-form
`riccatiSolution θ₀ λ` throughout the focal window.

**Mathematical content (Wald §9.2 / Hawking-Ellis 1973 §4.4 / Senovilla-
Garfinkle 2015 review §4):** the standard Raychaudhuri-comparison argument
via the monotone-transform `g(λ) := 1/θ(λ)`. The key computation is

    g'(λ) = -θ'(λ)/(θ(λ))²  ≥  (θ(λ))²/3 / (θ(λ))²  =  1/3,

using `θ'(λ) ≤ -(θ(λ))²/3` and `θ(λ) < 0` (so `(θ(λ))² > 0`). By the
mean-value-theorem, `g(λ) - g(0) ≥ λ/3`, i.e., `1/θ(λ) ≥ 1/θ₀ + λ/3 =
1/riccatiSolution(θ₀, λ)`. Both sides are negative on the focal window,
so the reciprocal-comparison inverts to `θ(λ) ≤ riccatiSolution(θ₀, λ)`.

**First formalization in any proof assistant** (per Phase 6f audit §3E)
of the Raychaudhuri-Riccati comparison theorem at the curve-level scope,
discharging the `riccati_compare` Mathlib-PR-shape hypothesis introduced
in `PenroseSingularityCurveTheoretic.IsCurveTheoreticPenroseHypothesis`
on 2026-04-30.

**Bundle-target alignment:** lifts as **D3 §24** (the headline
correctness-push section, completing the 2026-04-30 wave's Mathlib-PR
follow-on) per `PAPER_DRAFT_MAPPING.md` Phase 6g addendum.
-/
import SKEFTHawking.PenroseSingularity
import SKEFTHawking.PenroseSingularityCurveTheoretic
import SKEFTHawking.FocalPoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace SKEFTHawking.RiccatiComparison

open Set
open SKEFTHawking.PenroseSingularity SKEFTHawking.FocalPoint
open SKEFTHawking.PenroseSingularityCurveTheoretic

/-! ## §1 Raychaudhuri-curve predicate

We encode the curve-level Raychaudhuri hypothesis on the focal window
`[0, lam_focus)`: an expansion scalar `θ : ℝ → ℝ` with explicit
derivative `θ' : ℝ → ℝ`, satisfying the Raychaudhuri inequality + sign
+ initial condition.

The choice of `Ico 0 lam_focus` for the continuous-on side and
`Ioo 0 lam_focus` for the differentiable + bound sides matches the
mean-value-theorem hypothesis pattern of
`Mathlib.Analysis.Calculus.Deriv.MeanValue.Convex.mul_sub_le_image_sub_of_le_deriv`,
which we consume in the comparison theorem below.
-/

/--
**`IsRaychaudhuriCurve θ θ' θ₀ lam_focus`:** the curve-level
Raychaudhuri hypothesis on the focal window `[0, lam_focus)`. The
expansion scalar `θ : ℝ → ℝ` has explicit derivative `θ' : ℝ → ℝ` on
the open interval `(0, lam_focus)` with:
- `initial_value` — `θ(0) = θ₀` (initial condition);
- `continuous_on_focal` — `θ` is continuous on `[0, lam_focus)`;
- `hasDerivAt_interior` — `θ` has derivative `θ'(λ)` at every
  `λ ∈ (0, lam_focus)`;
- `expansion_neg` — the trapped-surface initial condition propagates:
  `θ(λ) < 0` throughout `[0, lam_focus)`;
- `raychaudhuri_bound` — the substantive Raychaudhuri inequality at
  dimension 4 (n = 4): `θ'(λ) ≤ -(θ(λ))²/3` on `(0, lam_focus)`.

This is the substantive curve-level content: the Raychaudhuri equation
at the abstracted-trace scope (Phase 6g.2-curve Session 3) descends to
this curve-pullback predicate via the manifold-level derivative on the
geodesic congruence.
-/
structure IsRaychaudhuriCurve
    (θ θ' : ℝ → ℝ) (θ₀ lam_focus : ℝ) : Prop where
  /-- Initial condition: `θ(0) = θ₀`. -/
  initial_value : θ 0 = θ₀
  /-- Continuity on the half-open focal window. -/
  continuous_on_focal : ContinuousOn θ (Set.Ico (0 : ℝ) lam_focus)
  /-- Differentiability + explicit derivative on the open focal
  window. -/
  hasDerivAt_interior : ∀ lam ∈ Set.Ioo (0 : ℝ) lam_focus,
      HasDerivAt θ (θ' lam) lam
  /-- Trapped-surface initial condition propagates: `θ(λ) < 0`
  throughout `[0, lam_focus)`. -/
  expansion_neg : ∀ lam ∈ Set.Ico (0 : ℝ) lam_focus, θ lam < 0
  /-- Raychaudhuri inequality at n = 4: `θ'(λ) ≤ -(θ(λ))²/3` on
  `(0, lam_focus)`. -/
  raychaudhuri_bound : ∀ lam ∈ Set.Ioo (0 : ℝ) lam_focus,
      θ' lam ≤ -(θ lam)^2 / 3

/-! ## §2 Reciprocal-derivative auxiliary lemma

The substantive computation: under `IsRaychaudhuriCurve`, the
reciprocal `(θ(·))⁻¹` has derivative `≥ 1/3` on the open focal window.
This is the substantive sign computation that produces the comparison.
-/

/--
**Reciprocal-derivative bound:** under `IsRaychaudhuriCurve`, for every
`λ ∈ (0, lam_focus)`, the reciprocal expansion `(θ(·))⁻¹` has derivative
at `λ` equal to `-θ'(λ) / (θ(λ))²`, which is `≥ 1/3`.

This is the load-bearing substantive content of the comparison
argument: from `θ'(λ) ≤ -(θ(λ))²/3` and `(θ(λ))² > 0`, conclude
`-θ'(λ) / (θ(λ))² ≥ 1/3`. The derivative computation uses
`HasDerivAt.inv`, and the bound uses `div_le_div_of_nonneg_right` +
sign analysis.
-/
theorem hasDerivAt_recipExpansion
    {θ θ' : ℝ → ℝ} {θ₀ lam_focus : ℝ}
    (h : IsRaychaudhuriCurve θ θ' θ₀ lam_focus)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) lam_focus) :
    HasDerivAt (fun x => (θ x)⁻¹) (-θ' lam / (θ lam)^2) lam := by
  have h_θ_neg : θ lam < 0 := h.expansion_neg lam ⟨le_of_lt hlam.1, hlam.2⟩
  have h_θ_ne : θ lam ≠ 0 := ne_of_lt h_θ_neg
  have h_deriv_θ : HasDerivAt θ (θ' lam) lam := h.hasDerivAt_interior lam hlam
  have h_inv := h_deriv_θ.inv h_θ_ne
  -- HasDerivAt.inv gives derivative -θ' lam / (θ lam)^2
  convert h_inv using 1

/--
**Reciprocal-derivative ≥ 1/3:** under `IsRaychaudhuriCurve`, for every
`λ ∈ (0, lam_focus)`, the reciprocal-expansion derivative is bounded
below by `1/3`. This is the substantive bound that consumes the
Raychaudhuri inequality.
-/
theorem recipExpansion_deriv_ge_one_third
    {θ θ' : ℝ → ℝ} {θ₀ lam_focus : ℝ}
    (h : IsRaychaudhuriCurve θ θ' θ₀ lam_focus)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) lam_focus) :
    (1 : ℝ) / 3 ≤ -θ' lam / (θ lam)^2 := by
  have h_θ_neg : θ lam < 0 := h.expansion_neg lam ⟨le_of_lt hlam.1, hlam.2⟩
  have h_θ_ne : θ lam ≠ 0 := ne_of_lt h_θ_neg
  have h_θ_sq_pos : 0 < (θ lam)^2 := by
    have : (θ lam)^2 = (θ lam) * (θ lam) := by ring
    rw [this]; exact mul_pos_of_neg_of_neg h_θ_neg h_θ_neg
  have h_bound : θ' lam ≤ -(θ lam)^2 / 3 := h.raychaudhuri_bound lam hlam
  -- We need: 1/3 ≤ -θ' lam / (θ lam)^2
  -- From h_bound: θ' lam ≤ -(θ lam)^2 / 3
  --       ⟹  -θ' lam ≥ (θ lam)^2 / 3
  --       ⟹  -θ' lam / (θ lam)^2 ≥ ((θ lam)^2 / 3) / (θ lam)^2 = 1/3
  rw [le_div_iff₀ h_θ_sq_pos]
  -- Goal: (1 / 3) * (θ lam)^2 ≤ -θ' lam
  linarith

/-! ## §3 Wave-headline Riccati comparison theorem

The substantive Riccati comparison: under `IsRaychaudhuriCurve` plus
the focal-time identity `lam_focus = -3/θ₀` with `θ₀ < 0`, conclude
`θ(λ) ≤ riccatiSolution θ₀ λ` throughout `[0, lam_focus)`.
-/

/--
**Riccati comparison theorem (Wave 9 Session 1 headline).**
Under the curve-level Raychaudhuri hypothesis `IsRaychaudhuriCurve θ θ'
θ₀ lam_focus` plus the focal-configuration identity `lam_focus = -3/θ₀`
(with `θ₀ < 0`), the curve-level expansion `θ(λ)` is bounded above by
the Riccati closed-form `riccatiSolution θ₀ λ` throughout the focal
window `[0, lam_focus)`.

**Substantive content:** this discharges the
`IsCurveTheoreticPenroseHypothesis.riccati_compare` hypothesis from a
genuine Raychaudhuri inequality + sign + initial condition, closing the
Mathlib-PR-style follow-on parked at the close of the 2026-04-30 wave.

**Proof:** apply `Convex.mul_sub_le_image_sub_of_le_deriv` to the
reciprocal `(θ(·))⁻¹` on the convex set `Icc 0 lam` (for any
`lam ∈ [0, lam_focus)`) with constant `C = 1/3`. From
`recipExpansion_deriv_ge_one_third`, the reciprocal's derivative is
≥ 1/3 on the interior `Ioo 0 lam`, so the MVT gives
`(λ - 0) * (1/3) ≤ (θ(λ))⁻¹ - (θ(0))⁻¹`. Substitute `θ(0) = θ₀`:
`(θ(λ))⁻¹ ≥ θ₀⁻¹ + λ/3 = (riccatiSolution θ₀ λ)⁻¹`. Both sides are
negative (by `expansion_neg` for `θ` and by `riccatiSolution_neg` for
the Riccati formula), so the reciprocal-comparison inverts:
`θ(λ) ≤ riccatiSolution θ₀ λ`.
-/
theorem riccati_comparison_on_focal_window
    {θ θ' : ℝ → ℝ} {θ₀ lam_focus : ℝ}
    (h : IsRaychaudhuriCurve θ θ' θ₀ lam_focus)
    (h_focal : IsFocalConfigurationFor θ₀ lam_focus)
    (lam : ℝ) (hlam : lam ∈ Set.Ico (0 : ℝ) lam_focus) :
    θ lam ≤ riccatiSolution θ₀ lam := by
  obtain ⟨hθ₀_neg, h_focal_eq⟩ := h_focal
  -- Set up the convex set Icc 0 lam ⊆ Ico 0 lam_focus
  have h_lam_nonneg : (0 : ℝ) ≤ lam := hlam.1
  have h_lam_lt : lam < lam_focus := hlam.2
  -- Compute denominator in the Riccati solution
  have h_θ₀_ne : θ₀ ≠ 0 := ne_of_lt hθ₀_neg
  have h_lam_focus_pos : 0 < lam_focus := by
    rw [h_focal_eq]; exact focusingTime_pos θ₀ hθ₀_neg
  -- Goal: θ lam ≤ θ₀ / (1 + θ₀ * lam / 3)
  -- Strategy: show 1/(θ lam) ≥ 1/(riccatiSolution θ₀ lam),
  -- both negative, hence θ lam ≤ riccatiSolution θ₀ lam.
  --
  -- The reciprocal of the Riccati solution is θ₀⁻¹ + lam/3:
  --   1/r(lam) = (1 + θ₀ lam/3)/θ₀ = θ₀⁻¹ + lam/3.
  --
  -- Apply mul_sub_le_image_sub_of_le_deriv to (θ ·)⁻¹ on Icc 0 lam
  -- with C = 1/3, x = 0, y = lam.
  -- This gives: (1/3) * (lam - 0) ≤ (θ lam)⁻¹ - (θ 0)⁻¹
  -- i.e., (θ lam)⁻¹ ≥ θ₀⁻¹ + lam/3 = 1/r(lam).
  have h_θ_lam_neg : θ lam < 0 := h.expansion_neg lam hlam
  have h_θ_lam_ne : θ lam ≠ 0 := ne_of_lt h_θ_lam_neg
  have h_θ_zero_eq : θ 0 = θ₀ := h.initial_value
  have h_θ_zero_neg : θ 0 < 0 := by rw [h_θ_zero_eq]; exact hθ₀_neg
  -- Riccati denominator positive on focal window
  have h_riccati_neg : riccatiSolution θ₀ lam < 0 :=
    riccatiSolution_neg θ₀ lam hθ₀_neg (by rw [h_focal_eq] at h_lam_lt; exact h_lam_lt)
  have h_riccati_ne : riccatiSolution θ₀ lam ≠ 0 := ne_of_lt h_riccati_neg
  -- Step 1: ContinuousOn (·)⁻¹ ∘ θ on Icc 0 lam
  have h_Icc_subset_Ico : Icc 0 lam ⊆ Ico (0 : ℝ) lam_focus := fun x hx =>
    ⟨hx.1, lt_of_le_of_lt hx.2 h_lam_lt⟩
  have h_θ_continuous_Icc : ContinuousOn θ (Icc (0 : ℝ) lam) :=
    h.continuous_on_focal.mono h_Icc_subset_Ico
  -- θ ≠ 0 on Icc 0 lam (from expansion_neg)
  have h_θ_ne_on_Icc : ∀ x ∈ Icc (0 : ℝ) lam, θ x ≠ 0 := fun x hx =>
    ne_of_lt (h.expansion_neg x (h_Icc_subset_Ico hx))
  have h_recip_continuous : ContinuousOn (fun x => (θ x)⁻¹) (Icc (0 : ℝ) lam) := by
    intro x hx
    exact (h_θ_continuous_Icc x hx).inv₀ (h_θ_ne_on_Icc x hx)
  -- Step 2: DifferentiableOn (·)⁻¹ ∘ θ on interior (Icc 0 lam) = Ioo 0 lam
  have h_int_eq : interior (Icc (0 : ℝ) lam) = Ioo 0 lam := by
    by_cases h_lam_pos : 0 < lam
    · exact interior_Icc
    · rw [not_lt] at h_lam_pos
      have h_lam_eq : lam = 0 := le_antisymm h_lam_pos h_lam_nonneg
      simp [h_lam_eq]
  have h_Ioo_subset : Ioo (0 : ℝ) lam ⊆ Ioo 0 lam_focus := fun x hx =>
    ⟨hx.1, lt_trans hx.2 h_lam_lt⟩
  have h_recip_differentiable :
      DifferentiableOn ℝ (fun x => (θ x)⁻¹) (interior (Icc (0 : ℝ) lam)) := by
    rw [h_int_eq]
    intro x hx
    exact (hasDerivAt_recipExpansion h x (h_Ioo_subset hx)).differentiableAt.differentiableWithinAt
  -- Step 3: deriv (·)⁻¹ ∘ θ ≥ 1/3 on interior (Icc 0 lam) = Ioo 0 lam
  have h_recip_deriv_ge :
      ∀ x ∈ interior (Icc (0 : ℝ) lam), (1 : ℝ) / 3 ≤ deriv (fun y => (θ y)⁻¹) x := by
    intro x hx
    rw [h_int_eq] at hx
    have h_has := hasDerivAt_recipExpansion h x (h_Ioo_subset hx)
    rw [h_has.deriv]
    exact recipExpansion_deriv_ge_one_third h x (h_Ioo_subset hx)
  -- Step 4: apply mul_sub_le_image_sub_of_le_deriv with x = 0, y = lam
  have h_convex : Convex ℝ (Icc (0 : ℝ) lam) := convex_Icc 0 lam
  have h_zero_in : (0 : ℝ) ∈ Icc 0 lam := ⟨le_refl _, h_lam_nonneg⟩
  have h_lam_in : lam ∈ Icc (0 : ℝ) lam := ⟨h_lam_nonneg, le_refl _⟩
  have h_mvt :=
    h_convex.mul_sub_le_image_sub_of_le_deriv h_recip_continuous h_recip_differentiable
      h_recip_deriv_ge 0 h_zero_in lam h_lam_in h_lam_nonneg
  -- h_mvt : 1/3 * (lam - 0) ≤ (θ lam)⁻¹ - (θ 0)⁻¹
  rw [sub_zero] at h_mvt
  -- Step 5: convert to (θ lam)⁻¹ ≥ θ₀⁻¹ + lam/3
  have h_recip_lower : (1 : ℝ) / 3 * lam + (θ 0)⁻¹ ≤ (θ lam)⁻¹ := by linarith
  rw [h_θ_zero_eq] at h_recip_lower
  -- (θ lam)⁻¹ ≥ θ₀⁻¹ + lam/3
  -- Now substitute that (riccatiSolution θ₀ lam)⁻¹ = θ₀⁻¹ + lam/3
  have h_riccati_recip : (riccatiSolution θ₀ lam)⁻¹ = θ₀⁻¹ + lam / 3 := by
    unfold riccatiSolution
    rw [inv_div]
    field_simp
  -- (θ lam)⁻¹ ≥ (riccatiSolution θ₀ lam)⁻¹
  have h_recip_compare : (riccatiSolution θ₀ lam)⁻¹ ≤ (θ lam)⁻¹ := by
    rw [h_riccati_recip]; linarith
  -- Step 6: invert reciprocal-comparison on negatives
  -- 1/x ≥ 1/y, x < 0, y < 0 ⟹ y ≤ x... wait, careful: we have (1/r) ≤ (1/θ).
  -- Let a := θ lam (< 0), b := riccatiSolution θ₀ lam (< 0). Have b⁻¹ ≤ a⁻¹.
  -- Multiply both sides by ab > 0: a ≤ b. So θ lam ≤ riccatiSolution θ₀ lam. ✓
  have h_ab_pos : 0 < (θ lam) * (riccatiSolution θ₀ lam) :=
    mul_pos_of_neg_of_neg h_θ_lam_neg h_riccati_neg
  -- From (riccatiSolution)⁻¹ ≤ (θ)⁻¹, multiply both sides by θ lam * riccatiSolution
  -- Use: a⁻¹ ≤ b⁻¹ + a, b same sign ⟹ b ≤ a... wait let me redo.
  -- We have b⁻¹ ≤ a⁻¹ where a = θ lam < 0, b = riccatiSolution < 0.
  -- Multiply both sides by ab (positive since both negative): ab/b ≤ ab/a, i.e., a ≤ b.
  -- So θ lam ≤ riccatiSolution θ₀ lam. ✓
  have h_mul_a : (riccatiSolution θ₀ lam)⁻¹ * (θ lam * riccatiSolution θ₀ lam) ≤
      (θ lam)⁻¹ * (θ lam * riccatiSolution θ₀ lam) :=
    mul_le_mul_of_nonneg_right h_recip_compare (le_of_lt h_ab_pos)
  have h_lhs : (riccatiSolution θ₀ lam)⁻¹ * (θ lam * riccatiSolution θ₀ lam) = θ lam := by
    rw [show (θ lam * riccatiSolution θ₀ lam) = riccatiSolution θ₀ lam * θ lam from by ring,
        ← mul_assoc, inv_mul_cancel₀ h_riccati_ne, one_mul]
  have h_rhs : (θ lam)⁻¹ * (θ lam * riccatiSolution θ₀ lam) = riccatiSolution θ₀ lam := by
    rw [← mul_assoc, inv_mul_cancel₀ h_θ_lam_ne, one_mul]
  linarith [h_lhs ▸ h_rhs ▸ h_mul_a]

/-! ## §4 Bridge to `IsCurveTheoreticPenroseHypothesis`

The Wave 9 Session 1 wave-completion content: package
`IsRaychaudhuriCurve` plus a (trivial) negative-`lam` extension into
`IsCurveTheoreticPenroseHypothesis`. The substantive content is the
focal-window comparison from §3; the negative-lam side is delegated as
a hypothesis (typically discharged by extending `θ` to all of `ℝ` via
the Riccati closed form, or by setting `θ` constant for `lam ≤ 0`).
-/

/--
**Bridge: `IsRaychaudhuriCurve ⟹ IsCurveTheoreticPenroseHypothesis`.**
Under `IsRaychaudhuriCurve θ θ' θ₀ lam_focus` plus
`IsFocalConfigurationFor θ₀ lam_focus` plus a negative-`lam` extension
hypothesis, conclude `IsCurveTheoreticPenroseHypothesis θ θ₀ lam_focus`.

The substantive content is the focal-window comparison
`θ lam ≤ riccatiSolution θ₀ lam` for `lam ∈ [0, lam_focus)`, which is
discharged via §3's `riccati_comparison_on_focal_window`. The
negative-lam case is taken as a hypothesis (the typical witness is
`θ lam := riccatiSolution θ₀ lam` on `lam < 0`, in which case the
comparison is `≤` reflexivity).
-/
theorem isRaychaudhuriCurve_toCurveTheoreticPenroseHypothesis
    {θ θ' : ℝ → ℝ} {θ₀ lam_focus : ℝ}
    (h : IsRaychaudhuriCurve θ θ' θ₀ lam_focus)
    (h_focal : IsFocalConfigurationFor θ₀ lam_focus)
    (h_neg_lam : ∀ lam : ℝ, lam < 0 → θ lam ≤ riccatiSolution θ₀ lam) :
    IsCurveTheoreticPenroseHypothesis θ θ₀ lam_focus where
  initial_expansion := h.initial_value
  focal_config := h_focal
  riccati_compare := by
    intro lam h_lam_lt_focus
    by_cases h_lam_neg : lam < 0
    · exact h_neg_lam lam h_lam_neg
    · rw [not_lt] at h_lam_neg
      exact riccati_comparison_on_focal_window h h_focal lam ⟨h_lam_neg, h_lam_lt_focus⟩

/-! ## §5 Substantive baseline witness

The Riccati function itself is a witness for `IsRaychaudhuriCurve`:
when `θ := riccatiSolution θ₀` with `θ' := -(riccatiSolution θ₀)²/3`,
the Raychaudhuri inequality is saturated to equality. This confirms
the predicate is non-vacuously inhabitable and exhibits the
substantive content of §3 reducing to ≤-reflexivity in the saturated
case.
-/

/--
**Substantive baseline witness:** the Riccati function `riccatiSolution
θ₀` is itself a `IsRaychaudhuriCurve` (saturated to equality) at
`(θ₀, lam_focus) = (-1, 3)`. The witness shows §3's substantive
comparison theorem is non-vacuous: when applied to the saturating
solution, it produces `riccatiSolution θ₀ lam ≤ riccatiSolution θ₀
lam`, which is `≤`-reflexivity, but the theorem's discharge of the
hypothesis is genuine (every conjunct of `IsRaychaudhuriCurve` is
load-bearing). -/
theorem riccatiSolution_isRaychaudhuriCurve_witness :
    IsRaychaudhuriCurve (riccatiSolution (-1)) (fun lam => -(riccatiSolution (-1) lam)^2 / 3)
      (-1) 3 where
  initial_value := riccatiSolution_at_zero (-1)
  continuous_on_focal := by
    intro x hx
    -- riccatiSolution (-1) x = -1 / (1 + (-1)*x/3); denominator positive on Ico 0 3.
    have h_denom_pos : 0 < 1 + (-1 : ℝ) * x / 3 :=
      riccatiSolution_denom_pos (-1) x (by norm_num) (by linarith [hx.2])
    have h_denom_ne : (1 + (-1 : ℝ) * x / 3) ≠ 0 := ne_of_gt h_denom_pos
    refine ContinuousAt.continuousWithinAt ?_
    unfold riccatiSolution
    exact (continuousAt_const).div (by fun_prop) h_denom_ne
  hasDerivAt_interior := by
    intro lam hlam
    -- Direct computation: r(λ) = -1 / (1 + (-1)·λ/3). r'(λ) = -1/(3 (1+(-1)λ/3)²) = -r²/3.
    unfold riccatiSolution
    have h_denom_pos : 0 < 1 + (-1 : ℝ) * lam / 3 :=
      riccatiSolution_denom_pos (-1) lam (by norm_num) (by linarith [hlam.2])
    have h_denom_ne : (1 + (-1 : ℝ) * lam / 3) ≠ 0 := ne_of_gt h_denom_pos
    -- denom(λ) = 1 + (-1)·λ/3, d/dλ = -1/3
    have h_deriv_denom :
        HasDerivAt (fun x : ℝ => 1 + (-1 : ℝ) * x / 3) ((-1 : ℝ) / 3) lam := by
      have h_id : HasDerivAt (fun x : ℝ => x) (1 : ℝ) lam := hasDerivAt_id lam
      have h_mul : HasDerivAt (fun x : ℝ => (-1 : ℝ) * x) ((-1 : ℝ) * 1) lam :=
        h_id.const_mul (-1 : ℝ)
      have h_div := h_mul.div_const (3 : ℝ)
      have h_add := (hasDerivAt_const lam (1 : ℝ)).add h_div
      convert h_add using 1
      ring
    -- Quotient rule: d/dλ [-1 / denom] = -(0·denom - (-1)·denom') / denom²
    --                                  = denom' · (-1) / denom²
    --                                  = ((-1)/3) · (-1) / denom² = (1/3) / denom².
    have h_const : HasDerivAt (fun _ : ℝ => (-1 : ℝ)) 0 lam := hasDerivAt_const lam (-1)
    have h_quot := h_const.div h_deriv_denom h_denom_ne
    -- h_quot : HasDerivAt (-1 / denom) ((0 * denom lam - (-1) * (-1/3)) / denom lam ^ 2) lam
    -- Now convert to -((-1/denom lam)^2 / 3)
    convert h_quot using 1
    field_simp
    ring
  expansion_neg := by
    intro lam hlam
    apply riccatiSolution_neg (-1) lam (by norm_num)
    linarith [hlam.2]
  raychaudhuri_bound := by
    intro lam _
    -- Equality saturates the inequality.
    rfl

/--
**Substantive composition: `IsCurveTheoreticPenroseHypothesis` for the
saturating Riccati solution via the §4 bridge.** Recovers the existing
`PenroseSingularityCurveTheoretic.penrose_curve_theoretic_baseline_witness`
through the newly-shipped Wave 9 Session 1 path: the bridge §4
applied to the §5 Riccati-saturating-solution witness produces an
`IsCurveTheoreticPenroseHypothesis (riccatiSolution (-1)) (-1) 3`
instance. The negative-`lam` hypothesis is `≤`-reflexivity (the same
function on both sides). This non-trivially consumes both the bridge
and the witness in a load-bearing composition, demonstrating the
wave-completion content end-to-end.
-/
theorem riccatiSolution_isCurveTheoreticPenroseHypothesis_via_bridge :
    IsCurveTheoreticPenroseHypothesis (riccatiSolution (-1)) (-1) 3 :=
  isRaychaudhuriCurve_toCurveTheoreticPenroseHypothesis
    riccatiSolution_isRaychaudhuriCurve_witness
    focalConfiguration_neg_one_three
    (fun _ _ => le_refl _)

/-! ## §7 Module summary marker

Phase 6g.2-curve-theoretic Wave 9 Session 1 — curve-pullback Riccati
comparison bridge.

**Substantive declarations shipped (5 + 1 marker):**

§1 — Curve-level Raychaudhuri predicate:
1. `IsRaychaudhuriCurve` (structure — substantive 5-conjunct bundle:
   `initial_value` + `continuous_on_focal` + `hasDerivAt_interior` +
   `expansion_neg` + `raychaudhuri_bound`).

§2 — Reciprocal-derivative auxiliary content:
2. `hasDerivAt_recipExpansion` (substantive: `HasDerivAt.inv` chain).
3. `recipExpansion_deriv_ge_one_third` (substantive: bound from
   Raychaudhuri + sign analysis).

§3 — Wave-headline Riccati comparison theorem:
4. `riccati_comparison_on_focal_window` (the load-bearing curve-level
   comparison `θ(λ) ≤ riccatiSolution θ₀ λ` on `[0, lam_focus)`,
   discharging the parked `riccati_compare` Mathlib-PR-shape hypothesis
   via `Convex.mul_sub_le_image_sub_of_le_deriv`).

§4 — Bridge to `IsCurveTheoreticPenroseHypothesis`:
5. `isRaychaudhuriCurve_toCurveTheoreticPenroseHypothesis` (substantive
   composition: §3 + negative-`lam` hypothesis ⟹
   `IsCurveTheoreticPenroseHypothesis` instance).

§5 — Substantive baseline witness:
6. `riccatiSolution_isRaychaudhuriCurve_witness` (Riccati function as
   self-witness with saturated Raychaudhuri inequality).

**Strengthening pre-pass discipline (applied prospectively):**
1. **Bundle redundancy** ✓ — the 5 conjuncts of `IsRaychaudhuriCurve`
   are independent (drop any one and the comparison fails: lose
   continuity and MVT fails; lose differentiability and reciprocal
   derivative is undefined; lose `expansion_neg` and the reciprocal
   bound's sign analysis fails; lose `raychaudhuri_bound` and the
   1/3-bound on the reciprocal derivative fails; lose `initial_value`
   and the Riccati closed-form's `θ₀⁻¹` doesn't connect to `(θ 0)⁻¹`).
2. **Quantitative connection** ✓ — comparison is the explicit
   closed-form `riccatiSolution θ₀ λ = θ₀ / (1 + θ₀ λ / 3)`; the bound
   `1/3` is the `n − 1 = 3` Raychaudhuri coefficient at `n = 4`;
   baseline witness exhibits `(-1, 3)` with the saturating solution.
3. **Cross-module bridge integrity** ✓ — body imports + calls
   `PenroseSingularity.{riccatiSolution, riccatiSolution_at_zero,
   riccatiSolution_neg, riccatiSolution_denom_pos, focusingTime_pos}`,
   `FocalPoint.{IsFocalConfigurationFor}`, and
   `PenroseSingularityCurveTheoretic.{IsCurveTheoreticPenroseHypothesis}`,
   plus Mathlib `Convex.mul_sub_le_image_sub_of_le_deriv` +
   `HasDerivAt.inv`.
4. **Trivial-discharge** ✓ — none of the §2–§4 theorems reduce to
   `rfl`/`decide`/tautology; each genuinely consumes the Raychaudhuri
   inequality + sign + initial condition + MVT machinery.
5. **Defining-the-conclusion** ✓ — the comparison theorem's conclusion
   is the explicit closed-form Riccati comparison, not a vacuous
   restatement of the hypothesis. The bridge's conclusion is an
   instance of an existing predicate, with every field exercised.

**Bundle-target alignment:** lifts as **D3 §24** (the headline
correctness-push section, completing the 2026-04-30 wave's Mathlib-PR
follow-on) per `PAPER_DRAFT_MAPPING.md` Phase 6g addendum.

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure; content lifts as D3 §24 + I1 sidebar).

**First formalization in any proof assistant** (per Phase 6f audit
§3E + this session's audit) of the Raychaudhuri-Riccati comparison
theorem at the curve-level scope. Mathlib has
`Convex.mul_sub_le_image_sub_of_le_deriv` + `HasDerivAt.inv`, but no
combined Raychaudhuri-Riccati-comparison content; no other proof
assistant (Coq, Isabelle/AFP, HOL Light, HOL4, Mizar, Agda) has the
chain in any form per the Phase 6f audit §3E. -/
theorem _phase6g_w9_session1_module_summary_marker : True := trivial

end SKEFTHawking.RiccatiComparison
