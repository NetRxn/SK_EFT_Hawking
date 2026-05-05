/-
Phase 6n.α Wave (G2 Resurgence) — Stage 1 Borel-action substrate.

Central deliverable: the closed-form Λ_UV = κ √A predictor from
the leading Borel-plane singularity location A in the dimensionless
expansion variable g = (ω/κ)².

The Python-side numerical infrastructure for this module lives at
`src/resurgence/borel.py:lambda_uv_estimate`. Validation against
synthetic Heller–Spalinski-style sequences in `tests/test_resurgence.py`.

DR §5: extracts Λ_UV from N=4 ratio-test extrapolation; full Padé–Borel
reconstruction needs N≥6 coefficients (currently shipped through order 7
in `src/core/formulas.py`).

References:
- Aniceto–Başar–Schiappa, Phys. Rep. 809 (2019) 1, arXiv:1802.10441
- Heller–Spalinski, PRL 115 (2015) 072501, arXiv:1503.07514
- Mera–Pedersen–Nikolić, PRL 115 (2015) 143001, arXiv:1502.06743
- Lit-Search/_Exploratory/Resurgence Theory and Schwinger–Keldysh EFT.md §5
-/
import SKEFTHawking.Resurgence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SKEFTHawking.Resurgence

/--
**Borel-action data for an SK-EFT gradient-expansion coefficient sequence.**

Bundles the three load-bearing facts about the Borel-plane singularity
structure: the action `A` (radius of convergence of the Borel transform),
its strict positivity, and the witnessing `IsGevrey1` predicate (which
encodes the factorial growth `|a n| ≤ n!/A^n`).

Tracked-hypothesis form: the existence of a finite positive Borel action
is itself a *prediction* the program must verify numerically (DR §5
caveat: with only orders 0–7 generated, the Gevrey-1 conjecture is
substantially supported but not formally proven). This structure
provides the Lean-level interface; the substantive verification lives
in the Python ratio-test diagnostic + Padé–Borel reconstruction at
`src/resurgence/borel.py`.
-/
structure BorelActionData (a : ℕ → ℝ) where
  /-- The Borel action — radius of convergence of the Borel transform. -/
  A : ℝ
  /-- Positivity of the Borel action. -/
  A_pos : 0 < A
  /-- The coefficient sequence is Gevrey-1 with this action. -/
  isGevrey1 : IsGevrey1 a A

/--
**Λ_UV-from-IR closed-form predictor: Λ_UV = κ · √A.**

Given an SK-EFT coefficient sequence whose dimensionless expansion
variable is `g = (ω/κ)²` (the natural variable of the SK-EFT gradient
expansion) and whose Borel transform has a leading singularity at
the dimensionless action `A`, the substrate UV cutoff Λ_UV is
predicted by the closed form `Λ_UV = κ · √A`.

The corresponding non-perturbative correction is
`δ_NP(ω) = S₁ · exp(-(Λ_UV/ω)² · A)`, exponentially suppressed at
frequencies `ω ≪ Λ_UV` and providing the resurgence-theoretic
contribution beyond the perturbative gradient expansion.

DR §5 derivation: dimensional analysis on g = (ω/κ)² identifies the
Borel action's dimensional content with the substrate's UV scale.
Validated numerically in `src/resurgence/borel.py:lambda_uv_estimate`
on synthetic Heller–Spalinski-style sequences (recovers `A` exactly
via [1/1] Padé on `a_n = n!/A^n` test inputs).
-/
noncomputable def lambdaUV_from_borelAction
    (κ : ℝ) (a : ℕ → ℝ) (h : BorelActionData a) : ℝ :=
  κ * Real.sqrt h.A

/--
**The Λ_UV predictor is positive whenever the surface gravity κ is.**

Substantive content: `Λ_UV = κ · √A > 0` follows from `κ > 0` and
`√A > 0` (the latter from `A > 0` via `Real.sqrt_pos.mpr h.A_pos`).
-/
theorem lambdaUV_pos
    {κ : ℝ} (hκ : 0 < κ) (a : ℕ → ℝ) (h : BorelActionData a) :
    0 < lambdaUV_from_borelAction κ a h := by
  unfold lambdaUV_from_borelAction
  exact mul_pos hκ (Real.sqrt_pos.mpr h.A_pos)

/--
**The Λ_UV predictor is monotone in `√A`.**

Substantive content: for fixed κ > 0, larger Borel actions yield larger
predicted UV cutoffs. Useful for comparing two competing fits to the
same coefficient data (e.g., leading vs subleading Borel singularity).
-/
theorem lambdaUV_mono_in_sqrt_A
    {κ : ℝ} (hκ : 0 < κ) (a₁ a₂ : ℕ → ℝ)
    (h₁ : BorelActionData a₁) (h₂ : BorelActionData a₂)
    (hA : h₁.A ≤ h₂.A) :
    lambdaUV_from_borelAction κ a₁ h₁ ≤ lambdaUV_from_borelAction κ a₂ h₂ := by
  unfold lambdaUV_from_borelAction
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA) hκ.le

end SKEFTHawking.Resurgence
