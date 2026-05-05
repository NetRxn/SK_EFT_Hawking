/-
Phase 6n.α Wave (G2 Resurgence) — Stage 1 Lean substrate.

Borel transform on coefficient sequences and the Gevrey-1
asymptotic-growth predicate. Substrate for `BorelAction.lean`
(Λ_UV-from-IR theorem) and `StokesBound.lean` (FDR-mandated lower
bound on the Stokes constant).

The Python-side numerical infrastructure for this module lives at
`src/resurgence/borel.py` (Padé–Borel pipeline, ratio-test diagnostic,
Λ_UV closed-form predictor; 17 tests in `tests/test_resurgence.py`).

References:
- Aniceto–Başar–Schiappa, Phys. Rep. 809 (2019) 1, arXiv:1802.10441
- Sauzin, Introduction to 1-Summability and Resurgence, arXiv:1405.0356
- Heller–Spalinski, PRL 115 (2015) 072501, arXiv:1503.07514
- Lit-Search/_Exploratory/Resurgence Theory and Schwinger–Keldysh EFT.md
  §4 (Borel–Écalle theory) + §7 (Mathlib4 gap analysis)
- temporary/working-docs/phase6n/6n_alpha_resurgence_stage1.md
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SKEFTHawking.Resurgence

/--
**The Borel transform of a coefficient sequence.**

`B[a]_n := a_n / n!` — the elementary Borel transform sufficient for
the SK-EFT gradient-expansion application. The full
`FormalMultilinearSeries`-valued lift is a downstream Mathlib-PR-class
deliverable (DR §7); this elementary form is the substrate predicate
for the SK-EFT Λ_UV-from-IR result.

DR §4: For a Gevrey-1 series `a_n ~ n!/A^n`, the Borel transform has
finite radius of convergence equal to `A` (the "Borel action"). The
analytic continuation past that disk encodes the non-perturbative
content (alien-derivative structure).
-/
noncomputable def borelTransform (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n => a n / n.factorial

/--
**A coefficient sequence is `IsGevrey1 a A`** if `|a n| ≤ n!/A^n`
for all `n` and `A > 0`.

DR §4 (Aniceto–Başar–Schiappa): Gevrey-1 is the asymptotic-growth class
for which the Borel transform converges in a disk of radius `A`. The
program's conjecture for the SK-EFT gradient expansion (per Heller–
Spalinski 2015 and the Aniceto–Başar–Schiappa physics canon) is that
the coefficient sequence is Gevrey-1 with a finite positive Borel
action, encoding the substrate's UV cutoff via Λ_UV = κ √A.
-/
def IsGevrey1 (a : ℕ → ℝ) (A : ℝ) : Prop :=
  0 < A ∧ ∀ n : ℕ, |a n| ≤ n.factorial / A ^ n

/-- Extracts the positivity of `A` from `IsGevrey1`. -/
theorem IsGevrey1.A_pos {a : ℕ → ℝ} {A : ℝ} (h : IsGevrey1 a A) : 0 < A :=
  h.1

/-- Extracts the per-`n` factorial bound from `IsGevrey1`. -/
theorem IsGevrey1.bound {a : ℕ → ℝ} {A : ℝ} (h : IsGevrey1 a A) (n : ℕ) :
    |a n| ≤ n.factorial / A ^ n :=
  h.2 n

/--
**The Borel transform of a Gevrey-1 sequence is bounded by `1/A^n`.**

Substantive convergence statement: dividing both sides of the
factorial bound `|a n| ≤ n!/A^n` by `n! > 0` yields
`|borelTransform a n| = |a n|/n! ≤ 1/A^n`. The Borel-plane series
`Σ B[a]_n · ζ^n` therefore has radius of convergence at least `A`,
matching the Aniceto–Başar–Schiappa Gevrey-1-implies-Borel-disk lemma.
-/
theorem borelTransform_bounded_of_isGevrey1
    {a : ℕ → ℝ} {A : ℝ} (h : IsGevrey1 a A) :
    ∀ n : ℕ, |borelTransform a n| ≤ 1 / A ^ n := by
  intro n
  have hn_pos : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hAn_pos : (0 : ℝ) < A ^ n := pow_pos h.A_pos n
  have hbound : |a n| ≤ n.factorial / A ^ n := h.bound n
  -- |borelTransform a n| = |a n / n!| = |a n| / n!  (since n! > 0)
  calc |borelTransform a n|
      = |a n| / n.factorial := by
        unfold borelTransform; rw [abs_div, abs_of_pos hn_pos]
    _ ≤ (n.factorial / A ^ n) / n.factorial := by
        exact div_le_div_of_nonneg_right hbound hn_pos.le
    _ = 1 / A ^ n := by field_simp

end SKEFTHawking.Resurgence
