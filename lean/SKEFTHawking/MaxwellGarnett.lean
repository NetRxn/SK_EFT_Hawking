import Mathlib

/-!
# Phase 6CE, Wave 1 — The Maxwell–Garnett effective permittivity

The quasi-static **Maxwell–Garnett** mixing formula for a two-phase composite: spherical inclusions of
permittivity `εᵢ` at volume fraction `f` embedded in a host of permittivity `εₕ`. The effective
permittivity is

  `ε_eff = εₕ · (εᵢ + 2εₕ + 2f(εᵢ − εₕ)) / (εᵢ + 2εₕ − f(εᵢ − εₕ))`   (`maxwellGarnett`).

This is the unique solution of the **Clausius–Mossotti** implicit relation

  `(ε_eff − εₕ)/(ε_eff + 2εₕ) = f · (εᵢ − εₕ)/(εᵢ + 2εₕ)`.

## Wave-1 headlines

* `maxwellGarnett_clausius_mossotti` — the closed form satisfies the Clausius–Mossotti relation
  (cross-multiplied, division-free): `(ε_eff − εₕ)(εᵢ + 2εₕ) = f(εᵢ − εₕ)(ε_eff + 2εₕ)`.
* `maxwellGarnett_host_recovery` — the `f → 0` (no-inclusion) limit recovers the host: `ε_eff = εₕ`.

## Guardrail — algebraic path only

Per the roadmap, this is the **algebraic** quasi-static derivation: finite-field arithmetic only. Full
two-scale / periodic-homogenization convergence is a documented substrate stall (Mathlib has no
two-scale convergence; PhysLib `Optics` is an explicit placeholder) and is **out of scope**.

**Two-layer honesty.** The mixing formula and its Clausius–Mossotti characterisation are Lean-verified;
the physical-composite identification (dilute limit, spherical inclusion geometry) stays
literature-cited (cf. Maxwell Garnett, Phil. Trans. R. Soc. 203, 385 (1904); Choy, *Effective Medium
Theory*).
-/

namespace SKEFTHawking.Metamaterial

/-- The Maxwell–Garnett effective permittivity `ε_eff(εₕ, εᵢ, f)` of a two-phase composite (host `εₕ`,
spherical inclusions `εᵢ` at volume fraction `f`). -/
noncomputable def maxwellGarnett (εh εi f : ℝ) : ℝ :=
  εh * (εi + 2 * εh + 2 * f * (εi - εh)) / (εi + 2 * εh - f * (εi - εh))

/-- **Clausius–Mossotti relation (Phase 6CE W1).** The Maxwell–Garnett effective permittivity solves
the defining implicit relation, in cross-multiplied (division-free) form. This is the substantive
characterisation: the closed form is *the* root of the Clausius–Mossotti equation. -/
theorem maxwellGarnett_clausius_mossotti (εh εi f : ℝ)
    (hD : εi + 2 * εh - f * (εi - εh) ≠ 0) :
    (maxwellGarnett εh εi f - εh) * (εi + 2 * εh)
      = f * (εi - εh) * (maxwellGarnett εh εi f + 2 * εh) := by
  have hkey : maxwellGarnett εh εi f * (εi + 2 * εh - f * (εi - εh))
      = εh * (εi + 2 * εh + 2 * f * (εi - εh)) := by
    rw [maxwellGarnett, div_mul_cancel₀ _ hD]
  linear_combination hkey

/-- **Host recovery (Phase 6CE W1).** At zero inclusion fraction the effective medium is the bare
host: `ε_eff(εₕ, εᵢ, 0) = εₕ`. -/
theorem maxwellGarnett_host_recovery (εh εi : ℝ) (h : εi + 2 * εh ≠ 0) :
    maxwellGarnett εh εi 0 = εh := by
  unfold maxwellGarnett
  simp only [mul_zero, zero_mul, sub_zero, add_zero]
  rw [mul_div_assoc, div_self h, mul_one]

end SKEFTHawking.Metamaterial
