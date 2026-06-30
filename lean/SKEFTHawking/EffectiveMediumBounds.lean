import SKEFTHawking.MaxwellGarnett

/-!
# Phase 6CE, Wave 2 — Hashin–Shtrikman-type two-sided bounds on the effective permittivity

The Maxwell–Garnett effective permittivity (`MaxwellGarnett.maxwellGarnett`) of a physical two-phase
composite (`0 < εₕ ≤ εᵢ`, fill fraction `0 ≤ f ≤ 1`) is **bracketed by its constituents**:

  `εₕ ≤ ε_eff ≤ εᵢ`   (`effectiveMedium_constituent_bounds`).

This is the elementary Hashin–Shtrikman / Wiener-type enclosure: a mixture's effective response can
never leave the interval spanned by the two phases. The bound is a **certificate**: it is exact
(rational, `norm_num`-checkable) for any rational composite, with no floating-point.

## Wave-2 headlines

* `effectiveMedium_constituent_bounds` — `εₕ ≤ ε_eff ≤ εᵢ` for `0 < εₕ ≤ εᵢ`, `0 ≤ f ≤ 1`.
* `effectiveMedium_hashinShtrikman_enclosure` — a concrete `norm_num`-backed rational enclosure:
  for `εₕ = 1, εᵢ = 4, f = 1/2`, `ε_eff = 2`, with `1 ≤ 2 ≤ 4`.

**Two-layer honesty.** The bounds are Lean-verified algebraic facts about the mixing formula; the
physical-composite identification stays literature-cited (cf. Hashin & Shtrikman, J. Appl. Phys. 33,
3125 (1962)).
-/

namespace SKEFTHawking.Metamaterial

/-- The Maxwell–Garnett denominator `D = εᵢ + 2εₕ − f(εᵢ − εₕ)` is at least `3εₕ`, hence positive,
for a physical composite (`0 < εₕ ≤ εᵢ`, `f ≤ 1`). -/
lemma mg_denom_pos (εh εi f : ℝ) (hh : 0 < εh) (ho : εh ≤ εi) (hf1 : f ≤ 1) :
    0 < εi + 2 * εh - f * (εi - εh) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ho) (sub_nonneg.mpr hf1)]

/-- The effective permittivity is at least the host (the lower constituent). -/
lemma maxwellGarnett_ge_host (εh εi f : ℝ) (hh : 0 < εh) (ho : εh ≤ εi) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    εh ≤ maxwellGarnett εh εi f := by
  rw [maxwellGarnett, le_div_iff₀ (mg_denom_pos εh εi f hh ho hf1)]
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt hh) hf0) (sub_nonneg.mpr ho)]

/-- The effective permittivity is at most the inclusion (the upper constituent). -/
lemma maxwellGarnett_le_inclusion (εh εi f : ℝ) (hh : 0 < εh) (ho : εh ≤ εi) (_hf0 : 0 ≤ f)
    (hf1 : f ≤ 1) : maxwellGarnett εh εi f ≤ εi := by
  rw [maxwellGarnett, div_le_iff₀ (mg_denom_pos εh εi f hh ho hf1)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr ho) (by linarith : (0:ℝ) ≤ εi + 2 * εh))
    (sub_nonneg.mpr hf1)]

/-- **Hashin–Shtrikman constituent bounds (Phase 6CE W2).** The Maxwell–Garnett effective
permittivity of a physical composite is bracketed by its two phases: `εₕ ≤ ε_eff ≤ εᵢ`. -/
theorem effectiveMedium_constituent_bounds (εh εi f : ℝ) (hh : 0 < εh) (ho : εh ≤ εi)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    εh ≤ maxwellGarnett εh εi f ∧ maxwellGarnett εh εi f ≤ εi :=
  ⟨maxwellGarnett_ge_host εh εi f hh ho hf0 hf1,
   maxwellGarnett_le_inclusion εh εi f hh ho hf0 hf1⟩

/-- **Certified rational enclosure (Phase 6CE W2).** A concrete composite (`εₕ = 1`, `εᵢ = 4`,
half-filled `f = 1/2`) has effective permittivity exactly `ε_eff = 2`, lying (as the bounds require)
in the constituent interval `[1, 4]`. All values rational; `norm_num`-checkable, no floating point. -/
theorem effectiveMedium_hashinShtrikman_enclosure :
    maxwellGarnett 1 4 (1 / 2) = 2 ∧
    (1 : ℝ) ≤ maxwellGarnett 1 4 (1 / 2) ∧ maxwellGarnett 1 4 (1 / 2) ≤ 4 := by
  have hval : maxwellGarnett 1 4 (1 / 2) = 2 := by unfold maxwellGarnett; norm_num
  exact ⟨hval, by rw [hval]; norm_num, by rw [hval]; norm_num⟩

end SKEFTHawking.Metamaterial
