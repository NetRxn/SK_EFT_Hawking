import SKEFTHawking.MaxwellGarnett

/-!
# Phase 6CE, Wave 2 — constituent two-sided bounds on the effective permittivity

The Maxwell–Garnett effective permittivity (`MaxwellGarnett.maxwellGarnett`) of a physical two-phase
composite (`0 < εₕ ≤ εᵢ`, fill fraction `0 ≤ f ≤ 1`) is **bracketed by its constituents**:

  `εₕ ≤ ε_eff ≤ εᵢ`   (`effectiveMedium_constituent_bounds`).

A mixture's effective response can never leave the interval spanned by the two phases. The bound is
a **certificate**: it is exact (rational, `norm_num`-checkable) for any rational composite, with no
floating-point.

## ⚠️ Naming: this is NOT the Hashin–Shtrikman bound, and NOT the Wiener bound

Corrected 2026-07-31 after a D11 Stage-13 finding. This module previously titled itself
"Hashin–Shtrikman-type" and called the result "the elementary Hashin–Shtrikman / Wiener-type
enclosure". Both names overstate it, and they overstate it by two distinct rungs:

* the **Wiener** (1912) bounds are the harmonic and arithmetic means of the phases,
  `[(1−f)/εₕ + f/εᵢ]⁻¹ ≤ ε_eff ≤ (1−f)εₕ + f εᵢ`;
* the **Hashin–Shtrikman** (1962) bounds are tighter still, being the best bounds obtainable from
  volume fraction and isotropy alone.

What is proved here is the **constituent** bracket `[εₕ, εᵢ]`, which is weaker than both. At this
module's own worked point `(εₕ, εᵢ, f) = (1, 4, 1/2)` the constituent bracket is `[1, 4]` while the
Wiener bracket is `[1.6, 2.5]` and `ε_eff = 2` — so the shipped lower bound `1` sits strictly below
the Wiener lower bound `1.6`, and this theorem does **not** entail either sharper family.

Neither the Wiener nor the Hashin–Shtrikman bound is formalized in this development. Do not cite
this module as having proved one. (The elastic sibling `EffectiveModuli.lean` genuinely does prove
the arithmetic/harmonic pair, correctly named there as the Voigt–Reuss bracket.)

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

/-- **Constituent bounds (Phase 6CE W2).** The Maxwell–Garnett effective permittivity of a physical
composite is bracketed by its two phases: `εₕ ≤ ε_eff ≤ εᵢ`.

⚠️ This is the **constituent** bracket, not the Hashin–Shtrikman bound and not the Wiener bound —
both of those are strictly tighter and neither is formalized here. See the module header. The
hypotheses are load-bearing: `ho : εh ≤ εi` is **not** a WLOG relabeling, because Maxwell–Garnett is
not symmetric under exchanging host and inclusion, so for `εᵢ < εₕ` the chain above is false and the
correct chain reverses. -/
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
