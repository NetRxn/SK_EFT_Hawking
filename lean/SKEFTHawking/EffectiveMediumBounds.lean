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
this module as having proved one. (The elastic sibling `EffectiveModuli.lean` proves the
ordering of the arithmetic and harmonic averages plus constituent bounds — it likewise does NOT
prove the classical Voigt–Reuss bracket on a physical effective modulus. Corrected 2026-07-31: an
earlier version of this sentence said it was "correctly named there as the Voigt–Reuss bracket",
which was the same misnomer one file away.)

## Wave-2 headlines

* `effectiveMedium_constituent_bounds` — `εₕ ≤ ε_eff ≤ εᵢ` for `0 < εₕ ≤ εᵢ`, `0 ≤ f ≤ 1`.
* `effectiveMedium_constituent_bounds_strict` — `εₕ < ε_eff < εᵢ` for `εₕ < εᵢ`, `0 < f < 1`; the
  general statement that the non-strict bracket is attained only at the degenerate endpoints.
* `effectiveMedium_hashinShtrikman_enclosure` — a concrete `norm_num`-backed rational value:
  for `εₕ = 1, εᵢ = 4, f = 1/2`, `ε_eff = 2`; `effectiveMedium_worked_point_strict` instantiates the
  strict bracket there.

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

/-! ### Strict interiority — the general statement

The non-strict pair above is attained at the endpoints (`f = 0` gives `ε_eff = εh`, `f = 1` gives
`ε_eff = εi`, and `εh = εi` collapses everything). Away from those degeneracies it is *strict*, which
is genuinely more than `effectiveMedium_constituent_bounds` gives and is not derivable from any
single evaluated instance.

Added 2026-07-31, D11 Stage-13 round-7 finding 3.2 (raised in round 3, and a first remediation
attempt in round 6 did NOT fix it). The concrete witness below used to bundle
`maxwellGarnett 1 4 (1/2) = 2` with two order facts about the same number, which `norm_num` derives
from the value — the project's own P2 bundle-redundancy anti-pattern. Round 6 changed those conjuncts
from `≤` to `<`, which is not entailed by `effectiveMedium_constituent_bounds` but *is* still entailed
by the value, so the redundancy survived. The fix is to put the non-derivable content in a general
theorem and let the concrete point be an instance of it. -/

lemma maxwellGarnett_gt_host (εh εi f : ℝ) (hh : 0 < εh) (ho : εh < εi) (hf0 : 0 < f)
    (hf1 : f ≤ 1) : εh < maxwellGarnett εh εi f := by
  rw [maxwellGarnett, lt_div_iff₀ (mg_denom_pos εh εi f hh (le_of_lt ho) hf1)]
  nlinarith [mul_pos (mul_pos hh hf0) (sub_pos.mpr ho)]

lemma maxwellGarnett_lt_inclusion (εh εi f : ℝ) (hh : 0 < εh) (ho : εh < εi) (_hf0 : 0 ≤ f)
    (hf1 : f < 1) : maxwellGarnett εh εi f < εi := by
  rw [maxwellGarnett, div_lt_iff₀ (mg_denom_pos εh εi f hh (le_of_lt ho) (le_of_lt hf1))]
  nlinarith [mul_pos (sub_pos.mpr ho) (sub_pos.mpr hf1), sq_nonneg (εi - εh)]

/-- **Strict constituent enclosure.** For a genuinely two-phase composite (`εh < εi`) at a genuinely
mixed fill fraction (`0 < f < 1`), the Maxwell–Garnett effective permittivity lies **strictly**
between the constituents. Neither bound of `effectiveMedium_constituent_bounds` is attained. -/
theorem effectiveMedium_constituent_bounds_strict (εh εi f : ℝ) (hh : 0 < εh) (ho : εh < εi)
    (hf0 : 0 < f) (hf1 : f < 1) :
    εh < maxwellGarnett εh εi f ∧ maxwellGarnett εh εi f < εi :=
  ⟨maxwellGarnett_gt_host εh εi f hh ho hf0 (le_of_lt hf1),
   maxwellGarnett_lt_inclusion εh εi f hh ho (le_of_lt hf0) hf1⟩

/-- **Certified rational enclosure (Phase 6CE W2).** A concrete composite (`εₕ = 1`, `εᵢ = 4`,
half-filled `f = 1/2`) has effective permittivity exactly `ε_eff = 2`. All values rational;
`norm_num`-checkable, no floating point.

Reduced to the value alone on 2026-07-31 (D11 Stage-13 round-7 finding 3.2, first raised in round 3).
Two earlier versions bundled order facts alongside the value: originally `1 ≤ ε_eff ≤ 4`, then
`1 < ε_eff < 4`. Neither is an instance of `effectiveMedium_constituent_bounds`, but **both are
derivable from the value by `norm_num`** — which is what made them redundant, so the round-6 attempt
fixed the wrong entailment. The non-derivable content is the *general* strict statement, which now
lives in `effectiveMedium_constituent_bounds_strict`; the interiority of this point is an instance of
it (`effectiveMedium_worked_point_strict`) rather than a restatement of `= 2`. -/
theorem effectiveMedium_hashinShtrikman_enclosure :
    maxwellGarnett 1 4 (1 / 2) = 2 := by
  unfold maxwellGarnett; norm_num

/-- The worked point lies **strictly** inside `[1, 4]` — obtained by *instantiating*
`effectiveMedium_constituent_bounds_strict`, not by re-deriving order facts from the value. The
proof term is itself the evidence that the general theorem is what carries this claim. -/
theorem effectiveMedium_worked_point_strict :
    (1:ℝ) < maxwellGarnett 1 4 (1 / 2) ∧ maxwellGarnett 1 4 (1 / 2) < 4 :=
  effectiveMedium_constituent_bounds_strict 1 4 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end SKEFTHawking.Metamaterial
