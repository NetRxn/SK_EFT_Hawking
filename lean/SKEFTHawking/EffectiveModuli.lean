import SKEFTHawking.EffectiveMediumBounds

/-!
# Phase 6CE, Wave 3 — Elastic effective moduli (constituent bounds on the Voigt/Reuss averages)

The mechanical analog of the Wave-2 electromagnetic enclosure. For a two-phase elastic composite
(constituent moduli `0 < M₁ ≤ M₂` — bulk or shear — at volume fraction `f`), the two classical
algebraic mixing rules are the **Voigt** (arithmetic, iso-strain) and **Reuss** (harmonic, iso-stress)
averages:

  `M_Voigt = (1−f)M₁ + f M₂`,   `M_Reuss = M₁M₂ / ((1−f)M₂ + f M₁)`.

What is proved here is an **ordering of the two averages**, together with constituent bounds:

  `M₁ ≤ M_Reuss ≤ M_Voigt ≤ M₂`   (`effectiveModuli_enclosure`).

⚠️ **This is NOT the Voigt–Reuss–Hill theorem** (scope corrected 2026-07-31, D11 Stage-13). The VRH
statement brackets a *physical* effective modulus, `M_Reuss ≤ M_eff ≤ M_Voigt`. No effective modulus
of a composite appears anywhere in `effectiveModuli_enclosure`'s statement — only the two closed-form
averages and the constituents. The distinction is exactly the one `EffectiveMediumBounds.lean` draws
between its constituent bracket and the Hashin–Shtrikman bounds, and for the same reason: to name
a result after a family it does not touch is the defect that file's header now warns about.
(Note the reflow: a docstring line that *begins* with the word "theorem" is counted as a
declaration by this project's stated source-level counting rule, and briefly inflated D11's
published theorem count by one.)
`voigtModulus` and `reussModulus` genuinely *are* the Voigt and Reuss averages; it is the *bracket*
that is not formalized.

The Reuss ≤ Voigt gap is exactly `f(1−f)(M₁−M₂)²/((1−f)M₂+fM₁) ≥ 0` (an AM–HM inequality).

## Wave-3 headline

* `effectiveModuli_enclosure` — the full `M₁ ≤ M_Reuss ≤ M_Voigt ≤ M₂` chain for `0 < M₁ ≤ M₂`,
  `0 ≤ f ≤ 1`. Purely algebraic (the elastic analog of the Maxwell–Garnett enclosure); no
  floating-point.

**Two-layer honesty.** The mixing rules and bounds are Lean-verified algebra; the identification with a
physical bulk/shear modulus of a real composite stays literature-cited (cf. Hill, Proc. Phys. Soc. A 65,
349 (1952)).
-/

namespace SKEFTHawking.Metamaterial

/-- The Voigt (arithmetic, iso-strain) effective modulus `(1−f)M₁ + f M₂`. -/
noncomputable def voigtModulus (M1 M2 f : ℝ) : ℝ := (1 - f) * M1 + f * M2

/-- The Reuss (harmonic, iso-stress) effective modulus `M₁M₂ / ((1−f)M₂ + f M₁)`. -/
noncomputable def reussModulus (M1 M2 f : ℝ) : ℝ := M1 * M2 / ((1 - f) * M2 + f * M1)

/-- The Reuss denominator `(1−f)M₂ + f M₁` is positive for a physical composite. -/
lemma reuss_denom_pos (M1 M2 f : ℝ) (h1 : 0 < M1) (h2 : 0 < M2) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    0 < (1 - f) * M2 + f * M1 := by
  have : 0 ≤ 1 - f := by linarith
  nlinarith [mul_nonneg this (le_of_lt h2), mul_nonneg hf0 (le_of_lt h1)]

/-- The Voigt average is bracketed by the constituents: `M₁ ≤ M_Voigt ≤ M₂`. -/
lemma voigt_bounds (M1 M2 f : ℝ) (ho : M1 ≤ M2) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    M1 ≤ voigtModulus M1 M2 f ∧ voigtModulus M1 M2 f ≤ M2 := by
  unfold voigtModulus
  constructor
  · nlinarith [mul_nonneg hf0 (sub_nonneg.mpr ho)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - f) (sub_nonneg.mpr ho)]

/-- **Reuss ≤ Voigt** (the AM–HM inequality): the harmonic average never exceeds the arithmetic one. -/
lemma reuss_le_voigt (M1 M2 f : ℝ) (h1 : 0 < M1) (h2 : 0 < M2) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    reussModulus M1 M2 f ≤ voigtModulus M1 M2 f := by
  rw [reussModulus, div_le_iff₀ (reuss_denom_pos M1 M2 f h1 h2 hf0 hf1)]
  unfold voigtModulus
  nlinarith [mul_nonneg (mul_nonneg hf0 (by linarith : (0:ℝ) ≤ 1 - f)) (sq_nonneg (M1 - M2))]

/-- **The exact AM–HM gap:** `M_Voigt − M_Reuss = f(1−f)(M₁−M₂)² / ((1−f)M₂ + f M₁)`. This is the
identity underlying `reuss_le_voigt` (the right side is manifestly `≥ 0`). -/
lemma voigt_sub_reuss_eq (M1 M2 f : ℝ) (h1 : 0 < M1) (h2 : 0 < M2) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    voigtModulus M1 M2 f - reussModulus M1 M2 f
      = f * (1 - f) * (M1 - M2) ^ 2 / ((1 - f) * M2 + f * M1) := by
  rw [voigtModulus, reussModulus]
  field_simp [ne_of_gt (reuss_denom_pos M1 M2 f h1 h2 hf0 hf1)]
  ring

/-- The Reuss average is at least the lower constituent `M₁`. -/
lemma reuss_ge_host (M1 M2 f : ℝ) (h1 : 0 < M1) (h2 : 0 < M2) (ho : M1 ≤ M2) (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1) : M1 ≤ reussModulus M1 M2 f := by
  rw [reussModulus, le_div_iff₀ (reuss_denom_pos M1 M2 f h1 h2 hf0 hf1)]
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt h1) hf0) (sub_nonneg.mpr ho)]

/-- **Constituent bounds on the Voigt/Reuss averages (Phase 6CE W3).** For `0 < M₁ ≤ M₂`,
`0 ≤ f ≤ 1`, the two averages are ordered and both lie between the constituents:
`M₁ ≤ M_Reuss ≤ M_Voigt ≤ M₂`. The elastic analog of the Maxwell–Garnett constituent enclosure.

⚠️ **This is NOT the Voigt–Reuss–Hill theorem** (scope corrected 2026-07-31, D11 Stage-13 round 4;
the module header was corrected in round 3 and this docstring — the one a consumer actually reads —
was missed). VRH brackets a *physical* effective modulus, `M_Reuss ≤ M_eff ≤ M_Voigt`. **No
effective modulus of a composite appears anywhere in this statement**: `voigtModulus` and
`reussModulus` are the two closed-form averages, and what is proved is their ordering plus the
constituent bounds. `voigtModulus`/`reussModulus` genuinely *are* the Voigt and Reuss averages; it
is the *bracket on M_eff* that is not formalized here. -/
theorem effectiveModuli_enclosure (M1 M2 f : ℝ) (h1 : 0 < M1) (h2 : 0 < M2) (ho : M1 ≤ M2)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    M1 ≤ reussModulus M1 M2 f ∧
    reussModulus M1 M2 f ≤ voigtModulus M1 M2 f ∧
    voigtModulus M1 M2 f ≤ M2 :=
  ⟨reuss_ge_host M1 M2 f h1 h2 ho hf0 hf1,
   reuss_le_voigt M1 M2 f h1 h2 hf0 hf1,
   (voigt_bounds M1 M2 f ho hf0 hf1).2⟩

end SKEFTHawking.Metamaterial
