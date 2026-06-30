import SKEFTHawking.PhononicBandGap

/-!
# Phase 6CB, Wave 3 — A certified rational (floating-point-free) band-gap enclosure

Wave 2 proved the *squared-frequency* gap `(1, 2)` with exact rational edges. The physical **angular
frequency** `ω = √(ω²)` turns the optical edge into the irrational `√2`. This module certifies a
two-sided **rational** bracket for that edge and packages a rational frequency-gap interval that
provably contains no Bloch eigenmode — a certificate usable with no floating-point arithmetic.

## Wave-3 headline (`band_gap_rational_enclosure`)

`1 < 141/100`, and for every crystal momentum `k` the acoustic eigenfrequency `√(ω²₋(k)) ≤ 1` while
the optical eigenfrequency `√(ω²₊(k)) ≥ 141/100`. Hence the rational frequency interval
`(1, 141/100)` — a strict inner approximation of the true gap `(1, √2)` — contains no eigenmode.
Every bound is `norm_num`-backed; no floating-point appears.

**Two-layer honesty.** The enclosure is a verified mathematical bound on this rational crystal's
spectrum; mapping `√2` to a measured device frequency stays literature-cited.
-/

namespace SKEFTHawking.Phononic

open Matrix

/-- The optical band-edge frequency `√2` lies in the rational bracket `[141/100, 142/100]`
(`1.41 ≤ √2 ≤ 1.42`). A `norm_num`-backed, floating-point-free enclosure. -/
lemma sqrt_two_enclosure : (141 : ℝ) / 100 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (142 : ℝ) / 100 := by
  constructor
  · rw [show (141 : ℝ) / 100 = Real.sqrt ((141 / 100) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [show (142 : ℝ) / 100 = Real.sqrt ((142 / 100) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)

namespace diatomicCrystal

/-- The acoustic eigenfrequency never exceeds `1` (the lower gap edge in `ω`). -/
lemma acoustic_freq_le_one (k : ℝ) : Real.sqrt (diatomicCrystal.branchMinus k) ≤ 1 := by
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (diatomicCrystal.acoustic_le_one k)

/-- The optical eigenfrequency is at least the rational floor `141/100` (`< √2`). -/
lemma optical_freq_ge (k : ℝ) : (141 : ℝ) / 100 ≤ Real.sqrt (diatomicCrystal.branchPlus k) :=
  le_trans sqrt_two_enclosure.1 (Real.sqrt_le_sqrt (diatomicCrystal.optical_ge_two k))

end diatomicCrystal

/-- **Certified rational band-gap enclosure (Phase 6CB W3).** The rational frequency interval
`(1, 141/100)` (a strict inner bracket of the true gap `(1, √2)`) contains no Bloch eigenmode: for
every `k`, the acoustic eigenfrequency `√(ω²₋(k)) ≤ 1` and the optical eigenfrequency
`√(ω²₊(k)) ≥ 141/100`, with `1 < 141/100`. All bounds are `norm_num`-backed (no floating point). -/
theorem band_gap_rational_enclosure :
    (1 : ℝ) < 141 / 100 ∧
      ∀ k : ℝ, Real.sqrt (diatomicCrystal.branchMinus k) ≤ 1 ∧
        (141 : ℝ) / 100 ≤ Real.sqrt (diatomicCrystal.branchPlus k) :=
  ⟨by norm_num, fun k => ⟨diatomicCrystal.acoustic_freq_le_one k, diatomicCrystal.optical_freq_ge k⟩⟩

end SKEFTHawking.Phononic
