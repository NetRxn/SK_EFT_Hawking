import SKEFTHawking.AcousticBlochOperator

/-!
# Phase 6CB, Wave 2 — A certified phononic band gap

A concrete diatomic crystal — masses `m₁ = 1` (light), `m₂ = 2` (heavy), spring constant `κ = 1`,
lattice constant `a = 1` — whose acoustic and optical squared-frequency branches (from
`AcousticBlochOperator`) are

  `ω²±(k) = 3/2 ± √(5/4 + cos k)`.

Across the whole Brillouin zone the **acoustic** branch never exceeds `1` (its maximum, at the zone
edge `k = π`) and the **optical** branch never drops below `2` (its minimum, also at `k = π`). Hence
the open interval `(1, 2)` contains **no Bloch eigenfrequency** — a proven phononic band gap.

## Wave-2 headlines

* `phononic_band_gap_exists` — `∃ lo < hi`, `lo = 1`, `hi = 2`, with `ω²₋(k) ≤ lo` and `hi ≤ ω²₊(k)`
  for *every* `k`: the two squared-frequency branches straddle the gap.
* `band_gap_falsifier` — no eigenmode lies strictly inside the gap: if `ω²` is one of the two
  Bloch eigenvalues at any `k` (each annihilating the secular determinant, `AcousticBlochOperator`)
  and `1 < ω² < 2`, that is a contradiction.

The `1` and `2` are `norm_num`-backed exact rational gap edges (no floating point); Wave 3 turns
them into a two-sided interval enclosure.

**Two-layer honesty.** The gap *theorem* for this rational crystal is Lean-verified. Whether a given
physical material realises exactly these mass/spring ratios stays literature-cited (cf. Kittel ch. 4).
-/

namespace SKEFTHawking.Phononic

open Matrix

/-- The concrete diatomic crystal: light/heavy masses `1, 2`, spring constant `1`, lattice `1`. -/
noncomputable def diatomicCrystal : DiatomicChain :=
  ⟨1, 2, 1, 1, one_pos, two_pos, one_pos, one_pos⟩

namespace diatomicCrystal

/-- The crystal's diagonal-splitting parameter `gap = κ(1/m₁ − 1/m₂) = 1/2`. -/
lemma gap_eq : diatomicCrystal.gap = 1 / 2 := by
  simp [DiatomicChain.gap, diatomicCrystal]; norm_num

/-- The crystal's band centre `mid = κ(1/m₁ + 1/m₂) = 3/2`. -/
lemma mid_eq : diatomicCrystal.mid = 3 / 2 := by
  simp [DiatomicChain.mid, diatomicCrystal]; norm_num

/-- The discriminant is at least `1/4 = gap²` (the optical–acoustic splitting never collapses). -/
lemma disc_ge_quarter (k : ℝ) : 1 / 4 ≤ diatomicCrystal.disc k := by
  have h2 : 0 ≤ diatomicCrystal.normSqOff k := diatomicCrystal.normSqOff_nonneg k
  unfold DiatomicChain.disc
  rw [gap_eq]
  nlinarith [h2]

/-- Consequently `√disc ≥ 1/2` — the half-splitting that separates the two branches. -/
lemma sqrt_disc_ge_half (k : ℝ) : (1 : ℝ) / 2 ≤ Real.sqrt (diatomicCrystal.disc k) := by
  have h : (1 : ℝ) / 2 = Real.sqrt (1 / 4) := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]
  exact Real.sqrt_le_sqrt (disc_ge_quarter k)

/-- **Acoustic branch capped at the gap bottom:** `ω²₋(k) ≤ 1` for every `k`. -/
lemma acoustic_le_one (k : ℝ) : diatomicCrystal.branchMinus k ≤ 1 := by
  unfold DiatomicChain.branchMinus
  rw [mid_eq]
  linarith [sqrt_disc_ge_half k]

/-- **Optical branch above the gap top:** `2 ≤ ω²₊(k)` for every `k`. -/
lemma optical_ge_two (k : ℝ) : 2 ≤ diatomicCrystal.branchPlus k := by
  unfold DiatomicChain.branchPlus
  rw [mid_eq]
  linarith [sqrt_disc_ge_half k]

/-- At the Brillouin-zone edge `k = π` the discriminant bottoms out at `1/4` (`cos π = −1`,
`normSqOff = 0`): the two branches are closest there. -/
lemma disc_at_pi : diatomicCrystal.disc Real.pi = 1 / 4 := by
  unfold DiatomicChain.disc DiatomicChain.normSqOff
  rw [gap_eq]
  simp only [diatomicCrystal, mul_one, Real.cos_pi]
  norm_num

/-- **The gap bottom is attained:** the acoustic branch reaches exactly `1` at `k = π`. So the
`≤ 1` bound of `acoustic_le_one` is tight (not a loose over-estimate). -/
lemma branchMinus_at_pi : diatomicCrystal.branchMinus Real.pi = 1 := by
  unfold DiatomicChain.branchMinus
  rw [mid_eq, disc_at_pi, show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **The gap top is attained:** the optical branch reaches exactly `2` at `k = π`. So the `2 ≤`
bound of `optical_ge_two` is tight. -/
lemma branchPlus_at_pi : diatomicCrystal.branchPlus Real.pi = 2 := by
  unfold DiatomicChain.branchPlus
  rw [mid_eq, disc_at_pi, show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **The gap bottom is attained at the other zone edge too.** By evenness of the branches
(`DiatomicChain.branchMinus_neg`), the acoustic branch also reaches exactly `1` at `k = -π`.

Added 2026-07-31 (D11 Stage-13 round-7 finding 5.6). Fig. 1 marks both `+π` and `-π` as certified
gap-edge points and the caption appealed to evenness in `k`; only the `+π` endpoint had a theorem. -/
lemma branchMinus_at_neg_pi : diatomicCrystal.branchMinus (-Real.pi) = 1 := by
  rw [DiatomicChain.branchMinus_neg]
  exact branchMinus_at_pi

/-- **The gap top is attained at the other zone edge too** — the optical counterpart of
`branchMinus_at_neg_pi`. -/
lemma branchPlus_at_neg_pi : diatomicCrystal.branchPlus (-Real.pi) = 2 := by
  rw [DiatomicChain.branchPlus_neg]
  exact branchPlus_at_pi

end diatomicCrystal

/-- **Phononic band gap (Phase 6CB W2).** There is a non-empty squared-frequency interval
`(1, 2)` straddled by the two branches: for every crystal momentum `k`, the acoustic branch lies at
or below `1` and the optical branch at or above `2`. -/
theorem phononic_band_gap_exists :
    ∃ lo hi : ℝ, lo < hi ∧
      ∀ k : ℝ, diatomicCrystal.branchMinus k ≤ lo ∧ hi ≤ diatomicCrystal.branchPlus k :=
  ⟨1, 2, by norm_num, fun k => ⟨diatomicCrystal.acoustic_le_one k, diatomicCrystal.optical_ge_two k⟩⟩

/-- **Gap falsifier (Phase 6CB W2).** No Bloch eigenmode lies strictly inside the gap `(1, 2)` — for
*any* eigenvalue, not just a named branch. If a real squared frequency `ω²` annihilates the secular
determinant `det(D(k) − ω²·I) = 0` (i.e. `ω²` is a genuine eigenvalue of the Bloch operator at some
`k`) then `ω²` cannot satisfy `1 < ω² < 2`. Uses spectral completeness
(`acousticBloch_eigenvalue_iff`): every eigenvalue is one of the two branches. -/
theorem band_gap_falsifier (k : ℝ) {ω : ℝ}
    (heig : (diatomicCrystal.blochMatrix k - (ω : ℂ) • 1).det = 0)
    (hmode : 1 < ω ∧ ω < 2) : False := by
  rw [diatomicCrystal.acousticBloch_eigenvalue_iff] at heig
  rcases heig with h | h
  · have := diatomicCrystal.acoustic_le_one k
    rw [← h] at this; linarith [hmode.1]
  · have := diatomicCrystal.optical_ge_two k
    rw [← h] at this; linarith [hmode.2]

end SKEFTHawking.Phononic
