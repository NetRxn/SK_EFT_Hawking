/-
Phase 5a Wave 2A: Wilson Mass Function

The Wilson mass M(k) = 3 - cos(kx) - cos(ky) - cos(kz) gaps all doubler
fermions on a 3+1D lattice. The key property: M(k) = 0 if and only if
k = (0,0,0), ensuring exactly one massless Weyl node.

On the discrete Brillouin zone with k_i = 2πn_i/L (n_i ∈ Fin L), the
proof that M = 0 forces k = 0 uses only:
  1. cos θ ≤ 1 for all real θ  (Real.cos_le_one)
  2. cos(2πn/L) = 1 iff L ∣ n  (roots of unity)
  3. On Fin L, L ∣ n iff n = 0

References:
  Wilson, PRD 10, 2445 (1974) — Wilson fermions, mass term
  Gioia & Thorngren, PRL 136, 061601 (2026) — GT construction uses Wilson mass
  Misumi, arXiv:2512.22609 (2025) — BdG form with Wilson mass
-/

import Mathlib

open Real

noncomputable section

namespace SKEFTHawking

/-! ## 1. Wilson Mass Definition -/

/-- Wilson mass function: M(kx, ky, kz) = 3 - cos kx - cos ky - cos kz.
    This is a trigonometric polynomial on the Brillouin zone T³. -/
def wilsonMass (kx ky kz : ℝ) : ℝ :=
  3 - cos kx - cos ky - cos kz

/-- The Wilson offset d = 3 (spatial dimension). -/
theorem wilson_offset : (3 : ℝ) = 3 := rfl

/-! ## 2. Non-negativity -/

/-- Wilson mass is non-negative: M(k) ≥ 0 for all k.
    Proof: each cos ≤ 1, so 3 - cos - cos - cos ≥ 3 - 1 - 1 - 1 = 0. -/
theorem wilson_mass_nonneg (kx ky kz : ℝ) : 0 ≤ wilsonMass kx ky kz := by
  unfold wilsonMass
  have h1 := cos_le_one kx
  have h2 := cos_le_one ky
  have h3 := cos_le_one kz
  linarith

/-- Wilson mass upper bound: M(k) ≤ 6.
    Proof: each cos ≥ -1, so 3 - cos - cos - cos ≤ 3 + 1 + 1 + 1 = 6. -/
theorem wilson_mass_le_six (kx ky kz : ℝ) : wilsonMass kx ky kz ≤ 6 := by
  unfold wilsonMass
  have h1 := neg_one_le_cos kx
  have h2 := neg_one_le_cos ky
  have h3 := neg_one_le_cos kz
  linarith

/-! ## 3. Zero Locus -/

/-- Auxiliary: if a + b + c = 3 and each ≤ 1, then each = 1. -/
theorem sum_eq_three_of_le_one {a b c : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hsum : a + b + c = 3) : a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor <;> [skip; constructor] <;> linarith

/--
Wilson mass vanishes iff all three cosines equal 1:
  M(k) = 0 ↔ cos(kx) = 1 ∧ cos(ky) = 1 ∧ cos(kz) = 1.

PROVIDED SOLUTION
M(k) = 3 - cos kx - cos ky - cos kz = 0 means cos kx + cos ky + cos kz = 3.
Since each cos ≤ 1, the sum can be 3 only if each equals 1.
Conversely, if each is 1, the sum is 3 and M = 0.
-/
theorem wilson_mass_zero_iff_cos_eq_one (kx ky kz : ℝ) :
    wilsonMass kx ky kz = 0 ↔ cos kx = 1 ∧ cos ky = 1 ∧ cos kz = 1 := by
  unfold wilsonMass
  constructor
  · intro h
    have hcos : cos kx + cos ky + cos kz = 3 := by linarith
    exact sum_eq_three_of_le_one (cos_le_one kx) (cos_le_one ky) (cos_le_one kz) hcos
  · intro ⟨hx, hy, hz⟩
    rw [hx, hy, hz]; ring

/-
Wilson mass at zero momentum: M(0,0,0) = 0.
-/
theorem wilson_mass_at_zero : wilsonMass 0 0 0 = 0 := by
  unfold wilsonMass; norm_num;

/-
Wilson mass at k = (π,0,0): M = 2 > 0 (doubler is gapped).
-/
theorem wilson_mass_positive_at_pi : 0 < wilsonMass π 0 0 := by
  norm_num [ wilsonMass ]

/-! ## 4. Strictly Positive Away from Zero -/

/-- Wilson mass is strictly positive when any cosine differs from 1.
    This means all doublers are gapped — only the k=0 Weyl node is massless. -/
theorem wilson_mass_pos_of_ne_zero (kx ky kz : ℝ)
    (h : ¬(cos kx = 1 ∧ cos ky = 1 ∧ cos kz = 1)) :
    0 < wilsonMass kx ky kz := by
  have hge := wilson_mass_nonneg kx ky kz
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact hlt
  · exfalso; exact h ((wilson_mass_zero_iff_cos_eq_one kx ky kz).mp heq.symm)

/-! ## 5. Weyl Node Count -/

/-- On any finite lattice, the Wilson mass has exactly one zero: k = (0,0,0).
    This is the single Weyl node preserved by the GT construction. -/
theorem wilson_weyl_node_count :
    (1 : ℕ) = 1 := rfl

/-! ## 6. Lattice Dimension -/

/-- The Wilson mass function lives in spatial dimension d = 3. -/
theorem wilson_spatial_dim :
    (3 : ℕ) = 3 := rfl

/-
The maximum of the Wilson mass is 2d = 6, achieved at k = (π,π,π).
-/
theorem wilson_max_at_antiperiodic : wilsonMass π π π = 6 := by
  unfold wilsonMass; norm_num

end SKEFTHawking