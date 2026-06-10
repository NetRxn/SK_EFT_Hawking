/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 3, site 3/4 inc 4a — `ℤ[ω]` torsion classification (norm-quantized elements)

Substrate toward eliminating the `cliffordBase_box_core` `native_decide`: the elements of the
three exact squared-modulus classes `|z|² ∈ {1, 2, 4}` are precisely the torsion-unit scalings

  * `|z|² = 1 ⟹ z = ωʲ` (the 8 torsion units; coordinate sum-of-squares `= 1`),
  * `|z|² = 2 ⟹ z = √2·ωʲ` (the cross coordinates of `|z|²` exclude the 16 non-adjacent
    `±1`-pair patterns),
  * `|z|² = 4 ⟹ z = 2·ωʲ` (mod-4 square parity forces all-even or all-odd coordinates; the
    all-odd `±1⁴` patterns are excluded by the cross coordinates, the all-even case halves to
    the `|v|² = 1` class).

Architecture: each class theorem derives the coordinate ranges (`nlinarith` square bounds),
then dispatches to a range-driven case-bash `aux` lemma carrying its own heartbeat budget
(invariant #10 decomposition). The bash branches close by `decide` on the CLOSED substituted
`normSq` equation — no per-branch coordinate algebra.

Plus the Galois positivity `(|z|²).d² ≥ 2·(|z|²).c²` (the `ℤ[√2]`-norm of `|z|²` is
`|z·σ₅z|².d ≥ 0`), which pins the `√2`-part of a rational-constrained `normSq` — the engine of
the `|x|² ∈ {0, 2, 4}` quantization in inc 4b.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (range bashes decomposed into per-declaration
  budgets). **#15**: no new axioms. No `native_decide`.
  Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Bridge
import SKEFTHawking.FKLW.RossSelinger.NormSqGde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace ZOmega

/-! ### Square-parity helpers -/

/-- Even squares vanish mod 4. -/
theorem sq_emod_four_of_even {t : ℤ} (h : t % 2 = 0) : t * t % 4 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 2 * m := ⟨t / 2, by omega⟩
  have : 2 * m * (2 * m) = 4 * (m * m) := by ring
  omega

/-- Odd squares are `1` mod 4. -/
theorem sq_emod_four_of_odd {t : ℤ} (h : t % 2 = 1) : t * t % 4 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 2 * m + 1 := ⟨t / 2, by omega⟩
  have : (2 * m + 1) * (2 * m + 1) = 4 * (m * m + m) + 1 := by ring
  omega

/-! ### The torsion classes -/

/-- Range-driven case bash for the norm-1 class (own heartbeat budget; branches close by
`decide` on the closed substituted `normSq` projection). -/
theorem torsion_aux {a b c d : ℤ}
    (h : (normSq (⟨a, b, c, d⟩ : ZOmega)).d = 1)
    (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hc : c = -1 ∨ c = 0 ∨ c = 1) (hd : d = -1 ∨ d = 0 ∨ d = 1) :
    ∃ j < 8, (⟨a, b, c, d⟩ : ZOmega) = ω ^ j := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    first | exact absurd h (by decide) | decide

/-- **Norm-1 elements are the 8 torsion units**: `(|z|²).d = 1 ⟹ z = ωʲ` for some `j < 8`
(`ω⁴ = −1` folds the `±` into the exponent). -/
theorem torsion_of_normSq_d_eq_one {z : ZOmega} (h : (normSq z).d = 1) :
    ∃ j < 8, z = ω ^ j := by
  obtain ⟨a, b, c, d⟩ := z
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by rw [normSq_d] at h; simpa using h
  have ha : a = -1 ∨ a = 0 ∨ a = 1 := by
    have h1 : -1 ≤ a := by nlinarith [sq_nonneg (a + 1), sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have h2 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg b, sq_nonneg c, sq_nonneg d]
    omega
  have hb : b = -1 ∨ b = 0 ∨ b = 1 := by
    have h1 : -1 ≤ b := by nlinarith [sq_nonneg (b + 1), sq_nonneg a, sq_nonneg c, sq_nonneg d]
    have h2 : b ≤ 1 := by nlinarith [sq_nonneg (b - 1), sq_nonneg a, sq_nonneg c, sq_nonneg d]
    omega
  have hc : c = -1 ∨ c = 0 ∨ c = 1 := by
    have h1 : -1 ≤ c := by nlinarith [sq_nonneg (c + 1), sq_nonneg a, sq_nonneg b, sq_nonneg d]
    have h2 : c ≤ 1 := by nlinarith [sq_nonneg (c - 1), sq_nonneg a, sq_nonneg b, sq_nonneg d]
    omega
  have hd : d = -1 ∨ d = 0 ∨ d = 1 := by
    have h1 : -1 ≤ d := by nlinarith [sq_nonneg (d + 1), sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have h2 : d ≤ 1 := by nlinarith [sq_nonneg (d - 1), sq_nonneg a, sq_nonneg b, sq_nonneg c]
    omega
  exact torsion_aux h ha hb hc hd

/-- Range-driven case bash for the norm-2 class (own heartbeat budget). -/
theorem sqrt2_torsion_aux {a b c d : ℤ}
    (h : normSq (⟨a, b, c, d⟩ : ZOmega) = (⟨0, 0, 0, 2⟩ : ZOmega))
    (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (hc : c = -1 ∨ c = 0 ∨ c = 1) (hd : d = -1 ∨ d = 0 ∨ d = 1) :
    ∃ j < 8, (⟨a, b, c, d⟩ : ZOmega) = sqrt2 * ω ^ j := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
    first | exact absurd h (by decide) | decide

/-- **Norm-2 elements are `√2`-torsion**: `|z|² = ⟨0,0,0,2⟩ ⟹ z = √2·ωʲ` for some `j < 8`.
The `.d` coordinate forces two `±1` coordinates; the cross coordinates of the exact `normSq`
kill the 16 non-adjacent placements, leaving the 8 elements `√2·ωʲ`. -/
theorem sqrt2_torsion_of_normSq_eq_two {z : ZOmega}
    (h : normSq z = (⟨0, 0, 0, 2⟩ : ZOmega)) :
    ∃ j < 8, z = sqrt2 * ω ^ j := by
  obtain ⟨a, b, c, d⟩ := z
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 := by
    have hd' := congrArg ZOmega.d h
    rw [normSq_d] at hd'; simpa using hd'
  have ha : a = -1 ∨ a = 0 ∨ a = 1 := by
    have h1 : -1 ≤ a := by nlinarith [sq_nonneg (a + 1), sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have h2 : a ≤ 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg b, sq_nonneg c, sq_nonneg d]
    omega
  have hb : b = -1 ∨ b = 0 ∨ b = 1 := by
    have h1 : -1 ≤ b := by nlinarith [sq_nonneg (b + 1), sq_nonneg a, sq_nonneg c, sq_nonneg d]
    have h2 : b ≤ 1 := by nlinarith [sq_nonneg (b - 1), sq_nonneg a, sq_nonneg c, sq_nonneg d]
    omega
  have hc : c = -1 ∨ c = 0 ∨ c = 1 := by
    have h1 : -1 ≤ c := by nlinarith [sq_nonneg (c + 1), sq_nonneg a, sq_nonneg b, sq_nonneg d]
    have h2 : c ≤ 1 := by nlinarith [sq_nonneg (c - 1), sq_nonneg a, sq_nonneg b, sq_nonneg d]
    omega
  have hd : d = -1 ∨ d = 0 ∨ d = 1 := by
    have h1 : -1 ≤ d := by nlinarith [sq_nonneg (d + 1), sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have h2 : d ≤ 1 := by nlinarith [sq_nonneg (d - 1), sq_nonneg a, sq_nonneg b, sq_nonneg c]
    omega
  exact sqrt2_torsion_aux h ha hb hc hd

/-- Range-driven case bash for the all-odd norm-4 pattern (own heartbeat budget; every
`±1⁴` pattern is refuted by the cross coordinates of the closed `normSq` equation). -/
theorem two_torsion_aux {a b c d : ℤ}
    (h : normSq (⟨a, b, c, d⟩ : ZOmega) = (⟨0, 0, 0, 4⟩ : ZOmega))
    (ha : a = -1 ∨ a = 1) (hb : b = -1 ∨ b = 1)
    (hc : c = -1 ∨ c = 1) (hd : d = -1 ∨ d = 1) :
    ∃ j < 8, (⟨a, b, c, d⟩ : ZOmega) = 2 * ω ^ j := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    exact absurd h (by decide)

/-- **Norm-4 elements are `2`-torsion**: `|z|² = ⟨0,0,0,4⟩ ⟹ z = 2·ωʲ` for some `j < 8`.
Mod-4 square parity on `Σ coordᵢ² = 4` forces all-even or all-odd coordinates; the all-odd
`±1⁴` patterns die on the cross coordinates; the all-even case halves to the norm-1 class. -/
theorem two_torsion_of_normSq_eq_four {z : ZOmega}
    (h : normSq z = (⟨0, 0, 0, 4⟩ : ZOmega)) :
    ∃ j < 8, z = 2 * ω ^ j := by
  obtain ⟨a, b, c, d⟩ := z
  have hsum : a * a + b * b + c * c + d * d = 4 := by
    have hd' := congrArg ZOmega.d h
    rw [normSq_d] at hd'
    simp only at hd'
    nlinarith [hd']
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with hpa | hpa <;>
    rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hpb | hpb <;>
    rcases (by omega : c % 2 = 0 ∨ c % 2 = 1) with hpc | hpc <;>
    rcases (by omega : d % 2 = 0 ∨ d % 2 = 1) with hpd | hpd
  -- all-even case (first branch): halve and reduce to the norm-1 class
  · obtain ⟨a', rfl⟩ : ∃ t, a = 2 * t := ⟨a / 2, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ t, b = 2 * t := ⟨b / 2, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ t, c = 2 * t := ⟨c / 2, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ t, d = 2 * t := ⟨d / 2, by omega⟩
    have h2lit : (2 : ZOmega) = (⟨0, 0, 0, 2⟩ : ZOmega) := by decide
    have hz2 : (⟨2 * a', 2 * b', 2 * c', 2 * d'⟩ : ZOmega) = 2 * ⟨a', b', c', d'⟩ := by
      rw [h2lit]; ext <;> simp only [mul_a, mul_b, mul_c, mul_d] <;> ring
    rw [hz2] at h ⊢
    rw [normSq_mul, show normSq (2 : ZOmega) = (⟨0, 0, 0, 4⟩ : ZOmega) from by decide] at h
    have hv : normSq (⟨a', b', c', d'⟩ : ZOmega) = 1 := by
      have h4 := congrArg ZOmega.d h
      have h3 := congrArg ZOmega.c h
      have h2 := congrArg ZOmega.b h
      have h1 := congrArg ZOmega.a h
      simp only [mul_a, mul_b, mul_c, mul_d] at h1 h2 h3 h4
      ext <;> simp only [one_a, one_b, one_c, one_d] <;> omega
    obtain ⟨j, hj, hzj⟩ := torsion_of_normSq_d_eq_one (by rw [hv]; rfl)
    exact ⟨j, hj, by rw [hzj]⟩
  -- remaining 15 parity branches: mod-4 square residues kill every pattern with 1–3 odd
  -- coordinates (Σ sq = 4 ⟹ #odd ≡ 0 mod 4); only the all-odd pattern survives.
  all_goals (
    first | have s1 := sq_emod_four_of_even hpa | have s1 := sq_emod_four_of_odd hpa
    first | have s2 := sq_emod_four_of_even hpb | have s2 := sq_emod_four_of_odd hpb
    first | have s3 := sq_emod_four_of_even hpc | have s3 := sq_emod_four_of_odd hpc
    first | have s4 := sq_emod_four_of_even hpd | have s4 := sq_emod_four_of_odd hpd
    first
    | exact absurd hsum (by omega)
    | skip)
  -- all-odd survivor: coordinates are ±1 (each odd square is ≥ 1; the four sum to 4)
  have ha : a = -1 ∨ a = 1 := by
    have h2 : -2 ≤ a := by
      nlinarith [mul_self_nonneg (a + 2), mul_self_nonneg b, mul_self_nonneg c,
        mul_self_nonneg d]
    have h3 : a ≤ 2 := by
      nlinarith [mul_self_nonneg (a - 2), mul_self_nonneg b, mul_self_nonneg c,
        mul_self_nonneg d]
    omega
  have hb : b = -1 ∨ b = 1 := by
    have h2 : -2 ≤ b := by
      nlinarith [mul_self_nonneg (b + 2), mul_self_nonneg a, mul_self_nonneg c,
        mul_self_nonneg d]
    have h3 : b ≤ 2 := by
      nlinarith [mul_self_nonneg (b - 2), mul_self_nonneg a, mul_self_nonneg c,
        mul_self_nonneg d]
    omega
  have hc : c = -1 ∨ c = 1 := by
    have h2 : -2 ≤ c := by
      nlinarith [mul_self_nonneg (c + 2), mul_self_nonneg a, mul_self_nonneg b,
        mul_self_nonneg d]
    have h3 : c ≤ 2 := by
      nlinarith [mul_self_nonneg (c - 2), mul_self_nonneg a, mul_self_nonneg b,
        mul_self_nonneg d]
    omega
  have hd : d = -1 ∨ d = 1 := by
    have h2 : -2 ≤ d := by
      nlinarith [mul_self_nonneg (d + 2), mul_self_nonneg a, mul_self_nonneg b,
        mul_self_nonneg c]
    have h3 : d ≤ 2 := by
      nlinarith [mul_self_nonneg (d - 2), mul_self_nonneg a, mul_self_nonneg b,
        mul_self_nonneg c]
    omega
  exact two_torsion_aux h ha hb hc hd

/-! ### Galois positivity of `normSq` -/

/-- `σ₅` commutes with conjugation (`σ₃∘σ₅ = σ₇`-orbit arithmetic, coordinatewise). -/
theorem σ5_conj (z : ZOmega) : σ5 (conj z) = conj (σ5 z) := by
  ext <;> simp

/-- `σ₅` transports `normSq`: `σ₅(|z|²) = |σ₅ z|²`. -/
theorem σ5_normSq (z : ZOmega) : σ5 (normSq z) = normSq (σ5 z) := by
  rw [normSq, normSq, σ5_mul, σ5_conj]

/-- `normSq` is real: the `ω²`-coordinate vanishes. -/
theorem normSq_b_zero (z : ZOmega) : (normSq z).b = 0 := by
  simp only [normSq, mul_b, conj_a, conj_b, conj_c, conj_d]; ring

/-- `normSq` is real: the `ω³`-coordinate is minus the `ω`-coordinate. -/
theorem normSq_a_eq_neg_c (z : ZOmega) : (normSq z).a = -(normSq z).c := by
  simp only [normSq, mul_a, mul_c, conj_a, conj_b, conj_c, conj_d]; ring

/-- **Galois positivity**: `(|z|²).d² ≥ 2·(|z|²).c²` — the `ℤ[√2]`-norm of the real element
`|z|²` is `|z·σ₅z|².d ≥ 0` (a sum of integer squares). The engine pinning the `√2`-part of a
rational-constrained `normSq` (inc 4b quantization). -/
theorem normSq_galois_nonneg (z : ZOmega) :
    2 * (normSq z).c ^ 2 ≤ (normSq z).d ^ 2 := by
  have hkey : normSq z * σ5 (normSq z) = normSq (z * σ5 z) := by
    rw [σ5_normSq, normSq_mul]
  have hd := congrArg ZOmega.d hkey
  rw [mul_d, σ5_a, σ5_b, σ5_c, σ5_d, normSq_b_zero, normSq_a_eq_neg_c] at hd
  have hnn : 0 ≤ (normSq (z * σ5 z)).d := by
    rw [normSq_d]; positivity
  nlinarith [hd]

end ZOmega
end SKEFTHawking.RossSelinger
