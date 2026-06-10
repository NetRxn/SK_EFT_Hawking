/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 3, increment 1 — the parity/valuation toolkit for the structural bridge

The structural replacement of the `bridge_box_core` `native_decide` (the `μ ≤ 3 ⟹ kSO3 ≤ 3`
bridge) reduces, after the Bloch-trace expansion, to **`√2² ∣ (x² ± y²)`** for the column
numerators of a `μ ≤ 3` unitary. This file proves that core (`sqrt2_sq_dvd_sq_add_sub`) from
elementary parity arithmetic on `ℤ[ω]`-coordinates:

  * the **parity** `(a+b+c+d) mod 2` controls everything at level 1:
    `√2 ∣ |z|² ⟺ √2 ∣ z² ⟺ parity z even` (the residue ring `ℤ[ω]/√2` in coordinates);
  * `δ = 1 + ω` is the ramified prime (`δ² = √2·⟨0,1,1,1⟩`), and parity-even elements split
    off a `δ` (`divDelta`, an explicit coordinate witness);
  * **equal-parity squares agree mod `√2`**, so after pulling out `δ` from both numerators,
    `x² ± y² = δ²·(x'² ± y'²)` carries `√2·√2`;
  * the mixed case (`√2 ∣ x`, `√2 ∤ y`) is **impossible** under the unit-column equation
    `|x|² + |y|² = √2⁴` — by the halving lemma (`dvdSqrt2Pow_normSq_half`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Giles–Selinger arXiv:1312.6584 Cor 7.11 (the `sde ↔ k_SO3` bridge this supports).
  * Kliuchnikov–Maslov–Mosca arXiv:1206.5236 §3 (the `√2`-valuation framework).
-/

import SKEFTHawking.FKLW.RossSelinger.CrossTermGde
import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
import SKEFTHawking.FKLW.RossSelinger.ZOmegaEuclideanDomain

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace ZOmega

/-! ### Parity arithmetic -/

/-- `t² ≡ t (mod 2)` over `ℤ`. -/
theorem sq_emod_two (t : ℤ) : t * t % 2 = t % 2 := by
  rcases Int.even_or_odd t with ⟨m, hm⟩ | ⟨m, hm⟩
  · have ht : t * t = 2 * (2 * (m * m)) := by rw [hm]; ring
    omega
  · have ht : t * t = 2 * (2 * (m * m) + 2 * m) + 1 := by rw [hm]; ring
    omega

/-- **`√2 ∣ |z|² ⟺ parity even`**: the rational coordinate of `|z|²` is `Σ coordᵢ²`, which has
the parity of `Σ coordᵢ`; the `√2`-coordinate condition is automatic. -/
theorem dividesSqrt2_normSq_iff (z : ZOmega) :
    dividesSqrt2 (normSq z) ↔ (z.a + z.b + z.c + z.d) % 2 = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  rw [normSq_coords]
  show -(a * b - a * d + c * b + c * d) % 2 = (a * b - a * d + c * b + c * d) % 2 ∧
      (0 : ℤ) % 2 = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) % 2 ↔ (a + b + c + d) % 2 = 0
  have e1 : -(a * b - a * d + c * b + c * d) % 2 = (a * b - a * d + c * b + c * d) % 2 := by
    have h : -(a * b - a * d + c * b + c * d)
        = (a * b - a * d + c * b + c * d) - 2 * (a * b - a * d + c * b + c * d) := by ring
    omega
  have e2 : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) % 2 = (a + b + c + d) % 2 := by
    have h1 := sq_emod_two a
    have h2 := sq_emod_two b
    have h3 := sq_emod_two c
    have h4 := sq_emod_two d
    have h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = a * a + b * b + c * c + d * d := by ring
    omega
  constructor
  · rintro ⟨-, h⟩
    omega
  · intro h
    exact ⟨e1, by omega⟩

/-- **`√2 ∣ z² ⟺ parity even`**: the `ω³`/`ω`-coordinates of `z²` are always even, and the
`ω²`/constant coordinates differ by `(a+c) − (b+d) ≡ Σ coordᵢ (mod 2)`. -/
theorem dividesSqrt2_mul_self_iff (z : ZOmega) :
    dividesSqrt2 (z * z) ↔ (z.a + z.b + z.c + z.d) % 2 = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  show (a * d + b * c + c * b + d * a) % 2 = (-(a * b) - b * a + c * d + d * c) % 2 ∧
      (-(a * a) + b * d + c * c + d * b) % 2 = (-(a * c) - b * b - c * a + d * d) % 2 ↔
      (a + b + c + d) % 2 = 0
  have e1 : (a * d + b * c + c * b + d * a) % 2 = 0 := by
    have h : a * d + b * c + c * b + d * a = 2 * (a * d + b * c) := by ring
    omega
  have e2 : (-(a * b) - b * a + c * d + d * c) % 2 = 0 := by
    have h : -(a * b) - b * a + c * d + d * c = 2 * (c * d - a * b) := by ring
    omega
  have e3 : (-(a * a) + b * d + c * c + d * b) % 2 = (a + c) % 2 := by
    have h1 := sq_emod_two a
    have h3 := sq_emod_two c
    have h : -(a * a) + b * d + c * c + d * b
        = (a * a + c * c) + 2 * (b * d) - 2 * (a * a) := by ring
    omega
  have e4 : (-(a * c) - b * b - c * a + d * d) % 2 = (b + d) % 2 := by
    have h2 := sq_emod_two b
    have h4 := sq_emod_two d
    have h : -(a * c) - b * b - c * a + d * d
        = (b * b + d * d) - 2 * (a * c) - 2 * (b * b) := by ring
    omega
  constructor
  · rintro ⟨-, h⟩
    omega
  · intro h
    exact ⟨by omega, by omega⟩

/-- **Equal parities make `x² ± y²` `√2`-divisible** (equal-parity squares agree mod `√2`).
Both signs at once. -/
theorem dividesSqrt2_sq_add_sub_of_parity_eq {x y : ZOmega}
    (h : (x.a + x.b + x.c + x.d) % 2 = (y.a + y.b + y.c + y.d) % 2) :
    dividesSqrt2 (x * x - y * y) ∧ dividesSqrt2 (x * x + y * y) := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨a', b', c', d'⟩ := y
  simp only at h
  have q1 := sq_emod_two a
  have q2 := sq_emod_two b
  have q3 := sq_emod_two c
  have q4 := sq_emod_two d
  have q5 := sq_emod_two a'
  have q6 := sq_emod_two b'
  have q7 := sq_emod_two c'
  have q8 := sq_emod_two d'
  constructor
  · show (a * d + b * c + c * b + d * a - (a' * d' + b' * c' + c' * b' + d' * a')) % 2
        = (-(a * b) - b * a + c * d + d * c - (-(a' * b') - b' * a' + c' * d' + d' * c')) % 2 ∧
      (-(a * a) + b * d + c * c + d * b - (-(a' * a') + b' * d' + c' * c' + d' * b')) % 2
        = (-(a * c) - b * b - c * a + d * d - (-(a' * c') - b' * b' - c' * a' + d' * d')) % 2
    refine ⟨?_, ?_⟩
    · have hL : a * d + b * c + c * b + d * a - (a' * d' + b' * c' + c' * b' + d' * a')
          = 2 * (a * d + b * c - a' * d' - b' * c') := by ring
      have hR : -(a * b) - b * a + c * d + d * c - (-(a' * b') - b' * a' + c' * d' + d' * c')
          = 2 * (c * d - a * b - c' * d' + a' * b') := by ring
      omega
    · have hL : -(a * a) + b * d + c * c + d * b - (-(a' * a') + b' * d' + c' * c' + d' * b')
          = (a * a + c * c) - (a' * a' + c' * c')
            + 2 * (b * d - b' * d' - a * a + a' * a') := by ring
      have hR : -(a * c) - b * b - c * a + d * d - (-(a' * c') - b' * b' - c' * a' + d' * d')
          = (b * b + d * d) - (b' * b' + d' * d')
            - 2 * (a * c - a' * c' + b * b - b' * b') := by ring
      omega
  · show (a * d + b * c + c * b + d * a + (a' * d' + b' * c' + c' * b' + d' * a')) % 2
        = (-(a * b) - b * a + c * d + d * c + (-(a' * b') - b' * a' + c' * d' + d' * c')) % 2 ∧
      (-(a * a) + b * d + c * c + d * b + (-(a' * a') + b' * d' + c' * c' + d' * b')) % 2
        = (-(a * c) - b * b - c * a + d * d + (-(a' * c') - b' * b' - c' * a' + d' * d')) % 2
    refine ⟨?_, ?_⟩
    · have hL : a * d + b * c + c * b + d * a + (a' * d' + b' * c' + c' * b' + d' * a')
          = 2 * (a * d + b * c + a' * d' + b' * c') := by ring
      have hR : -(a * b) - b * a + c * d + d * c + (-(a' * b') - b' * a' + c' * d' + d' * c')
          = 2 * (c * d - a * b + c' * d' - a' * b') := by ring
      omega
    · have hL : -(a * a) + b * d + c * c + d * b + (-(a' * a') + b' * d' + c' * c' + d' * b')
          = (a * a + c * c) + (a' * a' + c' * c')
            + 2 * (b * d + b' * d' - a * a - a' * a') := by ring
      have hR : -(a * c) - b * b - c * a + d * d + (-(a' * c') - b' * b' - c' * a' + d' * d')
          = (b * b + d * d) + (b' * b' + d' * d')
            - 2 * (a * c + a' * c' + b * b + b' * b') := by ring
      omega

/-! ### The ramified prime `δ = 1 + ω` -/

/-- The ramified prime `δ = 1 + ω` of `ℤ[ω]` (`δ² ~ √2`). -/
def delta : ZOmega := ⟨0, 0, 1, 1⟩

/-- `δ² = √2 · ⟨0,1,1,1⟩` (the explicit unit-completed ramification `δ² = λω√2`). -/
theorem delta_sq : delta * delta = sqrt2 * ⟨0, 1, 1, 1⟩ := by decide

/-- The explicit `δ`-quotient of a parity-even element. -/
def divDelta (w : ZOmega) : ZOmega :=
  ⟨(w.a - w.b + w.c - w.d) / 2,
   w.a - (w.a - w.b + w.c - w.d) / 2,
   w.b - (w.a - (w.a - w.b + w.c - w.d) / 2),
   w.c - (w.b - (w.a - (w.a - w.b + w.c - w.d) / 2))⟩

/-- **Parity-even elements split off a `δ`**: `δ · divDelta w = w`. -/
theorem delta_mul_divDelta {w : ZOmega} (h : (w.a + w.b + w.c + w.d) % 2 = 0) :
    delta * divDelta w = w := by
  obtain ⟨a, b, c, d⟩ := w
  simp only at h
  ext <;> simp only [divDelta, delta, mul_a, mul_b, mul_c, mul_d] <;> omega

/-- **`√2 ∣ δ·z ⟺ parity z even`** (multiplying by the uniformizer shifts the valuation by one
half-step). -/
theorem dividesSqrt2_delta_mul_iff (z : ZOmega) :
    dividesSqrt2 (delta * z) ↔ (z.a + z.b + z.c + z.d) % 2 = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  show ((0 : ℤ) * d + 0 * c + 1 * b + 1 * a) % 2 = (-((0 : ℤ) * b) - 0 * a + 1 * d + 1 * c) % 2 ∧
      (-((0 : ℤ) * a) + 0 * d + 1 * c + 1 * b) % 2 = (-((0 : ℤ) * c) - 0 * b - 1 * a + 1 * d) % 2
      ↔ (a + b + c + d) % 2 = 0
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · intro h
    omega

/-! ### Conjugate-pair `+1` lemmas (the `−` variant of `dvdSqrt2Pow_add_conj`) -/

/-- `√2^m ∣ w ⟹ √2^(m+1) ∣ (w − conj w)` (the `−`-twin of `dvdSqrt2Pow_add_conj`):
`w − w̄ = (w + w̄) − 2·w̄`, and `2·w̄` carries `m + 2`. -/
theorem dvdSqrt2Pow_sub_conj {w : ZOmega} {m : ℕ} (h : dvdSqrt2Pow w m) :
    dvdSqrt2Pow (w - conj w) (m + 1) := by
  have hadd := dvdSqrt2Pow_add_conj h
  rw [dvdSqrt2Pow_iff] at h hadd ⊢
  obtain ⟨v, hv⟩ := h
  obtain ⟨s, hs⟩ := hadd
  have hconj : conj w = sqrt2 ^ m * conj v := by rw [hv, conj_mul, conj_sqrt2_pow]
  refine ⟨s - sqrt2 * conj v, ?_⟩
  have hsub : w - conj w = (w + conj w) - 2 * conj w := by ring
  rw [hsub, hs, hconj, show (2 : ZOmega) = sqrt2 * sqrt2 from by decide]
  ring

/-- Unit transport: `√2^m ∣ z ⟹ √2^m ∣ ω^j·z`. -/
theorem dvdSqrt2Pow_omega_pow_mul' {z : ZOmega} {m : ℕ} (j : ℕ) (h : dvdSqrt2Pow z m) :
    dvdSqrt2Pow (ω ^ j * z) m := by
  rw [dvdSqrt2Pow_iff] at h ⊢
  exact Dvd.dvd.mul_left h _

/-! ### The level-2 core -/

/-- **The structural-bridge core**: for column numerators with `|x|² + |y|² = √2⁴` (the cleared
unit-column equation) and `√2 ∣ |x|²` (the `μ ≤ 3` condition), both `x² − y²` and `x² + y²`
carry `√2²`. -/
theorem sqrt2_sq_dvd_sq_add_sub {x y : ZOmega}
    (hsum : normSq x + normSq y = sqrt2 ^ 4) (hx : dividesSqrt2 (normSq x)) :
    dvdSqrt2Pow (x * x - y * y) 2 ∧ dvdSqrt2Pow (x * x + y * y) 2 := by
  have hy : dividesSqrt2 (normSq y) := by
    rw [dividesSqrt2_iff_dvd] at hx ⊢
    have h4 : (sqrt2 : ZOmega) ∣ sqrt2 ^ 4 := ⟨sqrt2 ^ 3, by ring⟩
    have hyeq : normSq y = sqrt2 ^ 4 - normSq x := by rw [← hsum]; ring
    rw [hyeq]
    exact dvd_sub h4 hx
  -- the divisibility of one numerator forces the other (halving through the unit-column sum)
  have hforce : ∀ u v : ZOmega, normSq u + normSq v = sqrt2 ^ 4 → dividesSqrt2 u →
      dividesSqrt2 v := by
    intro u v huv hu
    have hspec := divSqrt2_spec hu
    have hnv2 : dvdSqrt2Pow (normSq v) 2 := by
      rw [dvdSqrt2Pow_iff]
      refine ⟨sqrt2 ^ 2 - normSq (divSqrt2 u), ?_⟩
      have hnu : normSq u = sqrt2 ^ 2 * normSq (divSqrt2 u) := by
        conv_lhs => rw [← hspec]
        rw [normSq_mul, normSq_sqrt2, show (2 : ZOmega) = sqrt2 ^ 2 from by decide]
      have hveq : normSq v = sqrt2 ^ 4 - normSq u := by rw [← huv]; ring
      rw [hveq, hnu]
      ring
    have h1 := dvdSqrt2Pow_normSq_half 1 v (by rwa [show 2 * 1 = 2 from rfl])
    rw [show (1 : ℕ) = 0 + 1 from rfl, dvdSqrt2Pow_succ] at h1
    exact h1.1
  by_cases hxd : dividesSqrt2 x
  · -- both divisible: the squares carry √2² separately
    have hyd : dividesSqrt2 y := hforce x y hsum hxd
    have hxs := divSqrt2_spec hxd
    have hys := divSqrt2_spec hyd
    refine ⟨?_, ?_⟩
    · rw [dvdSqrt2Pow_iff]
      refine ⟨divSqrt2 x * divSqrt2 x - divSqrt2 y * divSqrt2 y, ?_⟩
      conv_lhs => rw [← hxs, ← hys]
      ring
    · rw [dvdSqrt2Pow_iff]
      refine ⟨divSqrt2 x * divSqrt2 x + divSqrt2 y * divSqrt2 y, ?_⟩
      conv_lhs => rw [← hxs, ← hys]
      ring
  · -- neither divisible: δ-split + equal-parity squares agree mod √2
    have hyd : ¬ dividesSqrt2 y := fun hyd =>
      hxd (hforce y x (by rw [← hsum]; ring) hyd)
    have hxpar : (x.a + x.b + x.c + x.d) % 2 = 0 := (dividesSqrt2_normSq_iff x).mp hx
    have hypar : (y.a + y.b + y.c + y.d) % 2 = 0 := (dividesSqrt2_normSq_iff y).mp hy
    have hxsplit := delta_mul_divDelta hxpar
    have hysplit := delta_mul_divDelta hypar
    set x' := divDelta x with hx'
    set y' := divDelta y with hy'
    have hx'odd : (x'.a + x'.b + x'.c + x'.d) % 2 = 1 := by
      by_contra hcon
      have h0 : (x'.a + x'.b + x'.c + x'.d) % 2 = 0 := by omega
      exact hxd (by rw [← hxsplit]; exact (dividesSqrt2_delta_mul_iff x').mpr h0)
    have hy'odd : (y'.a + y'.b + y'.c + y'.d) % 2 = 1 := by
      by_contra hcon
      have h0 : (y'.a + y'.b + y'.c + y'.d) % 2 = 0 := by omega
      exact hyd (by rw [← hysplit]; exact (dividesSqrt2_delta_mul_iff y').mpr h0)
    obtain ⟨hsub', hadd'⟩ :=
      dividesSqrt2_sq_add_sub_of_parity_eq (x := x') (y := y') (by omega)
    have hfacsub : x * x - y * y
        = sqrt2 * ((⟨0, 1, 1, 1⟩ : ZOmega) * (x' * x' - y' * y')) := by
      have h1 : x = delta * x' := hxsplit.symm
      have h2 : y = delta * y' := hysplit.symm
      rw [h1, h2]
      linear_combination (x' * x' - y' * y') * delta_sq
    have hfacadd : x * x + y * y
        = sqrt2 * ((⟨0, 1, 1, 1⟩ : ZOmega) * (x' * x' + y' * y')) := by
      have h1 : x = delta * x' := hxsplit.symm
      have h2 : y = delta * y' := hysplit.symm
      rw [h1, h2]
      linear_combination (x' * x' + y' * y') * delta_sq
    refine ⟨?_, ?_⟩
    · rw [hfacsub, show (2 : ℕ) = 1 + 1 from rfl, dvdSqrt2Pow_sqrt2_mul,
        show (1 : ℕ) = 0 + 1 from rfl, dvdSqrt2Pow_succ]
      refine ⟨?_, trivial⟩
      rw [dividesSqrt2_iff_dvd] at hsub' ⊢
      exact Dvd.dvd.mul_left hsub' _
    · rw [hfacadd, show (2 : ℕ) = 1 + 1 from rfl, dvdSqrt2Pow_sqrt2_mul,
        show (1 : ℕ) = 0 + 1 from rfl, dvdSqrt2Pow_succ]
      refine ⟨?_, trivial⟩
      rw [dividesSqrt2_iff_dvd] at hadd' ⊢
      exact Dvd.dvd.mul_left hadd' _

end ZOmega
end SKEFTHawking.RossSelinger
