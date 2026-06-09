/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 18) — Giles–Selinger residue-norm classification

The KMM (arXiv:1212.0822) circuit `C` is the **Giles–Selinger column lemma** (arXiv:1212.0506, Lemma 20),
whose reduction is **elementary**: a parity argument on entry residue-NORMS modulo 2 (Lemma 5) plus an
explicit 3-case H/T row operation (Lemma 4). This file ships the number-theoretic entry point: the
**residue-norm classification** — Giles–Selinger's fact that for `z ∈ ℤ[ω]`, the squared modulus `|z|²`
has residue norm `mod 2` in the THREE classes `{0000, 0001, 1010}` (never `1011`).

Concretely, with `|z|² = ⟨−Q, 0, Q, P⟩` (`normSq_coords`; `P = a²+b²+c²+d²`, `Q = ab−ad+cb+cd`), modulo 2:
`P ≡ a+b+c+d = u+v` and `Q ≡ ab+ad+cb+cd = (a+c)(b+d) = u·v` where `u = a+c`, `v = b+d`. So
`(P mod 2, Q mod 2) ∈ {(0,0), (1,0), (0,1)}` — the case `(1,1)` is impossible (`Q ≡ 1 ⟹ u = v = 1 ⟹
P ≡ 0`). The headline of this file is exactly that exclusion: `(|z|²).c` and `(|z|²).d` are never both odd.

This is the seed of the Lemma-5 parity argument (the unit column `Σ|wᵢ|² = 2^s` forces an even number of
each irreducible residue-norm class, so a matching pair exists for the Lemma-4 reduction).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` (the `decide` is KERNEL `decide` over `(ZMod 2)⁴`, 16 cases). Kernel-pure.
-/

import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`n % 2 = 0 ⟺ (n : ZMod 2) = 0`** (the `ℤ ↔ 𝔽₂` bridge). -/
theorem emod_two_eq_zero_iff_zmod {n : ℤ} : n % 2 = 0 ↔ (n : ZMod 2) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨fun h => by exact_mod_cast Int.dvd_of_emod_eq_zero h,
    fun h => Int.emod_eq_zero_of_dvd (by exact_mod_cast h)⟩

private theorem emod_two_eq_zero_of_zmod {n : ℤ} (h : (n : ZMod 2) = 0) : n % 2 = 0 :=
  emod_two_eq_zero_iff_zmod.mpr h

/-- **`(n : ZMod 2)` is the parity indicator**: `1` if `n` is odd, `0` if even. -/
theorem intCast_zmod2_eq_ite (n : ℤ) : (n : ZMod 2) = if n % 2 = 1 then 1 else 0 := by
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · rw [if_neg (by omega), ← emod_two_eq_zero_iff_zmod]; exact h
  · rw [if_pos h]
    have h0 : ((n - 1 : ℤ) : ZMod 2) = 0 := emod_two_eq_zero_iff_zmod.mp (by omega)
    push_cast at h0
    exact eq_of_sub_eq_zero h0

/-- **An even integer sum has an even number of odd summands.** If `∑ g ≡ 0 (mod 2)` over a `Fintype`,
the count of indices with `g i` odd is even — the parity engine of the Giles–Selinger Lemma-5
matching-pair argument. -/
theorem even_card_filter_of_sum_even {ι : Type*} [Fintype ι] (g : ι → ℤ)
    (hg : (∑ i, g i) % 2 = 0) :
    Even (Finset.univ.filter (fun i => g i % 2 = 1)).card := by
  rw [even_iff_two_dvd, ← CharP.cast_eq_zero_iff (ZMod 2) 2, ← Finset.sum_boole,
    Finset.sum_congr rfl (fun i _ => (intCast_zmod2_eq_ite (g i)).symm), ← Int.cast_sum]
  exact emod_two_eq_zero_iff_zmod.mp hg

/-- **Giles–Selinger residue-norm classification (the `{0000, 0001, 1010}` exclusion of `1011`).**
For `z ∈ ℤ[ω]`, the `√2`-coordinate `(|z|²).c` and the rational coordinate `(|z|²).d` are **never both
odd**. Equivalently `(P mod 2, Q mod 2) ≠ (1,1)`: with `u = a+c`, `v = b+d`, `Q ≡ uv` and `P ≡ u+v`, so
`Q` odd forces `u = v = 1`, hence `P ≡ 0`. The three admissible residue norms are `0000` (`P,Q` even),
`0001` (`P` odd, `Q` even), `1010` (`P` even, `Q` odd). -/
theorem normSq_cd_not_both_odd (z : ZOmega) :
    (normSq z).c % 2 = 0 ∨ (normSq z).d % 2 = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  simp only [normSq_coords]
  have key : ∀ x y w t : ZMod 2,
      x * y - x * t + w * y + w * t = 0 ∨ x ^ 2 + y ^ 2 + w ^ 2 + t ^ 2 = 0 := by decide
  rcases key (a : ZMod 2) (b : ZMod 2) (c : ZMod 2) (d : ZMod 2) with h | h
  · left
    refine emod_two_eq_zero_of_zmod ?_
    push_cast
    exact h
  · right
    refine emod_two_eq_zero_of_zmod ?_
    push_cast
    exact h

/-- The `√2`-coordinate as an additive hom `ℤ[ω] →+ ℤ`. -/
def cHom : ZOmega →+ ℤ := { toFun := ZOmega.c, map_zero' := rfl, map_add' := ZOmega.add_c }

/-- The rational coordinate as an additive hom `ℤ[ω] →+ ℤ`. -/
def dHom : ZOmega →+ ℤ := { toFun := ZOmega.d, map_zero' := rfl, map_add' := ZOmega.add_d }

/-- The `√2`-coordinate commutes with finite sums. -/
theorem sum_c {ι : Type*} (s : Finset ι) (f : ι → ZOmega) :
    (∑ i ∈ s, f i).c = ∑ i ∈ s, (f i).c := map_sum cHom f s

/-- The rational coordinate commutes with finite sums. -/
theorem sum_d {ι : Type*} (s : Finset ι) (f : ι → ZOmega) :
    (∑ i ∈ s, f i).d = ∑ i ∈ s, (f i).d := map_sum dHom f s

/-- **`√2 ∣ z` ⟺ the residue norm is `0000`** (`(|z|²).c` and `(|z|²).d` both even). With `u = a+c`,
`v = b+d`: `√2 ∣ z ⟺ a≡c ∧ b≡d ⟺ u≡v≡0`, and the residue norm is `0000 ⟺ (uv, u+v) ≡ (0,0) ⟺ u≡v≡0`.
So the "active" (irreducible) entries — those NOT divisible by `√2` (residue norm `0001` or `1010`) —
are exactly those with `(|z|²).c` or `(|z|²).d` odd. -/
theorem dividesSqrt2_iff_normSq_cd_even (z : ZOmega) :
    dividesSqrt2 z ↔ (normSq z).c % 2 = 0 ∧ (normSq z).d % 2 = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  have hbridge : ∀ m n : ℤ, m % 2 = n % 2 ↔ (m : ZMod 2) = (n : ZMod 2) := fun m n =>
    (ZMod.intCast_eq_intCast_iff m n 2).symm
  have hz : ∀ n : ℤ, n % 2 = 0 ↔ (n : ZMod 2) = 0 := fun n =>
    ⟨fun h => by rw [← Int.cast_zero (R := ZMod 2)]; exact (hbridge n 0).mp (by simpa using h),
     emod_two_eq_zero_of_zmod⟩
  simp only [normSq_coords, dividesSqrt2, hbridge, hz]
  have key : ∀ x y w t : ZMod 2,
      (x = w ∧ y = t) ↔
        (x * y - x * t + w * y + w * t = 0 ∧ x ^ 2 + y ^ 2 + w ^ 2 + t ^ 2 = 0) := by decide
  push_cast
  exact key (a : ZMod 2) (b : ZMod 2) (c : ZMod 2) (d : ZMod 2)

end ZOmega

end SKEFTHawking.RossSelinger
