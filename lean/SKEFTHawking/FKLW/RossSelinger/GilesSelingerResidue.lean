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

/-- **Giles–Selinger Lemma 5 (matching-residue-norm pair exists).** For a dim-4 column `w` whose
squared-modulus sum has even `√2`- and rational coordinates (`(Σ|wᵢ|²).c`, `(Σ|wᵢ|²).d` both even —
which the unit condition `Σ|wᵢ|² = 2^s`, `s ≥ 1`, supplies), if some entry `w i₀` is **active** (not
`√2`-divisible, i.e. residue norm `0001` or `1010`), then there exist **two distinct entries with the
same residue norm mod 2**, both active. (The active entry lies in the `.c`-odd (`1010`) or `.d`-odd
(`0001`) class; that class's count is EVEN by `even_card_filter_of_sum_even`, hence `≥ 2`; the two share
both residue coordinates by `normSq_cd_not_both_odd`.) This is exactly the pair Lemma 4's row operation
reduces. -/
theorem exists_matching_residue_pair {w : Fin 2 × Fin 2 → ZOmega}
    (hc : (∑ i, normSq (w i)).c % 2 = 0) (hd : (∑ i, normSq (w i)).d % 2 = 0)
    {i₀ : Fin 2 × Fin 2} (hact : ¬ dividesSqrt2 (w i₀)) :
    ∃ i j, i ≠ j ∧ (normSq (w i)).c % 2 = (normSq (w j)).c % 2 ∧
      (normSq (w i)).d % 2 = (normSq (w j)).d % 2 ∧ ¬ dividesSqrt2 (w i) := by
  rw [sum_c] at hc
  rw [sum_d] at hd
  have hEc : Even (Finset.univ.filter (fun i => (normSq (w i)).c % 2 = 1)).card :=
    even_card_filter_of_sum_even (fun i => (normSq (w i)).c) hc
  have hEd : Even (Finset.univ.filter (fun i => (normSq (w i)).d % 2 = 1)).card :=
    even_card_filter_of_sum_even (fun i => (normSq (w i)).d) hd
  have hi0 : (normSq (w i₀)).c % 2 = 1 ∨ (normSq (w i₀)).d % 2 = 1 := by
    by_contra h
    rw [not_or] at h
    rcases Int.emod_two_eq_zero_or_one (normSq (w i₀)).c with hc0 | hc1
    · rcases Int.emod_two_eq_zero_or_one (normSq (w i₀)).d with hd0 | hd1
      · exact hact ((dividesSqrt2_iff_normSq_cd_even (w i₀)).mpr ⟨hc0, hd0⟩)
      · exact h.2 hd1
    · exact h.1 hc1
  rcases hi0 with hi0 | hi0
  · have hmem : i₀ ∈ Finset.univ.filter (fun i => (normSq (w i)).c % 2 = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩
    have hpos : 0 < (Finset.univ.filter (fun i => (normSq (w i)).c % 2 = 1)).card :=
      Finset.card_pos.mpr ⟨i₀, hmem⟩
    have hcard : 1 < (Finset.univ.filter (fun i => (normSq (w i)).c % 2 = 1)).card := by
      rcases hEc with ⟨k, hk⟩; omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
    have hpi := (Finset.mem_filter.mp hi).2
    have hpj := (Finset.mem_filter.mp hj).2
    refine ⟨i, j, hij, by rw [hpi, hpj], ?_, ?_⟩
    · have hdi : (normSq (w i)).d % 2 = 0 := (normSq_cd_not_both_odd (w i)).resolve_left (by omega)
      have hdj : (normSq (w j)).d % 2 = 0 := (normSq_cd_not_both_odd (w j)).resolve_left (by omega)
      rw [hdi, hdj]
    · exact fun hdvd => by have := ((dividesSqrt2_iff_normSq_cd_even (w i)).mp hdvd).1; omega
  · have hmem : i₀ ∈ Finset.univ.filter (fun i => (normSq (w i)).d % 2 = 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩
    have hpos : 0 < (Finset.univ.filter (fun i => (normSq (w i)).d % 2 = 1)).card :=
      Finset.card_pos.mpr ⟨i₀, hmem⟩
    have hcard : 1 < (Finset.univ.filter (fun i => (normSq (w i)).d % 2 = 1)).card := by
      rcases hEd with ⟨k, hk⟩; omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
    have hpi := (Finset.mem_filter.mp hi).2
    have hpj := (Finset.mem_filter.mp hj).2
    refine ⟨i, j, hij, ?_, by rw [hpi, hpj], ?_⟩
    · have hci : (normSq (w i)).c % 2 = 0 := (normSq_cd_not_both_odd (w i)).resolve_right (by omega)
      have hcj : (normSq (w j)).c % 2 = 0 := (normSq_cd_not_both_odd (w j)).resolve_right (by omega)
      rw [hci, hcj]
    · exact fun hdvd => by have := ((dividesSqrt2_iff_normSq_cd_even (w i)).mp hdvd).2; omega

end ZOmega

end SKEFTHawking.RossSelinger
