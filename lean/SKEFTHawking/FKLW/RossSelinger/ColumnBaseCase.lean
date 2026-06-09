/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 11) — the dim-4 column-lemma base case (number-theoretic heart)

The dim-4 exact synthesis (column lemma) inducts on the denominator exponent down to `0`. At
denominator exponent `0` the column has entries in `ℤ[ω]` and is a unit vector; this file proves its
structure: **exactly one entry is a unit (`ωᵏ`), the rest are `0`** — so the column is `ωᵏ·eᵢ`, which
is realizable by the basis-state permutation (`isColRealizableWithin_basis`, inc 10b) plus a global
`ω`-phase.

Crucially this needs **no** total-positivity / Galois-conjugate / Kronecker argument: since `normSq`
lands in `ℤ[ω]` with rational coordinate `(|z|²).d = a²+b²+c²+d²` (`normSq_coords`), the unit-column
identity `Σ |zᵢ|² = 1` reduces to the elementary **sum-of-four-squares** facts `Σ Pᵢ = 1` with each
`Pᵢ = aᵢ²+bᵢ²+cᵢ²+dᵢ² ≥ 0` — one `Pᵢ = 1`, the rest `0`.

## Headlines

  * `ZOmega.normSq_eq_one_iff_omega_pow` — `|z|² = 1 ↔ z = ωᵏ` for some `k < 8` (the units of `ℤ[ω]`
    of modulus 1 are exactly the 8th roots of unity; `⟸` is `normSq_omega_pow`, `⟹` is sum-of-four-
    squares = 1).
  * `ZOmega.normSq_eq_zero_iff` — `|z|² = 0 ↔ z = 0`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` (the per-case `z = ωᵏ` checks are kernel `decide` on bounded integer coordinates).
  Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
import SKEFTHawking.FKLW.RossSelinger.NormSqGde
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`|z|² = 0 ↔ z = 0`** in `ℤ[ω]`: the rational coordinate `(|z|²).d = a²+b²+c²+d²` is `0` iff all
coordinates vanish. -/
theorem normSq_eq_zero_iff {z : ZOmega} : normSq z = 0 ↔ z = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  constructor
  · intro h
    rw [normSq_coords] at h
    have hP : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 0 := by
      have := congrArg ZOmega.d h; simpa using this
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    rw [ha, hb, hc, hd]; rfl
  · intro h; rw [h, normSq_zero]

/-- **`|z|² = 1 ↔ z = ωᵏ`** (`k < 8`): the modulus-1 elements of `ℤ[ω]` are exactly the 8th roots of
unity. `⟸` is `normSq_omega_pow`; `⟹` reduces (`normSq_coords`) to `a²+b²+c²+d² = 1`, whose only
integer solutions are the signed basis vectors `±eᵢ = ω^{0..7}`. -/
theorem normSq_eq_one_iff_omega_pow {z : ZOmega} : normSq z = 1 ↔ ∃ k, k < 8 ∧ z = ω ^ k := by
  constructor
  · intro h
    obtain ⟨a, b, c, d⟩ := z
    rw [normSq_coords] at h
    have hP : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
      have := congrArg ZOmega.d h; simpa using this
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
    have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
    have hd2 : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have ha : -1 ≤ a ∧ a ≤ 1 := ⟨by nlinarith [sq_nonneg (a + 1)], by nlinarith [sq_nonneg (a - 1)]⟩
    have hb : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith [sq_nonneg (b + 1)], by nlinarith [sq_nonneg (b - 1)]⟩
    have hc : -1 ≤ c ∧ c ≤ 1 := ⟨by nlinarith [sq_nonneg (c + 1)], by nlinarith [sq_nonneg (c - 1)]⟩
    have hd : -1 ≤ d ∧ d ≤ 1 := ⟨by nlinarith [sq_nonneg (d + 1)], by nlinarith [sq_nonneg (d - 1)]⟩
    obtain ⟨ha1, ha2'⟩ := ha; obtain ⟨hb1, hb2'⟩ := hb
    obtain ⟨hc1, hc2'⟩ := hc; obtain ⟨hd1, hd2'⟩ := hd
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
      first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩ | exact ⟨3, by decide, by decide⟩ | exact ⟨4, by decide, by decide⟩ | exact ⟨5, by decide, by decide⟩ | exact ⟨6, by decide, by decide⟩ | exact ⟨7, by decide, by decide⟩ | exact absurd hP (by decide)
  · rintro ⟨k, _, rfl⟩; exact normSq_omega_pow k

/-- **A vanishing rational coordinate forces the element to vanish**: `(|z|²).d = 0 → z = 0`, since
`(|z|²).d = a²+b²+c²+d²`. -/
theorem normSq_d_eq_zero_imp {z : ZOmega} (h : (normSq z).d = 0) : z = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  rw [normSq_coords] at h
  have hP : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 0 := h
  have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  have hd : d = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
  rw [ha, hb, hc, hd]; rfl

/-- **denExp-0 unit-column structure.** For a column `v : Fin 2 × Fin 2 → ℤ[ω]` whose squared moduli
sum to `1` (a unit vector with no `√2` denominators — the column-lemma base case), **exactly one entry
has `|·|² = 1` and all others vanish**. Proof: the rational coordinate `(|v i|²).d = aᵢ²+bᵢ²+cᵢ²+dᵢ² ≥ 0`
sums to `1` (the `√2`-coordinate machinery is not needed), so exactly one is `1` and the rest `0`; a
zero rational coordinate forces the entry to vanish (`normSq_d_eq_zero_imp`). Combined with
`normSq_eq_one_iff_omega_pow`, the column is `ωᵏ·eᵢ`. -/
theorem unit_col_zero_denExp_structure (v : Fin 2 × Fin 2 → ZOmega)
    (h : ∑ i, normSq (v i) = 1) :
    ∃ i, normSq (v i) = 1 ∧ ∀ j, j ≠ i → v j = 0 := by
  have hnn : ∀ i, 0 ≤ (normSq (v i)).d := by
    intro i; obtain ⟨a, b, c, d⟩ := v i; rw [normSq_coords]; positivity
  have hd : ∑ i, (normSq (v i)).d = 1 := by
    let dH : ZOmega →+ ℤ := { toFun := ZOmega.d, map_zero' := rfl, map_add' := ZOmega.add_d }
    have hms := map_sum dH (fun i => normSq (v i)) Finset.univ
    simp only [dH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hms
    rw [← hms, h]; rfl
  have hle : ∀ i, (normSq (v i)).d ≤ 1 := fun i => by
    have hsl := Finset.single_le_sum (f := fun i => (normSq (v i)).d)
      (fun j _ => hnn j) (Finset.mem_univ i)
    rwa [hd] at hsl
  have hex : ∃ i, (normSq (v i)).d = 1 := by
    by_contra hc
    have hz : ∀ i, (normSq (v i)).d = 0 := fun i => by
      have h1 := hle i; have h2 := hnn i
      have h3 : (normSq (v i)).d ≠ 1 := fun he => hc ⟨i, he⟩
      omega
    rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const_zero] at hd
    exact absurd hd (by norm_num)
  obtain ⟨i₀, hi₀⟩ := hex
  have hrest : ∀ j, j ≠ i₀ → (normSq (v j)).d = 0 := by
    have hsplit : (normSq (v i₀)).d + ∑ j ∈ Finset.univ.erase i₀, (normSq (v j)).d = 1 :=
      (Finset.add_sum_erase Finset.univ (fun j => (normSq (v j)).d) (Finset.mem_univ i₀)).trans hd
    rw [hi₀] at hsplit
    have hrest0 : ∑ j ∈ Finset.univ.erase i₀, (normSq (v j)).d = 0 := by omega
    intro j hj
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn k)).mp hrest0 j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  have hvj : ∀ j, j ≠ i₀ → v j = 0 := fun j hj => normSq_d_eq_zero_imp (hrest j hj)
  refine ⟨i₀, ?_, hvj⟩
  rw [← h, Finset.sum_eq_single i₀ (fun j _ hj => by rw [hvj j hj, normSq_zero])
    (fun hni => absurd (Finset.mem_univ i₀) hni)]

end ZOmega

end SKEFTHawking.RossSelinger
