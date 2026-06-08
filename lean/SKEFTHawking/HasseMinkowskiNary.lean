import Mathlib
import SKEFTHawking.PadicSquare
import SKEFTHawking.HasseMinkowskiGlobal

/-!
# Hasse–Minkowski rank reduction (`n ≥ 5`) and the general `n`-ary diagonal local–global principle

This module builds the **general-rank** diagonal Hasse–Minkowski theorem on top of the completed
base cases:

* `n = 2` : `PadicSquare.binary_solvable_of_local`
* `n = 3` : `PadicSquare.diag_ternary_solvable_of_local`
* `n = 4` : `HasseMinkowskiGlobal.diag_quaternary_zero_of_local` (the genuinely hard Serre Thm 4 summit)

The remaining content is the classical **Meyer reduction** (`n ≥ 5 → n − 1`, Serre, *Course in
Arithmetic*, IV §3.2, proof of Theorem 8): split off a binary `c₀x₀² + c₁x₁²`, find a global value `a`
represented by it that matches the local square classes of the local zeros at the finite "bad" set, and
descend to the rank-`(n−1)` form `⟨a, c₂, …, c_{n−1}⟩`. The local inputs for the descent are free for
rank `≥ 5`: at good odd primes the residual unit form is isotropic hence universal
(`PadicSquare.exists_diag_nary_zero_odd_padic` + `represents_of_isotropic_diag` below), and over ℝ the
form is indefinite.

## Anti-circularity

Routes through quadratic-form / Hilbert-symbol arithmetic only (reciprocity, Dirichlet, the product
formula, and the completed `n ≤ 4` bases). It does NOT use ABP, the Adams spectral sequence, or Rokhlin's
theorem — `16 ∣ σ` is the eventual conclusion downstream.
-/

namespace SKEFTHawking

open Finset

/-- **Isotropic diagonal form is universal.** Over a field of characteristic `≠ 2`, a diagonal form
`∑ wᵢ xᵢ²` with every coefficient nonzero that has a *nontrivial* zero represents *every* value `t`.
(Concretely: with `∑ wᵢ vᵢ² = 0`, `v ≠ 0`, pick `j` with `vⱼ ≠ 0`; the vector `x = s • v + e_j` has
`q(x) = wⱼ(2 vⱼ s + 1)`, which equals `t` for `s = (t − wⱼ)/(2 wⱼ vⱼ)`.) This is the "good place" engine
of the Meyer rank reduction: at primes where the residual unit form is isotropic it represents any
target value. -/
theorem represents_of_isotropic_diag {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    {n : ℕ} (w : Fin n → K) (hw : ∀ i, w i ≠ 0)
    (hiso : ∃ v : Fin n → K, v ≠ 0 ∧ ∑ i, w i * v i ^ 2 = 0) :
    ∀ t : K, ∃ x : Fin n → K, ∑ i, w i * x i ^ 2 = t := by
  obtain ⟨v, hv0, hvz⟩ := hiso
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
  simp only [Pi.zero_apply] at hj
  intro t
  set s : K := (t - w j) / (2 * w j * v j) with hs
  have hwj := hw j
  refine ⟨fun i => v i * s + (if i = j then 1 else 0), ?_⟩
  have key : ∀ i, w i * (v i * s + (if i = j then (1 : K) else 0)) ^ 2
      = w i * v i ^ 2 * s ^ 2 + (if i = j then w j * (2 * v j * s + 1) else 0) := by
    intro i
    by_cases h : i = j
    · simp only [if_pos h]; subst h; ring
    · simp only [if_neg h]; ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ j (fun _ => w j * (2 * v j * s + 1))]
  simp only [Finset.mem_univ, if_true]
  have h1 : ∑ i, w i * v i ^ 2 * s ^ 2 = 0 := by rw [← Finset.sum_mul, hvz, zero_mul]
  rw [h1, zero_add, hs]
  field_simp
  ring

/-- **Good odd place: a rank `≥ 3` unit diagonal form over `ℚ_[p]` is universal.** For an odd prime `p`,
`n ≥ 3`, and norm-1 coefficients, `∑ wᵢ xᵢ²` represents every `t ∈ ℚ_[p]`. (The form is isotropic by
`PadicSquare.exists_diag_nary_zero_odd_padic_unit`; `represents_of_isotropic_diag` upgrades isotropy to
universality — `ℚ_[p]` has characteristic `0`, so `(2 : ℚ_[p]) ≠ 0`.) This is the residual-form input at the
good primes of the Meyer rank reduction: outside the finitely many bad primes the rank-`(n−2)` residual unit
form represents the value `−a` chosen for the descent. -/
theorem represents_of_units_odd_padic {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (w : Fin n → ℚ_[p]) (hw : ∀ i, ‖w i‖ = 1) (t : ℚ_[p]) :
    ∃ x : Fin n → ℚ_[p], ∑ i, w i * x i ^ 2 = t := by
  refine represents_of_isotropic_diag two_ne_zero w (fun i => ?_) ?_ t
  · exact norm_ne_zero_iff.mp (by rw [hw i]; norm_num)
  · exact exists_diag_nary_zero_odd_padic_unit hp hn w hw

/-- **Rank-reduction assembly (pure algebra).** If the leading binary `⟨c₀, c₁⟩` represents a nonzero value
`a`, and the descended rank-`(m+1)` form `⟨a, R⟩` (over ℚ) is isotropic, then the rank-`(m+2)` form
`⟨c₀, c₁, R⟩` is isotropic. (Substitute `a = c₀ u₀² + c₁ u₁²` into the descended zero `a y₀² + R(y') = 0`
and split the `a`-term: the witness is `x = (u₀ y₀, u₁ y₀, y')`. Nonzero: if `y₀ = 0` the residual tail
`y'` survives; if `y₀ ≠ 0` then `a ≠ 0 ⟹ u₀ ≠ 0 ∨ u₁ ≠ 0` makes a leading coordinate nonzero.) This is the
descent half of the Meyer reduction, isolating the algebra from the global-value construction. -/
theorem reduction_assembly {m : ℕ} {c0 c1 a : ℚ} (ha : a ≠ 0) {R : Fin m → ℚ}
    (hB : ∃ u0 u1 : ℚ, c0 * u0 ^ 2 + c1 * u1 ^ 2 = a)
    (hg : ∃ y : Fin (m + 1) → ℚ, y ≠ 0 ∧ ∑ i, (Fin.cons a R : Fin (m + 1) → ℚ) i * y i ^ 2 = 0) :
    ∃ x : Fin (m + 2) → ℚ, x ≠ 0 ∧
      ∑ i, (Fin.cons c0 (Fin.cons c1 R) : Fin (m + 2) → ℚ) i * x i ^ 2 = 0 := by
  obtain ⟨u0, u1, hBeq⟩ := hB
  obtain ⟨y, hy0, hgeq⟩ := hg
  rw [Fin.sum_univ_succ] at hgeq
  simp only [Fin.cons_zero, Fin.cons_succ] at hgeq
  refine ⟨Fin.cons (u0 * y 0) (Fin.cons (u1 * y 0) (fun i => y i.succ)), ?_, ?_⟩
  · intro hx
    by_cases hy00 : y 0 = 0
    · apply hy0
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hy00
      · have := congrFun hx j.succ.succ
        simpa [hy00] using this
    · have hu : u0 ≠ 0 ∨ u1 ≠ 0 := by
        by_contra h
        simp only [not_or, not_not] at h
        exact ha (by rw [← hBeq, h.1, h.2]; ring)
      rcases hu with hu | hu
      · exact mul_ne_zero hu hy00 (by simpa using congrFun hx 0)
      · exact mul_ne_zero hu hy00 (by simpa using congrFun hx 1)
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hR : ∑ i, R i * y i.succ ^ 2 = -(a * y 0 ^ 2) := by linarith [hgeq]
    rw [hR]
    have hsub : c0 * (u0 * y 0) ^ 2 + c1 * (u1 * y 0) ^ 2 = a * y 0 ^ 2 := by rw [← hBeq]; ring
    linarith [hsub]

end SKEFTHawking
