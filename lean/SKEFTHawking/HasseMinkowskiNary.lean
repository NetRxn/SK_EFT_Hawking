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

end SKEFTHawking
