/-
Phase 5q.B: the indefinite-case input [HM] — local solvability bricks toward "an indefinite even unimodular
form has a primitive isotropic vector" (Hasse–Minkowski / Meyer).

This is one of the two remaining classical inputs to van der Blij (`VanDerBlijReduction.eight_dvd_latticeSig
_of_HM_of_Theta`). The full statement decomposes (anti-circular, no ABP):
  [HM-ℝ]   indefinite ⟹ represents 0 over ℝ (elementary; `sigPos>0 ∧ sigNeg>0`).
  [HM-p]   a nondegenerate (unimodular) form of rank ≥ 3 represents 0 over ℚ_p, for every prime `p`:
            • `p` odd: the reduction mod `p` is isotropic over 𝔽_p (THIS FILE: `finite_field_form_isotropic`,
              via Chevalley–Warning), then Hensel-lift (`Mathlib`'s Hensel) to ℤ_p;
            • `p = 2`: an even unimodular form of rank ≥ 3 over ℤ_2 contains a hyperbolic plane.
  [HM-LG]  Hasse–Minkowski local-global: solvable over ℝ and all ℚ_p ⟹ solvable over ℚ. (The frontier:
            needs the Hilbert symbol + its product formula + Dirichlet on primes in AP for rank 3,4 — not yet
            in Mathlib.)
  [HM-ℤ]   a ℚ-isotropic vector of a unimodular ℤ-form scales to a primitive ℤ-isotropic vector (elementary).

`finite_field_form_isotropic` is the residue-field core of [HM-p] at odd primes — a genuine, kernel-pure,
classical result built directly on Mathlib's Chevalley–Warning (`char_dvd_card_solutions`): over a finite
field, a symmetric form in `≥ 3` variables has a nonzero zero (the number of zeros is divisible by the
characteristic and includes `0`, so exceeds one).

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib

namespace SKEFTHawking

open Matrix MvPolynomial

/-- **A symmetric form over a finite field in `≥ 3` variables is isotropic.** For a finite field `K` and a
matrix `A` over `K` with `3 ≤ n`, there is a nonzero `x` with `xᵀ A x = 0`. Proof via Chevalley–Warning: the
quadratic polynomial `∑ᵢⱼ Aᵢⱼ Xᵢ Xⱼ` has total degree `≤ 2 < n`, so its number of zeros is divisible by
`char K = p`; the zero vector is a solution, so there are at least `p ≥ 2` solutions, hence a nonzero one.
This is the residue-field core of the local solvability [HM-p] at odd primes. -/
theorem finite_field_form_isotropic {K : Type*} [Field K] [Fintype K] {n : ℕ} (hn : 3 ≤ n)
    (A : Matrix (Fin n) (Fin n) K) : ∃ x : Fin n → K, x ≠ 0 ∧ x ⬝ᵥ A *ᵥ x = 0 := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : Fact p.Prime := Fact.mk (CharP.char_is_prime K p)
  set P : MvPolynomial (Fin n) K := ∑ i, ∑ j, C (A i j) * X i * X j with hP
  have hterm : ∀ i j : Fin n, (C (A i j) * X i * X j : MvPolynomial (Fin n) K).totalDegree ≤ 2 := by
    intro i j
    have e1 := totalDegree_mul (C (A i j) * X i) (X j : MvPolynomial (Fin n) K)
    have e2 := totalDegree_mul (C (A i j)) (X i : MvPolynomial (Fin n) K)
    have e3 : (C (A i j) : MvPolynomial (Fin n) K).totalDegree = 0 := totalDegree_C _
    have e4 : (X i : MvPolynomial (Fin n) K).totalDegree = 1 := totalDegree_X i
    have e5 : (X j : MvPolynomial (Fin n) K).totalDegree = 1 := totalDegree_X j
    omega
  have hP2 : P.totalDegree ≤ 2 := by
    rw [hP]
    apply (totalDegree_finset_sum _ _).trans
    apply Finset.sup_le; intro i _
    apply (totalDegree_finset_sum _ _).trans
    apply Finset.sup_le; intro j _
    exact hterm i j
  have hdeg : P.totalDegree < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  have heval : ∀ x : Fin n → K, eval x P = x ⬝ᵥ A *ᵥ x := by
    intro x
    rw [hP]
    simp only [map_sum, map_mul, eval_C, eval_X]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsol := char_dvd_card_solutions (K := K) (p := p) hdeg
  have h0 : eval (0 : Fin n → K) P = 0 := by rw [heval]; simp
  have hcard : 1 < Fintype.card {x : Fin n → K // eval x P = 0} := by
    have hpos : 0 < Fintype.card {x : Fin n → K // eval x P = 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
    have hple := Nat.le_of_dvd hpos hsol
    have h2 := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨⟨y, hy⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, h0⟩
  refine ⟨y, ?_, ?_⟩
  · intro hy0; exact hne (by subst hy0; rfl)
  · rw [← heval]; exact hy

end SKEFTHawking
