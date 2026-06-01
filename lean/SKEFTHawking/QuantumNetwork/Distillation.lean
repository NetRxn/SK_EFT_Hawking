import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.Basic

/-!
# Entanglement distillation: BBPSSW recurrence (Phase 6AA, Wave 3)

The BBPSSW purification recurrence for two identical Werner copies of overlap
fidelity `F`, in the fidelity-parameter representation (D3):

`F'(F) = (F² + (1−F)²/9) / (F² + 2F(1−F)/3 + 5(1−F)²/9)`

(Dür–Briegel review, Rep. Prog. Phys. 70, 1381 (2007), Eq. (18); transcribed in
the Phase-6AA exact-formulas DR §2(a).)

**Flagship result:** the entire distillability statement reduces to a single
cubic polynomial inequality `(1−F)(2F−1)(4F−1) > 0`, closed by `nlinarith`.

Invariants (Phase 6AA): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- BBPSSW success probability (the recurrence denominator). -/
noncomputable def bbpsswSuccessProb (F : ℝ) : ℝ :=
  F ^ 2 + 2 * F * (1 - F) / 3 + 5 * (1 - F) ^ 2 / 9

/-- BBPSSW output fidelity after one purification round on two Werner copies. -/
noncomputable def bbpsswRecurrence (F : ℝ) : ℝ :=
  (F ^ 2 + (1 - F) ^ 2 / 9) / bbpsswSuccessProb F

/-- The success probability is strictly positive for every `F`
(`= (8F² − 4F + 5)/9`, a positive-definite quadratic). -/
theorem bbpsswSuccessProb_pos (F : ℝ) : 0 < bbpsswSuccessProb F := by
  unfold bbpsswSuccessProb
  nlinarith [sq_nonneg (4 * F - 1), sq_nonneg F, sq_nonneg (1 - F)]

/-- **Flagship — BBPSSW distillability.** On the convergence basin `F ∈ (1/2, 1)`
the purified fidelity strictly increases. The whole proof reduces to the cubic
`(1−F)(2F−1)(4F−1) > 0` (since `9·(num − F·denom) = (1−F)(2F−1)(4F−1)`). -/
theorem bbpsswRecurrence_gt (F : ℝ) (h1 : 1 / 2 < F) (h2 : F < 1) :
    F < bbpsswRecurrence F := by
  have hd : 0 < bbpsswSuccessProb F := bbpsswSuccessProb_pos F
  have hcubic : 0 < (1 - F) * (2 * F - 1) * (4 * F - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  unfold bbpsswRecurrence bbpsswSuccessProb at *
  rw [lt_div_iff₀ hd]
  nlinarith [hcubic]

/-! ## DEJMPS recurrence (Pauli-error convention)

In the Pauli-error Bell-basis labeling `(A,B,C,D) ↔ (λ_{00},λ_{01},λ_{10},λ_{11})`,
the DEJMPS output (Dür–Briegel review Eq. (19); exact-formulas DR §2(b)) is

`A' = (A² + D²) / N`,  `N = (A+D)² + (B+C)²`.

**Key (corrected) pairing:** the squared-and-added pair is the *diagonal*
`(00,11)=(I,Y)` pair — i.e. `A² + D²`, NOT the naive adjacent `A² + B²`. -/

/-- DEJMPS normalizer / success probability `N = (A+D)² + (B+C)²`. -/
noncomputable def dejmpsNorm (A B C D : ℝ) : ℝ := (A + D) ^ 2 + (B + C) ^ 2

/-- DEJMPS output target-fidelity component `A' = (A²+D²)/N` (diagonal pairing). -/
noncomputable def dejmpsOutA (A B C D : ℝ) : ℝ := (A ^ 2 + D ^ 2) / dejmpsNorm A B C D

/-- **DEJMPS fidelity increase on the Werner restriction.** For a Werner input
`(F, (1−F)/3, (1−F)/3, (1−F)/3)` with `F ∈ (1/2,1)`, DEJMPS strictly increases the
target-fidelity component — and, as for BBPSSW, the whole statement collapses to
the cubic `(1−F)(2F−1)(4F−1) > 0`. (General-Bell-diagonal convergence is
Macchiavello 1998, analytic, deferred.) -/
theorem dejmps_werner_fidelity_increase (F : ℝ) (h1 : 1 / 2 < F) (h2 : F < 1) :
    F < dejmpsOutA F ((1 - F) / 3) ((1 - F) / 3) ((1 - F) / 3) := by
  have hpos : 0 < F + (1 - F) / 3 := by linarith
  have hN : 0 < dejmpsNorm F ((1 - F) / 3) ((1 - F) / 3) ((1 - F) / 3) := by
    unfold dejmpsNorm
    nlinarith [mul_pos hpos hpos, sq_nonneg ((1 - F) / 3 + (1 - F) / 3)]
  have hcubic : 0 < (1 - F) * (2 * F - 1) * (4 * F - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  unfold dejmpsOutA dejmpsNorm at *
  rw [lt_div_iff₀ hN]
  nlinarith [hcubic]

end SKEFTHawking.QuantumNetwork
