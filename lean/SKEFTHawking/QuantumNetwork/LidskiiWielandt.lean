import SKEFTHawking.QuantumNetwork.SpectralMajorization

/-!
# Toward Lidskii–Wielandt (Phase 6AL, Wave 4, item F1b)

The remaining brick for Mirsky's inequality is the Lidskii–Wielandt sorted-difference majorization. Its
operator core is the **doubly-stochastic eigenvalue relation**: the diagonal of a Hermitian `B` conjugated
into another orthonormal eigenbasis `U` is a doubly-stochastic combination of `B`'s eigenvalues. This file
builds that relation (`diag_conj_eq_sum_normSq`); with `A = B + (A−B)` it expresses `λ(A)` as
doubly-stochastic combinations of `λ(B)` and `λ(A−B)`, which (Birkhoff) yields the majorization.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Doubly-stochastic eigenvalue expansion:** the `i`-th diagonal entry of a Hermitian `B` conjugated
into a unitary basis `U` is `∑ⱼ |Mᵢⱼ|² λⱼ(B)` with `M = Uᴴ · U_B` (the eigenbasis overlap). -/
theorem diag_conj_eq_sum_normSq (U : ↥(unitary (Matrix ι ι ℂ))) {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (i : ι) :
    (star (↑U : Matrix ι ι ℂ) * B * (↑U : Matrix ι ι ℂ)) i i
      = ((∑ j, Complex.normSq
          ((star (↑U : Matrix ι ι ℂ) * (↑hB.eigenvectorUnitary : Matrix ι ι ℂ)) i j)
          * hB.eigenvalues j : ℝ) : ℂ) := by
  set u : Matrix ι ι ℂ := (↑U : Matrix ι ι ℂ) with hu
  set Ub : Matrix ι ι ℂ := (↑hB.eigenvectorUnitary : Matrix ι ι ℂ) with hUb
  set M : Matrix ι ι ℂ := star u * Ub with hM
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) with hD
  have hstarM : star M = star Ub * u := by rw [hM, Matrix.star_mul, star_star]
  have hBd : star u * B * u = M * D * star M := by
    rw [hstarM, hM]
    conv_lhs => rw [hB.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [hD, hUb]
    noncomm_ring
  rw [hBd, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_eq_single j]
  · rw [hD, Matrix.diagonal_apply_eq, Matrix.star_apply, Function.comp_apply,
      show star (M i j) = (starRingEnd ℂ) (M i j) from rfl,
      Complex.ofReal_mul, ← Complex.mul_conj, RCLike.ofReal_eq_complex_ofReal]
    ring
  · intro k _ hk; rw [hD, Matrix.diagonal_apply_ne _ hk, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

end SKEFTHawking.QuantumNetwork
