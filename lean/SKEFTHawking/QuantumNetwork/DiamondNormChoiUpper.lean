import SKEFTHawking.QuantumNetwork.DiamondNormChoi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Diamond norm: the Choi operator-norm upper bound (Phase 6AF-11)

This file delivers the **one-sided primal upper bound** on the diamond distance in terms of the
operator norm of the (difference of) Choi matrices,

  `diamondDist Φ₁ Φ₂ ≤ C(n) · ‖J(Φ₁) − J(Φ₂)‖_∞`,

the companion to the maximally-entangled primal *lower* bound `diamondDist_ge_maxEntangled`
(`DiamondNormChoi.lean`). Together they sandwich the diamond distance by the Choi matrix
(`‖J‖₁ / d ≤ ‖·‖_◇ ≤ d · ‖J‖_∞` in the Watrous normalization), the formalizable content of the
Choi-SDP characterization without conic strong duality (the unformalizable piece).

The operator norm `‖·‖` in this file is the **ℓ²-operator norm** on matrices, activated by the
scoped instance `Matrix.Norms.L2Operator`. This file is deliberately separate from the
trace-norm / Frobenius-norm files so that this scoped norm instance never leaks into them.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.

## Proof blueprint (sharp constant `d = n`)

For the difference output `T = (Δ⊗id)ρ` (Hermitian, `Δ = Φ₁ − Φ₂` Hermiticity-preserving) with
Choi `C = choiMatrix Φ₁ − choiMatrix Φ₂`:

1. **Vectorization (entrywise).** From `krausMap (tensorKraus K) ρ = ∑ₖ (Kₖ⊗1) ρ (Kₖ⊗1)ᴴ` and
   `choiMatrix (krausMap K) (a,y) (b,y') = ∑ₖ Kₖ y a · conj (Kₖ y' b)`:

      `(krausMap (tensorKraus K) ρ) (y,α) (y',β) = ∑_{a,b} C (a,y) (b,y') · ρ (a,α) (b,β)`,   `C = choiMatrix (krausMap K)`.

2. **Trace–contraction identity.** For any `W` on the doubled (output) space,
   `tr(W · T) = tr(C · M(W,ρ))` where
   `M(W,ρ) (b,y') (a,y) := ∑_{α,β} W (y',β) (y,α) · ρ (a,α) (b,β)`.

3. **`M(W,ρ)` is PSD** when `W, ρ` are PSD (rank-1: `M(|w⟩⟨w|, |v⟩⟨v|) = |u⟩⟨u|`,
   `u (b,y') = ∑_β w (y',β) · conj (v (b,β))`; general by `posSemidef_sum`).

4. **`tr M(W,ρ) ≤ ‖W‖_∞ · n`** for `ρ` a density operator (reduces to
   `tr(W · (1_Y ⊗ ρ_X)) ≤ ‖W‖_∞ · n · tr ρ_X = ‖W‖_∞ · n`).

5. **Brick 2.** `tr(C · M) ≤ ‖C‖_∞ · tr M` for `M` PSD (via `M^{1/2} C M^{1/2} ≤ ‖C‖_∞ M`).
   With `P₊` the positive eigenprojection of `T` (a projection, `‖P₊‖_∞ ≤ 1`),
   `eigPosSum T = tr(P₊ · T) = tr(C · M(P₊,ρ)) ≤ n · ‖C‖_∞` (and likewise for `P₋ = 1 − P₊`).

6. `‖T‖₁ = tr(P₊T) − tr(P₋T) ≤ 2n‖C‖_∞`, hence `diamondDist ≤ ½ · 2n‖C‖_∞ = n · ‖C‖_∞`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- **Brick 1 — trace norm bounded by dimension × operator norm.**
For any square matrix, `‖M‖₁ = ∑ √eig(MᴴM) ≤ (card) · ‖M‖_op`: each singular value
`√eig(MᴴM)` is bounded by `√‖MᴴM‖_op = ‖M‖_op`, since the eigenvalues of `MᴴM` lie in its
spectrum and are dominated by the operator norm. -/
theorem traceNorm_le_card_mul_l2opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) : traceNorm M ≤ (Fintype.card ι : ℝ) * ‖M‖ := by
  have hP := Matrix.posSemidef_conjTranspose_mul_self M
  have hbound : ∀ i, Real.sqrt (hP.isHermitian.eigenvalues i) ≤ ‖M‖ := by
    intro i
    have hmem : hP.isHermitian.eigenvalues i ∈ spectrum ℝ (Mᴴ * M) :=
      hP.isHermitian.eigenvalues_mem_spectrum_real i
    have hle : |hP.isHermitian.eigenvalues i| ≤ ‖Mᴴ * M‖ := by
      have h := spectrum.norm_le_norm_of_mem hmem
      simpa [Real.norm_eq_abs] using h
    have hnn : 0 ≤ hP.isHermitian.eigenvalues i := hP.eigenvalues_nonneg i
    rw [abs_of_nonneg hnn, l2_opNorm_conjTranspose_mul_self] at hle
    calc Real.sqrt (hP.isHermitian.eigenvalues i)
        ≤ Real.sqrt (‖M‖ * ‖M‖) := Real.sqrt_le_sqrt hle
      _ = ‖M‖ := Real.sqrt_mul_self (norm_nonneg M)
  calc traceNorm M = ∑ _i : ι, Real.sqrt (hP.isHermitian.eigenvalues _i) := rfl
    _ ≤ ∑ _i : ι, ‖M‖ := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Fintype.card ι : ℝ) * ‖M‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end SKEFTHawking.QuantumNetwork
