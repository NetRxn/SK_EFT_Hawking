import SKEFTHawking.QuantumNetwork.FidelityDataProcessing

/-!
# The fidelity block matrix and mixed-unitary transport (Phase 6AJ continuation, brick 4)

Toward general/mixed-unitary Uhlmann monotonicity via the Alberti block-PSD form
`F(ρ,σ) = max{ Re tr X : [[ρ, X],[Xᴴ, σ]] ⪰ 0 }`. This file ships the **channel-conjugation
transport** brick: the fidelity block of a mixed-unitary channel output
`Φ(·) = ∑ᵢ pᵢ Uᵢ · Uᵢᴴ` is a `pᵢ`-weighted sum of unitary conjugations of the input block, so
block-PSD feasibility transports from `(ρ,σ)` to `(Φρ,Φσ)` with the trace preserved. Combined with the
(continuation) Alberti characterization, this gives `F(Φρ,Φσ) ≥ F(ρ,σ)` for mixed-unitary channels.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **fidelity block** `[[ρ, X],[Xᴴ, σ]]` on the doubled index `ι ⊕ ι`. The Alberti SDP form
characterizes the root fidelity as the max of `Re tr X` over `X` making this block PSD. -/
noncomputable def fidelityBlock (ρ X σ : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks ρ X Xᴴ σ

/-- The block-diagonal dilation `U ⊕ U`. -/
noncomputable def diagDil (U : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks U 0 0 U

/-- Conjugating a fidelity block by the dilation `U ⊕ U` conjugates each entry by `U`:
`(U⊕U) · [[ρ,X],[Xᴴ,σ]] · (U⊕U)ᴴ = [[UρUᴴ, UXUᴴ],[(UXUᴴ)ᴴ, UσUᴴ]]`. -/
theorem diagDil_conj_fidelityBlock (U ρ X σ : Matrix ι ι ℂ) :
    diagDil U * fidelityBlock ρ X σ * (diagDil U)ᴴ
      = fidelityBlock (U * ρ * Uᴴ) (U * X * Uᴴ) (U * σ * Uᴴ) := by
  unfold diagDil fidelityBlock
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_assoc, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- The fidelity block is real-linear in its three arguments: a `pᵢ`-weighted sum of blocks is the
block of the `pᵢ`-weighted sums (the off-diagonal `Xᴴ` is conjugate-linear, but `pᵢ` is real). -/
theorem fidelityBlock_sum_smul {n : ℕ} (p : Fin n → ℝ) (A B C : Fin n → Matrix ι ι ℂ) :
    ∑ i, (p i : ℂ) • fidelityBlock (A i) (B i) (C i)
      = fidelityBlock (∑ i, (p i : ℂ) • A i) (∑ i, (p i : ℂ) • B i) (∑ i, (p i : ℂ) • C i) := by
  have hB : (∑ i, (p i : ℂ) • B i)ᴴ = ∑ i, (p i : ℂ) • (B i)ᴴ := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.conjTranspose_smul]; simp
  unfold fidelityBlock
  rw [hB]
  simp_rw [Matrix.fromBlocks_smul]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- **Mixed-unitary transport of the fidelity block.** For nonnegative weights `p` and unitaries `U`,
the fidelity block of the channel outputs `(∑ᵢ pᵢ Uᵢ ρ Uᵢᴴ, ∑ᵢ pᵢ Uᵢ X Uᵢᴴ, ∑ᵢ pᵢ Uᵢ σ Uᵢᴴ)` is the
`pᵢ`-weighted sum of unitary conjugations of the input block — hence PSD whenever the input block is.
This is the data-processing transport: a feasible Alberti witness `X` for `(ρ,σ)` yields a feasible
witness `∑ᵢ pᵢ Uᵢ X Uᵢᴴ` for `(Φρ,Φσ)`. -/
theorem fidelityBlock_mixedUnitary_posSemidef {n : ℕ} (p : Fin n → ℝ) (U : Fin n → Matrix ι ι ℂ)
    (ρ X σ : Matrix ι ι ℂ) (hp : ∀ i, 0 ≤ p i) (hblock : (fidelityBlock ρ X σ).PosSemidef) :
    (fidelityBlock (∑ i, (p i : ℂ) • (U i * ρ * (U i)ᴴ)) (∑ i, (p i : ℂ) • (U i * X * (U i)ᴴ))
        (∑ i, (p i : ℂ) • (U i * σ * (U i)ᴴ))).PosSemidef := by
  rw [← fidelityBlock_sum_smul]
  refine Matrix.posSemidef_sum _ fun i _ => ?_
  rw [← diagDil_conj_fidelityBlock]
  have hconj : (diagDil (U i) * fidelityBlock ρ X σ * (diagDil (U i))ᴴ).PosSemidef := by
    have h := hblock.conjTranspose_mul_mul_same (diagDil (U i))ᴴ
    rwa [Matrix.conjTranspose_conjTranspose] at h
  exact hconj.smul (by exact_mod_cast hp i)

/-- **Schur-complement characterization of the fidelity block (brick 1).** When `σ` is positive
*definite* (hence invertible), the fidelity block `[[ρ, X],[Xᴴ, σ]]` is PSD iff the Schur complement
`ρ − X σ⁻¹ Xᴴ` is PSD. This is the entry point for the forward Alberti bound: it exhibits the feasible
`X` as `X = √ρ · K · √σ` with `‖K‖ ≤ 1` (the contraction `K = ρ^{-1/2} X σ^{-1/2}` satisfies
`KKᴴ = ρ^{-1/2}(X σ⁻¹ Xᴴ)ρ^{-1/2} ⪯ 1` exactly when the Schur complement is PSD). -/
theorem fidelityBlock_posDef_schur {ρ X σ : Matrix ι ι ℂ} (hσ : σ.PosDef) :
    (fidelityBlock ρ X σ).PosSemidef ↔ (ρ - X * σ⁻¹ * Xᴴ).PosSemidef := by
  letI : Invertible σ := hσ.isUnit.invertible
  exact Matrix.PosDef.fromBlocks₂₂ ρ X hσ

end SKEFTHawking.QuantumNetwork
