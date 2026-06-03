import SKEFTHawking.QuantumNetwork.FidelityForwardBound
import SKEFTHawking.QuantumNetwork.CPTPChannel

/-!
# General-CPTP fidelity data processing (Phase 6AJ — general Kraus generalization)

Lifts the mixed-unitary Uhlmann monotonicity (`sqrtFidelity_mixedUnitary_ge`) to an **arbitrary
trace-preserving Kraus channel** `Φ(·) = ∑ₖ Kₖ · Kₖᴴ` with `∑ₖ Kₖᴴ Kₖ = 1`. The mixed-unitary
proof generalizes directly: the block-transport `diagDil_conj_fidelityBlock` already holds for an
*arbitrary* matrix (not just a unitary), so conjugating the Alberti block `[[ρ,X],[Xᴴ,σ]]` by each
`Kₖ ⊕ Kₖ` and summing transports block-PSD feasibility from `(ρ,σ)` to `(Φρ,Φσ)`; the trace is
preserved by `∑ₖ Kₖᴴ Kₖ = 1` (`trace_krausMap`) instead of `∑ᵢ pᵢ = 1`. **No Stinespring, no Choi
dilation, no Lieb concavity.**

The forward Alberti bound (`re_trace_block_le_sqrtFidelity`) is proved via the Schur complement and
so requires the *output* states `Φρ, Φσ` to be positive **definite**. A general trace-preserving
channel may send a full-rank state to a rank-deficient one (e.g. the reset channel
`Kₖ = |0⟩⟨k|`), so the fully general statement carries the output-positive-definiteness as an explicit
hypothesis; it is discharged automatically for the broad class of channels whose "unital part"
`∑ₖ Kₖ Kₖᴴ` is positive definite (`posDef_krausMap_of_sumKrausKrausH_posDef`), which subsumes the
mixed-unitary case (`∑ᵢ pᵢ Uᵢ Uᵢᴴ = 1`).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The fidelity block is additive: a finite sum of fidelity blocks is the fidelity block of the
finite sums (the off-diagonal `Xᴴ` is conjugate-linear, but a plain sum commutes with `ᴴ`). -/
theorem fidelityBlock_sum (A B C : Fin m → Matrix ι ι ℂ) :
    ∑ k, fidelityBlock (A k) (B k) (C k)
      = fidelityBlock (∑ k, A k) (∑ k, B k) (∑ k, C k) := by
  unfold fidelityBlock
  rw [Matrix.conjTranspose_sum]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

omit [Nonempty ι] in
/-- **General-Kraus transport of the fidelity block.** For any Kraus operators `Kₖ`, the fidelity
block of the channel outputs `(Φρ, ΦX, Φσ)` is the sum of `(Kₖ⊕Kₖ)`-conjugations of the input block
`[[ρ,X],[Xᴴ,σ]]` — hence PSD whenever the input block is. A feasible Alberti witness `X` for `(ρ,σ)`
thus yields a feasible witness `Φ(X) = ∑ₖ Kₖ X Kₖᴴ` for `(Φρ, Φσ)`. -/
theorem fidelityBlock_krausMap_posSemidef (K : Fin m → Matrix ι ι ℂ) (ρ X σ : Matrix ι ι ℂ)
    (hblock : (fidelityBlock ρ X σ).PosSemidef) :
    (fidelityBlock (krausMap K ρ) (krausMap K X) (krausMap K σ)).PosSemidef := by
  unfold krausMap
  rw [← fidelityBlock_sum]
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  rw [← diagDil_conj_fidelityBlock]
  have h := hblock.conjTranspose_mul_mul_same (diagDil (K k))ᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- **General-CPTP Uhlmann monotonicity (data processing for fidelity).** For an arbitrary
trace-preserving Kraus channel `Φ(·) = ∑ₖ Kₖ · Kₖᴴ` (`∑ₖ Kₖᴴ Kₖ = 1`) and positive-definite inputs
`ρ, σ` whose outputs `Φρ, Φσ` are again positive definite,
`F(Φρ, Φσ) ≥ F(ρ, σ)`. The optimal Alberti witness `X*` for `(ρ,σ)` (attainment) transports to a
feasible witness `Φ(X*)` for `(Φρ,Φσ)` with the same trace (trace preservation); the forward Alberti
bound at `(Φρ,Φσ)` then gives `F(Φρ,Φσ) ≥ Re tr Φ(X*) = Re tr X* = F(ρ,σ)`. -/
theorem sqrtFidelity_krausMap_ge {K : Fin m → Matrix ι ι ℂ} {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hK : IsKrausChannel K)
    (hΦρ : (krausMap K ρ).PosDef) (hΦσ : (krausMap K σ).PosDef) :
    sqrtFidelity hρ.posSemidef hσ.posSemidef
      ≤ sqrtFidelity hΦρ.posSemidef hΦσ.posSemidef := by
  obtain ⟨X, hXblock, hXtr⟩ := exists_block_re_trace_eq_sqrtFidelity hρ hσ
  have hΦblock := fidelityBlock_krausMap_posSemidef K ρ X σ hXblock
  have hbound := re_trace_block_le_sqrtFidelity hΦρ hΦσ hΦblock
  rwa [show (krausMap K X).trace.re = X.trace.re from by rw [trace_krausMap hK], hXtr] at hbound

end SKEFTHawking.QuantumNetwork
