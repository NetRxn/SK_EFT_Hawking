import SKEFTHawking.QuantumNetwork.DiamondNormSup
import SKEFTHawking.QuantumNetwork.DiamondNorm

/-!
# Diamond norm: the Choi / maximally-entangled primal bound (Phase 6AF-9)

The Watrous SDP characterization of the diamond norm pairs a primal program (a maximization over
input states of the stabilized output distinguishability) with a dual program over the Choi
matrix. The full primal=dual identity needs conic strong duality (a `ProperCone`/`PointedCone`
convex-duality substrate absent at pin) — see the deferred-frontier note in `DiamondNorm.lean`.

This file delivers the **primal (one-sided) bound**: a concrete feasible point of the primal
program — the **maximally-entangled (Choi) state** `Ω = (1/n)|Ω⟩⟨Ω|` — gives a computable lower
bound on the diamond distance,

  `diamondDist Φ₁ Φ₂ ≥ D((Φ₁⊗id)Ω, (Φ₂⊗id)Ω)`,

via the least-upper-bound property `le_diamondDist`. The maximally-entangled state is the
canonical primal point of the Watrous program (it is the state whose stabilized output is the
normalized Choi matrix), so this is the primal-feasibility half of the Choi-SDP characterization.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {m n : ℕ}

/-- The unnormalized maximally-entangled vector `|Ω⟩ = ∑ᵢ |i,i⟩` as a column matrix on the
doubled index `Fin n × Fin n`: `omegaVec (i,j) = ⟦i = j⟧`. -/
noncomputable def omegaVec (n : ℕ) : Matrix (Fin n × Fin n) (Fin 1) ℂ :=
  fun p _ => if p.1 = p.2 then 1 else 0

/-- The **maximally-entangled (Choi) state** `Ω = (1/n)|Ω⟩⟨Ω|` on `Fin n × Fin n`. -/
noncomputable def maxEntangled (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ((n : ℂ))⁻¹ • (omegaVec n * (omegaVec n)ᴴ)

/-- **The maximally-entangled state is a density operator** (`n ≥ 1`): it is `(1/n)` times the
rank-one PSD outer product `|Ω⟩⟨Ω|`, and `tr|Ω⟩⟨Ω| = n`. -/
theorem isDensityOperator_maxEntangled [NeZero n] :
    IsDensityOperator (maxEntangled n) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hpos : (0 : ℂ) ≤ ((n : ℂ))⁻¹ := by
    rw [show ((n : ℂ))⁻¹ = (((n : ℝ))⁻¹ : ℝ) by push_cast; ring, Complex.zero_le_real]
    positivity
  refine ⟨?_, ?_⟩
  · exact (Matrix.posSemidef_self_mul_conjTranspose _).smul hpos
  · rw [maxEntangled, Matrix.trace_smul, smul_eq_mul]
    have htr : (omegaVec n * (omegaVec n)ᴴ).trace = (n : ℂ) := by
      rw [Matrix.trace_mul_comm, Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, omegaVec,
        Finset.univ_unique, Finset.sum_singleton]
      have hterm : ∀ p : Fin n × Fin n,
          star (if p.1 = p.2 then (1:ℂ) else 0) * (if p.1 = p.2 then 1 else 0)
            = if p.1 = p.2 then (1:ℂ) else 0 := fun p => by split <;> simp
      simp_rw [hterm]
      rw [Fintype.sum_prod_type]
      simp [Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ]
    rw [htr, inv_mul_cancel₀ hn]

/-- **Choi / maximally-entangled primal bound** — the diamond distance is bounded below by the
distinguishability of the channels on the maximally-entangled (Choi) input state. A concrete
feasible point of the Watrous primal program, hence the primal (one-sided) half of the Choi-SDP
characterization, with no SDP duality required. -/
theorem diamondDist_ge_maxEntangled [NeZero n]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    traceDist (krausMap (tensorKraus K₁) (maxEntangled n))
        (krausMap (tensorKraus K₂) (maxEntangled n))
      ≤ diamondDist K₁ K₂ :=
  le_diamondDist hK₁ hK₂ isDensityOperator_maxEntangled

end SKEFTHawking.QuantumNetwork
