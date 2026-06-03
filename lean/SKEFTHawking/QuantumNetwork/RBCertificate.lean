import SKEFTHawking.QuantumNetwork.GateFidelity
import SKEFTHawking.QuantumNetwork.GateFidelityBridge
import SKEFTHawking.QuantumNetwork.DiamondNormChoi

/-!
# RB-fidelity → entanglement-fidelity → diamond certificate (Phase 6AH, Wave 6AH.1)

The bench-data→worst-case bridge as a single object: a measured average gate fidelity
`F_avg` (e.g. from randomized benchmarking) certifies a worst-case diamond distance to the ideal
channel. This file builds the Choi/maximally-entangled connection that ties the Kraus-trace
entanglement fidelity `F_e = (1/d²)∑ₖ|tr Kₖ|²` (`entanglementFidelity`, Phase 6AG) to the
input–output overlap of the channel on the maximally-entangled state, which the
Fuchs–van de Graaf↔diamond bridge (`GateFidelityBridge.lean`) then converts to a diamond bound.

Foundational identity (the "ricochet" / transpose trick): for the unnormalised maximally-entangled
vector `|Ω⟩ = ∑ᵢ|i,i⟩`,
`⟨Ω|(A ⊗ 1)|Ω⟩ = tr A`.
Contracting `(K⊗id)Ω` against `⟨Ω|·|Ω⟩` then yields `⟨Ω|(K⊗id)Ω|Ω⟩ = n⁻¹·∑ₖ tr Kₖ · tr Kₖᴴ`,
i.e. `= n · F_e` after the `|tr Kₖ|²` identification — the channel–state-duality form of `F_e`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Complex Matrix
open scoped Kronecker

variable {m n : ℕ}

/-- **Conjugate transpose of a `A ⊗ 1` Kronecker block.** `(A ⊗ 1)ᴴ = Aᴴ ⊗ 1`. -/
theorem kron_one_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) :
    (A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = Aᴴ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    apply_ite star, eq_comm]

/-- **Ricochet identity** `⟨Ω|(A ⊗ 1)|Ω⟩ = tr A`, as the `1×1` matrix `(tr A)·1`. The
maximally-entangled vector `|Ω⟩ = ∑ᵢ|i,i⟩` "ricochets" `A ⊗ 1` into a trace. -/
theorem omega_ricochet (A : Matrix (Fin n) (Fin n) ℂ) :
    (omegaVec n)ᴴ * (A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * omegaVec n
      = A.trace • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  fin_cases a; fin_cases b
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply,
    Matrix.conjTranspose_apply, omegaVec, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.trace,
    Matrix.diag_apply, Fintype.sum_prod_type, apply_ite star, star_one, star_zero, mul_ite, mul_one,
    mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- **Channel–state-duality form of the unnormalised overlap.** For a Kraus tuple `K`, contracting
`(K⊗id)` applied to the maximally-entangled state against `⟨Ω|·|Ω⟩` gives
`⟨Ω|(K⊗id)Ω|Ω⟩ = n⁻¹·∑ₖ tr Kₖ · tr Kₖᴴ` (a `1×1` matrix). -/
theorem omega_overlap_krausMap (K : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    (omegaVec n)ᴴ * krausMap (tensorKraus K) (maxEntangled n) * omegaVec n
      = ((n : ℂ)⁻¹ * ∑ k, (K k).trace * ((K k)ᴴ).trace) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  unfold krausMap tensorKraus maxEntangled
  rw [Matrix.mul_sum, Matrix.sum_mul]
  conv_rhs => rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : (omegaVec n)ᴴ * (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)
        * ((n : ℂ)⁻¹ • (omegaVec n * (omegaVec n)ᴴ)) * (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ)
        * omegaVec n
      = (n : ℂ)⁻¹ • (((omegaVec n)ᴴ * (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * omegaVec n)
        * ((omegaVec n)ᴴ * (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * omegaVec n)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [e1, kron_one_conjTranspose, omega_ricochet (K k), omega_ricochet ((K k)ᴴ),
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, smul_smul, mul_assoc]

/-- The unnormalised overlap as a scalar: `(⟨Ω|(K⊗id)Ω|Ω⟩)₀₀ = n⁻¹·∑ₖ tr Kₖ · conj(tr Kₖ)
= n · F_e` (the `↑(entanglementFidelity)` identification is done in the assembly wave). -/
theorem omega_overlap_scalar (K : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    ((omegaVec n)ᴴ * krausMap (tensorKraus K) (maxEntangled n) * omegaVec n) 0 0
      = (n : ℂ)⁻¹ * ∑ k, ((Complex.normSq ((K k).trace) : ℝ) : ℂ) := by
  rw [omega_overlap_krausMap]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.trace_conjTranspose]
  exact Complex.mul_conj _

end SKEFTHawking.QuantumNetwork
