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
open scoped Kronecker ComplexOrder

/-! ## Rank-one trace norm `‖u vᴴ‖₁ = ‖u‖·‖v‖`

The trace norm of a rank-one matrix `u vᴴ` (columns `u, v`) is the product of the column norms. The
absolute value `|u vᴴ| = (‖u‖/‖v‖)·(v vᴴ)` (PSD-square uniqueness), and its trace is `‖u‖·‖v‖`.
Used to evaluate `sqrtFidelity` against a pure state below. -/

section RankOne
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `1×1` self-inner product `(uᴴ u)₀₀ = ∑ₖ |uₖ|²` (a nonnegative real). -/
theorem self_inner_eq (u : Matrix ι (Fin 1) ℂ) :
    (uᴴ * u) 0 0 = ((∑ k, Complex.normSq (u k 0) : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]; push_cast
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.conjTranspose_apply, mul_comm]; exact Complex.mul_conj (u k 0)

theorem self_inner_nonneg (u : Matrix ι (Fin 1) ℂ) : (0 : ℝ) ≤ ((uᴴ * u) 0 0).re := by
  rw [self_inner_eq, Complex.ofReal_re]; exact Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _

theorem self_inner_re (u : Matrix ι (Fin 1) ℂ) : (uᴴ * u) 0 0 = (((uᴴ * u) 0 0).re : ℂ) := by
  rw [self_inner_eq, Complex.ofReal_re]

/-- If `(vᴴ v)₀₀ = 0` then `v = 0`, so `u vᴴ = 0`. -/
theorem cross_zero (u v : Matrix ι (Fin 1) ℂ) (h : ((vᴴ * v) 0 0).re = 0) : u * vᴴ = 0 := by
  rw [self_inner_eq, Complex.ofReal_re] at h
  have hz : ∀ k, v k 0 = 0 := fun k => Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).mp h k (Finset.mem_univ k))
  ext p q; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hz]

theorem outer_sq (v : Matrix ι (Fin 1) ℂ) :
    (v * vᴴ) * (v * vᴴ) = ((vᴴ * v) 0 0) • (v * vᴴ) := by
  conv_lhs => rw [show v * vᴴ * (v * vᴴ) = v * (vᴴ * v) * vᴴ by simp only [Matrix.mul_assoc],
    show vᴴ * v = ((vᴴ * v) 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℂ) by
      ext a b; fin_cases a; fin_cases b; simp,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

theorem cross_sq (u v : Matrix ι (Fin 1) ℂ) :
    (u * vᴴ)ᴴ * (u * vᴴ) = ((uᴴ * u) 0 0) • (v * vᴴ) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  conv_lhs => rw [show v * uᴴ * (u * vᴴ) = v * (uᴴ * u) * vᴴ by simp only [Matrix.mul_assoc],
    show uᴴ * u = ((uᴴ * u) 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℂ) by
      ext a b; fin_cases a; fin_cases b; simp,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-- **Rank-one trace norm** `‖u vᴴ‖₁ = √((uᴴu)₀₀.re)·√((vᴴv)₀₀.re)` (the product of column norms). -/
theorem traceNorm_outer (u v : Matrix ι (Fin 1) ℂ) :
    traceNorm (u * vᴴ) = Real.sqrt (((uᴴ * u) 0 0).re) * Real.sqrt (((vᴴ * v) 0 0).re) := by
  have hun := self_inner_nonneg u
  have hvn := self_inner_nonneg v
  have hu : (uᴴ * u) 0 0 = (((uᴴ * u) 0 0).re : ℂ) := self_inner_re u
  have hv : (vᴴ * v) 0 0 = (((vᴴ * v) 0 0).re : ℂ) := self_inner_re v
  by_cases hb : ((vᴴ * v) 0 0).re = 0
  · rw [cross_zero u v hb, traceNorm_posSemidef Matrix.PosSemidef.zero, Matrix.trace_zero,
      Complex.zero_re, hb, Real.sqrt_zero, mul_zero]
  · set a := Real.sqrt (((uᴴ * u) 0 0).re)
    set b := Real.sqrt (((vᴴ * v) 0 0).re)
    have haa : a * a = ((uᴴ * u) 0 0).re := Real.mul_self_sqrt hun
    have hbb : b * b = ((vᴴ * v) 0 0).re := Real.mul_self_sqrt hvn
    have hbpos : 0 < b := Real.sqrt_pos.mpr (lt_of_le_of_ne hvn (Ne.symm hb))
    have hc : (0 : ℂ) ≤ ((a / b : ℝ) : ℂ) := by
      rw [Complex.le_def, Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), rfl⟩
    have habs : absOp (u * vᴴ) = ((a / b : ℝ) : ℂ) • (v * vᴴ) := by
      refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _)
        ((Matrix.posSemidef_self_mul_conjTranspose v).smul hc) ?_
      rw [absOp_mul_self, cross_sq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, outer_sq,
        smul_smul, hu, hv]
      congr 1
      rw [← haa, ← hbb]; push_cast; field_simp
    rw [traceNorm_eq_trace_absOp, habs, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
      Matrix.trace_fin_one, hv, ← Complex.ofReal_mul, Complex.ofReal_re, ← hbb]
    field_simp

end RankOne

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
