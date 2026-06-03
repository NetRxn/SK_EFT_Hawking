import SKEFTHawking.QuantumNetwork.GateFidelity
import SKEFTHawking.QuantumNetwork.GateFidelityBridge
import SKEFTHawking.QuantumNetwork.DiamondNormChoi
import SKEFTHawking.QuantumNetwork.NamedChannelDiamondExact

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

/-! ## Fidelity against the maximally-entangled (pure) state -/

/-- `⟨Ω|Ω⟩ = n` (the `n` diagonal terms of `∑_p ⟦p.1=p.2⟧`). -/
theorem omega_norm (n : ℕ) : ((omegaVec n)ᴴ * omegaVec n) 0 0 = (n : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, omegaVec, Fintype.sum_prod_type,
    apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

/-- The maximally-entangled state is a projector: `Ω² = Ω`. -/
theorem maxEntangled_projector (n : ℕ) [NeZero n] :
    maxEntangled n * maxEntangled n = maxEntangled n := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [maxEntangled, Matrix.smul_mul, Matrix.mul_smul, smul_smul, outer_sq, omega_norm, smul_smul]
  congr 1; field_simp

/-- `√Ω = Ω` (the square root of a projector is itself). -/
theorem psdSqrt_maxEntangled (n : ℕ) [NeZero n] :
    psdSqrt (isDensityOperator_maxEntangled (n := n)).1 = maxEntangled n := by
  refine posSemidef_eq_of_mul_self_eq (psdSqrt_posSemidef _) (isDensityOperator_maxEntangled).1 ?_
  rw [psdSqrt_mul_self, maxEntangled_projector]

/-- **Fidelity against the maximally-entangled pure state.** For any density operator `ρ`,
`√F(ρ, Ω) = √(1/n)·√(⟨Ω|ρ|Ω⟩)` — fidelity at a pure target is the overlap, evaluated via the rank-one
trace norm `‖Ω·√ρ‖₁ = ‖(1/n)·Ω⟩‖·‖√ρ·Ω⟩‖`. -/
theorem sqrtFidelity_maxEntangled {n : ℕ} [NeZero n]
    {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hρ : ρ.PosSemidef) :
    sqrtFidelity hρ (isDensityOperator_maxEntangled).1
      = Real.sqrt (1 / n) * Real.sqrt (((omegaVec n)ᴴ * ρ * omegaVec n) 0 0).re := by
  rw [sqrtFidelity, psdSqrt_maxEntangled]
  have huv : maxEntangled n * psdSqrt hρ
      = ((n : ℂ)⁻¹ • omegaVec n) * (psdSqrt hρ * omegaVec n)ᴴ := by
    rw [maxEntangled, Matrix.conjTranspose_mul, (psdSqrt_isHermitian hρ).eq, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_assoc]
  rw [huv, traceNorm_outer]
  congr 1
  · congr 1
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_apply,
      smul_eq_mul, omega_norm]
    rw [show star ((n : ℂ)⁻¹) * (n : ℂ)⁻¹ * (n : ℂ) = ((1 / n : ℝ) : ℂ) by
      rw [Complex.star_def, Complex.conj_inv, Complex.conj_natCast]; push_cast; field_simp]
    rw [Complex.ofReal_re]
  · congr 2
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian hρ).eq,
      show (omegaVec n)ᴴ * psdSqrt hρ * (psdSqrt hρ * omegaVec n)
          = (omegaVec n)ᴴ * (psdSqrt hρ * psdSqrt hρ) * omegaVec n by simp only [Matrix.mul_assoc],
      psdSqrt_mul_self]

/-- **The output–maximally-entangled root fidelity is `√F_e`.** For a CPTP channel `Φ` with Kraus
operators `K`, `√F((Φ⊗id)Ω, Ω) = √(F_e(Φ))` — the entanglement fidelity is the Choi-state overlap. -/
theorem sqrtFidelity_output_eq {K : Fin m → Matrix (Fin n) (Fin n) ℂ} [NeZero n]
    (hK : IsKrausChannel K) :
    sqrtFidelity (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK)
        isDensityOperator_maxEntangled).1 isDensityOperator_maxEntangled.1
      = Real.sqrt (entanglementFidelity K) := by
  rw [sqrtFidelity_maxEntangled, omega_overlap_scalar, entanglementFidelity]
  have hre : (((n : ℂ)⁻¹ * ∑ k, ((Complex.normSq ((K k).trace) : ℝ) : ℂ))).re
      = (n : ℝ)⁻¹ * ∑ k, Complex.normSq ((K k).trace) := by
    rw [← Complex.ofReal_sum, show ((n : ℂ)⁻¹) = (((n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-! ## The bench-data → worst-case certificate -/

/-- The identity channel `idKrausPad` tensored with `id` fixes the maximally-entangled state. -/
theorem krausMap_tensorKraus_idKrausPad (j n : ℕ)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    krausMap (tensorKraus (idKrausPad j n)) ρ = ρ := by
  unfold krausMap tensorKraus idKrausPad
  rw [Finset.sum_eq_single (0 : Fin (j + 1)) (fun b _ hb => by simp [hb]) (by simp)]; simp

/-- Root fidelity depends only on the matrices, not the positive-semidefinite proofs. -/
theorem sqrtFidelity_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ σ' : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hσ' : σ'.PosSemidef) (h : σ = σ') :
    sqrtFidelity hρ hσ = sqrtFidelity hρ hσ' := by subst h; rfl

/-- **Average-fidelity → worst-case diamond bound.** For a CPTP channel `Φ` on an `n`-dimensional
system, its average gate fidelity bounds the diamond distance to the identity below:
`diamondDist(Φ, id) ≥ 1 − √(((n+1)·F_avg(Φ) − 1)/n)`. Composes the Horodecki identity
(`avgGateFidelity_eq`, inverted to `F_e = ((n+1)·F_avg − 1)/n`), the entanglement-fidelity↔Choi-overlap
identity (`sqrtFidelity_output_eq`, `√F((Φ⊗id)Ω,Ω) = √F_e`), and the Fuchs–van de Graaf↔diamond bridge
at the maximally-entangled input. The averaged benchmark certifies a worst-case error guarantee. -/
theorem avgGateFidelity_diamondDist_bound {m n : ℕ} [NeZero n]
    {K : Fin (m + 1) → Matrix (Fin n) (Fin n) ℂ} (hK : IsKrausChannel K) :
    1 - Real.sqrt (((n + 1) * avgGateFidelity K - 1) / n) ≤ diamondDist K (idKrausPad m n) := by
  have hbridge := one_sub_sqrtFidelity_output_le_diamondDist hK (isKrausChannel_idKrausPad m n)
    (isDensityOperator_maxEntangled (n := n))
  rw [sqrtFidelity_congr _ _ isDensityOperator_maxEntangled.1
      (krausMap_tensorKraus_idKrausPad m n _),
    sqrtFidelity_output_eq hK] at hbridge
  have hinv : entanglementFidelity K = ((n + 1) * avgGateFidelity K - 1) / n := by
    have he := avgGateFidelity_eq K hK
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    field_simp at he ⊢; linarith [he]
  rw [← hinv]; exact hbridge

end SKEFTHawking.QuantumNetwork
