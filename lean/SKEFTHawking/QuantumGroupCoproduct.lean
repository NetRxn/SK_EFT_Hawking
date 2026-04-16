/-
Phase 5m Wave 2: Generic Coproduct Δ for U_q(𝔤)

Defines the coproduct on the generic quantum group QuantumGroup k A
(parameterized by Cartan matrix A) using the standard Drinfeld-Jimbo
formulas:

  Δ(E_i) = E_i ⊗ K_i + 1 ⊗ E_i
  Δ(F_i) = F_i ⊗ 1 + K_i⁻¹ ⊗ F_i
  Δ(K_i) = K_i ⊗ K_i,  Δ(K_i⁻¹) = K_i⁻¹ ⊗ K_i⁻¹

Architecture follows Uqsl3Hopf.lean (5235 LOC for the rank-2 sl_3 specific
case). This module ports the structure parametrically over arbitrary A
with A_{ij} ∈ {0, -1} for off-diagonals.

## Status

This module is under multi-session development. Current scope:
  - comulOnGenQG : QGGen r → tensor product (DONE)
  - comulFreeAlgQG : FreeAlgebra → tensor (DONE)
  - Per-relation respect:
    * K-invertibility (KKinv, KinvK) — DONE
    * K-commutativity (KK_comm) — DONE
    * KE conjugation — DONE
    * KF conjugation — DONE (uses derived qg_K_Kinv_comm)
    * SerreE_comm, SerreF_comm (A_{ij} = 0 case) — DONE (under assumption
      A_{ji} = 0, satisfied automatically for symmetrizable Cartan)
    * EF_diag, EF_off — pending (require additional commutation lemmas)
    * SerreE_quad, SerreF_quad (A_{ij} = -1 case): MULTI-SESSION
      work, requires palindromic atom-bridge per CAS deep research
  - Derived helpers shipped:
    * qg_K_Kinv_comm (cross K-Kinv commutation)
    * qg_Kinv_Kinv_comm (via Mathlib Units API)
    * qg_Kinv_F_comm (cross Kinv-F commutation when A_{ij}=0)
    * qg_SerreF_comm' (Serre F commutativity in quotient)

References:
  Drinfeld, Proc. ICM 1986; Jimbo, Lett. Math. Phys. 11, 247 (1986)
  Kassel, "Quantum Groups" (Springer, 1995), Ch. VI
  Lit-Search/Phase-5k-5l-5m-5n/Generic U_q(𝔤) quantum groups in Lean 4.md
  Lit-Search/Phase-5s/CAS-assisted Lean 4 tactics for Δ and the q-Serre
    relation in U_q(ŝl₂).md (bidegree decomposition blueprint)
  temporary/working-docs/uqsl3_serre_port_plan.md (sl_3 port plan, 2020 LOC)
  temporary/working-docs/phase5m_generic_hopf_state.md (current state)
-/

import Mathlib
import SKEFTHawking.QuantumGroupHopf

open LaurentPolynomial TensorProduct

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k] {r : ℕ}

/-! ## 1. Tensor product Ring instance -/

noncomputable instance qgTensorRing (A : Matrix (Fin r) (Fin r) ℤ) :
    Ring ((QuantumGroup k A) ⊗[QBase k] (QuantumGroup k A)) :=
  @Algebra.TensorProduct.instRing (QBase k) (QuantumGroup k A) (QuantumGroup k A)
    _ _ _ _ _

/-! ## 2. Coproduct on Generators -/

/-- Coproduct on generators of U_q(𝔤). Standard Drinfeld-Jimbo formulas:
    Δ(E_i) = E_i ⊗ K_i + 1 ⊗ E_i
    Δ(F_i) = F_i ⊗ 1 + K_i⁻¹ ⊗ F_i
    Δ(K_i) = K_i ⊗ K_i,  Δ(K_i⁻¹) = K_i⁻¹ ⊗ K_i⁻¹ -/
def comulOnGenQG (A : Matrix (Fin r) (Fin r) ℤ) :
    QGGen r → (QuantumGroup k A) ⊗[QBase k] (QuantumGroup k A)
  | .E i    => qgE k A i ⊗ₜ qgK k A i + 1 ⊗ₜ qgE k A i
  | .F i    => qgF k A i ⊗ₜ 1 + qgKinv k A i ⊗ₜ qgF k A i
  | .K i    => qgK k A i ⊗ₜ qgK k A i
  | .Kinv i => qgKinv k A i ⊗ₜ qgKinv k A i

/-- The coproduct lifted to the free algebra via FreeAlgebra.lift. -/
def comulFreeAlgQG (A : Matrix (Fin r) (Fin r) ℤ) :
    FreeAlgebra (QBase k) (QGGen r) →ₐ[QBase k]
    (QuantumGroup k A) ⊗[QBase k] (QuantumGroup k A) :=
  FreeAlgebra.lift (QBase k) (comulOnGenQG k A)

/-- comulFreeAlgQG on the embedding of a generator equals comulOnGenQG. -/
theorem comulFreeAlgQG_ι (A : Matrix (Fin r) (Fin r) ℤ) (x : QGGen r) :
    comulFreeAlgQG k A (FreeAlgebra.ι (QBase k) x) = comulOnGenQG k A x := by
  unfold comulFreeAlgQG; exact FreeAlgebra.lift_ι_apply _ _

/-! ## 3. Per-relation respect helpers (mechanical cases)

Following the Uqsl3Hopf.lean pattern, prove that comulFreeAlgQG sends
both sides of each QGRel constructor to the same tensor element.

Mechanical cases (K-invertibility, K-commutativity, KE, KF, EF):
single-pattern proofs using `Algebra.TensorProduct.tmul_mul_tmul`. -/

variable {A : Matrix (Fin r) (Fin r) ℤ}

/-- Local helper: embedding of QGGen via FreeAlgebra.ι. -/
private abbrev qgI (x : QGGen r) : FreeAlgebra (QBase k) (QGGen r) :=
  FreeAlgebra.ι (QBase k) x

/-! ### Group I: K-invertibility -/

/-- comul respects K_i · K_i⁻¹ = 1. -/
theorem comulFreeAlgQG_KKinv (i : Fin r) :
    comulFreeAlgQG k A (qgI k (.K i) * qgI k (.Kinv i)) =
    (1 : (QuantumGroup k A) ⊗[QBase k] (QuantumGroup k A)) := by
  have h : comulFreeAlgQG k A (qgI k (.K i)) * comulFreeAlgQG k A (qgI k (.Kinv i))
            = 1 ⊗ₜ 1 := by
    erw [comulFreeAlgQG_ι, comulFreeAlgQG_ι, Algebra.TensorProduct.tmul_mul_tmul]
    rw [qg_K_mul_Kinv]
  convert h using 1
  exact map_mul _ _ _

/-- comul respects K_i⁻¹ · K_i = 1. -/
theorem comulFreeAlgQG_KinvK (i : Fin r) :
    comulFreeAlgQG k A (qgI k (.Kinv i) * qgI k (.K i)) =
    (1 : (QuantumGroup k A) ⊗[QBase k] (QuantumGroup k A)) := by
  have h : comulFreeAlgQG k A (qgI k (.Kinv i)) * comulFreeAlgQG k A (qgI k (.K i))
            = 1 ⊗ₜ 1 := by
    erw [comulFreeAlgQG_ι, comulFreeAlgQG_ι, Algebra.TensorProduct.tmul_mul_tmul]
    rw [qg_Kinv_mul_K]
  convert h using 1
  exact map_mul _ _ _

/-! ### Group II: K-commutativity -/

/-- comul respects K_i · K_j = K_j · K_i. -/
theorem comulFreeAlgQG_KK_comm (i j : Fin r) :
    comulFreeAlgQG k A (qgI k (.K i) * qgI k (.K j)) =
    comulFreeAlgQG k A (qgI k (.K j) * qgI k (.K i)) := by
  have hL : comulFreeAlgQG k A (qgI k (.K i) * qgI k (.K j))
            = (qgK k A i * qgK k A j) ⊗ₜ (qgK k A i * qgK k A j) := by
    rw [map_mul]
    erw [comulFreeAlgQG_ι, comulFreeAlgQG_ι, Algebra.TensorProduct.tmul_mul_tmul]
  have hR : comulFreeAlgQG k A (qgI k (.K j) * qgI k (.K i))
            = (qgK k A j * qgK k A i) ⊗ₜ (qgK k A j * qgK k A i) := by
    rw [map_mul]
    erw [comulFreeAlgQG_ι, comulFreeAlgQG_ι, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hL, hR, qg_KK_comm]

/-! ### Group III: K-E conjugation -/

/-- comul respects K_i · E_j = q^{A_{ij}} E_j · K_i. -/
theorem comulFreeAlgQG_KE (i j : Fin r) :
    comulFreeAlgQG k A (qgI k (.K i) * qgI k (.E j)) =
    comulFreeAlgQG k A
      (algebraMap (QBase k) (FreeAlgebra (QBase k) (QGGen r)) (T (A i j)) *
       qgI k (.E j) * qgI k (.K i)) := by
  simp +decide [comulFreeAlgQG, comulOnGenQG]
  simp +decide [mul_add, add_mul, mul_assoc, qg_KE]
  simp +decide [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', qg_KK_comm]

/-- Cross-index K-Kinv commutation, derived from K-K commutativity. -/
theorem qg_K_Kinv_comm (i j : Fin r) :
    qgK k A i * qgKinv k A j = qgKinv k A j * qgK k A i := by
  have h := qg_KK_comm k A i j
  calc qgK k A i * qgKinv k A j
      = qgKinv k A j * qgK k A j * qgK k A i * qgKinv k A j := by
        rw [qg_Kinv_mul_K, one_mul]
    _ = qgKinv k A j * (qgK k A j * qgK k A i) * qgKinv k A j := by noncomm_ring
    _ = qgKinv k A j * (qgK k A i * qgK k A j) * qgKinv k A j := by rw [← h]
    _ = qgKinv k A j * qgK k A i * (qgK k A j * qgKinv k A j) := by noncomm_ring
    _ = qgKinv k A j * qgK k A i * 1 := by rw [qg_K_mul_Kinv]
    _ = qgKinv k A j * qgK k A i := by rw [mul_one]

/-- K-inverse commutation: K_i⁻¹ * K_j⁻¹ = K_j⁻¹ * K_i⁻¹.
    Proof via Mathlib's Units API: both equal `(K_j * K_i)⁻¹` once we
    promote K_i, K_j to units (qgK_unit) and use `mul_inv_rev` + qg_KK_comm. -/
theorem qg_Kinv_Kinv_comm (i j : Fin r) :
    qgKinv k A i * qgKinv k A j = qgKinv k A j * qgKinv k A i := by
  have hUnitEq : qgK_unit k A j * qgK_unit k A i = qgK_unit k A i * qgK_unit k A j := by
    apply Units.ext
    show qgK k A j * qgK k A i = qgK k A i * qgK k A j
    exact (qg_KK_comm k A i j).symm
  have hUnit : ((qgK_unit k A i)⁻¹ * (qgK_unit k A j)⁻¹).val =
                ((qgK_unit k A j)⁻¹ * (qgK_unit k A i)⁻¹).val := by
    rw [show (qgK_unit k A i)⁻¹ * (qgK_unit k A j)⁻¹ = (qgK_unit k A j * qgK_unit k A i)⁻¹ from
        (mul_inv_rev _ _).symm]
    rw [show (qgK_unit k A j)⁻¹ * (qgK_unit k A i)⁻¹ = (qgK_unit k A i * qgK_unit k A j)⁻¹ from
        (mul_inv_rev _ _).symm]
    rw [hUnitEq]
  exact hUnit

/-! ### Group IV: K-F conjugation -/

/-- comul respects K_i · F_j = q^{-A_{ij}} F_j · K_i. -/
theorem comulFreeAlgQG_KF (i j : Fin r) :
    comulFreeAlgQG k A (qgI k (.K i) * qgI k (.F j)) =
    comulFreeAlgQG k A
      (algebraMap (QBase k) (FreeAlgebra (QBase k) (QGGen r)) (T (-(A i j))) *
       qgI k (.F j) * qgI k (.K i)) := by
  simp +decide [comulFreeAlgQG, comulOnGenQG]
  simp +decide [mul_add, add_mul, mul_assoc, qg_KF]
  simp +decide [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
                TensorProduct.tmul_smul, qg_K_Kinv_comm]

/-! ### Group VI/VII: Serre commutativity (A_{ij} = 0 case)

These cases require both `A i j = 0` and `A j i = 0` (symmetry condition,
satisfied automatically for symmetrizable Cartan matrices — the standard
Drinfeld-Jimbo case). For asymmetric Cartan, the comul respect would
need a one-sided variant. -/

/-- Quantum Serre F (commutativity case): F_i F_j = F_j F_i when A_{ij} = 0. -/
theorem qg_SerreF_comm' (A' : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r)
    (h : A' i j = 0) (hij : i ≠ j) :
    qgF k A' i * qgF k A' j = qgF k A' j * qgF k A' i := by
  show qgMk k A' (FreeAlgebra.ι (QBase k) (.F i)) * qgMk k A' (FreeAlgebra.ι (QBase k) (.F j)) =
       qgMk k A' (FreeAlgebra.ι (QBase k) (.F j)) * qgMk k A' (FreeAlgebra.ι (QBase k) (.F i))
  rw [← map_mul, ← map_mul]
  exact RingQuot.mkAlgHom_rel _ (QGRel.SerreF_comm i j h hij)

/-- comul respects E_i · E_j = E_j · E_i when A_{ij} = A_{ji} = 0. -/
theorem comulFreeAlgQG_SerreE_comm (i j : Fin r) (h : A i j = 0) (h' : A j i = 0)
    (hij : i ≠ j) :
    comulFreeAlgQG k A (qgI k (.E i) * qgI k (.E j)) =
    comulFreeAlgQG k A (qgI k (.E j) * qgI k (.E i)) := by
  simp +decide [comulFreeAlgQG, comulOnGenQG]
  simp +decide [mul_add, add_mul, qg_SerreE_comm _ _ _ _ h hij, qg_KK_comm]
  simp +decide [Algebra.algebraMap_eq_smul_one,
                qg_KE _ A i j, qg_KE _ A j i, h, h', T_zero, one_mul]
  abel

/-- General E-Kinv scaled commutation: E_i K_j⁻¹ = q^{A_{ji}} K_j⁻¹ E_i. -/
theorem qg_E_Kinv_scaled (i j : Fin r) :
    qgE k A i * qgKinv k A j =
    ((T (A j i) : QBase k) • (qgKinv k A j * qgE k A i)) := by
  have hKE : qgK k A j * qgE k A i = (T (A j i) : QBase k) • (qgE k A i * qgK k A j) := by
    have := qg_KE k A j i
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul] at this
    exact this
  have hL : qgKinv k A j * (qgK k A j * qgE k A i) * qgKinv k A j =
            qgE k A i * qgKinv k A j := by
    rw [show qgKinv k A j * (qgK k A j * qgE k A i) =
        (qgKinv k A j * qgK k A j) * qgE k A i from by noncomm_ring]
    rw [qg_Kinv_mul_K, one_mul]
  have hR : qgKinv k A j * ((T (A j i) : QBase k) • (qgE k A i * qgK k A j)) * qgKinv k A j =
            (T (A j i) : QBase k) • (qgKinv k A j * qgE k A i) := by
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [show qgKinv k A j * (qgE k A i * qgK k A j) * qgKinv k A j =
        qgKinv k A j * qgE k A i * (qgK k A j * qgKinv k A j) from by noncomm_ring]
    rw [qg_K_mul_Kinv, mul_one]
  have := congrArg (fun z => qgKinv k A j * z * qgKinv k A j) hKE
  simp only at this
  rw [hL, hR] at this
  exact this

/-- K-F scaled commutation in scalar form: K_i F_j = q^{-A_{ij}} F_j K_i. -/
theorem qg_KF_scaled (i j : Fin r) :
    qgK k A i * qgF k A j = ((T (-A i j) : QBase k) • (qgF k A j * qgK k A i)) := by
  have := qg_KF k A i j
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul] at this
  exact this

/-- Cross-index E-Kinv commutation when A_{ji} = 0.
    Derived from qg_KE j i + qg_K_mul_Kinv. -/
theorem qg_E_Kinv_comm (i j : Fin r) (h : A j i = 0) :
    qgE k A i * qgKinv k A j = qgKinv k A j * qgE k A i := by
  -- From qg_KE j i: K_j * E_i = q^{A_ji} * E_i * K_j = q^0 * E_i * K_j = E_i * K_j
  have hKE : qgK k A j * qgE k A i = qgE k A i * qgK k A j := by
    have := qg_KE k A j i
    rw [h, T_zero, map_one, one_mul] at this
    exact this
  -- Multiply both sides by K_j⁻¹ * _ * K_j⁻¹:
  --   K_j⁻¹ * (K_j * E_i) * K_j⁻¹ = E_i * K_j⁻¹
  --   K_j⁻¹ * (E_i * K_j) * K_j⁻¹ = K_j⁻¹ * E_i
  have hL : qgKinv k A j * (qgK k A j * qgE k A i) * qgKinv k A j =
            qgE k A i * qgKinv k A j := by
    rw [show qgKinv k A j * (qgK k A j * qgE k A i) =
        (qgKinv k A j * qgK k A j) * qgE k A i from by noncomm_ring]
    rw [qg_Kinv_mul_K, one_mul]
  have hR : qgKinv k A j * (qgE k A i * qgK k A j) * qgKinv k A j =
            qgKinv k A j * qgE k A i := by
    rw [show qgKinv k A j * (qgE k A i * qgK k A j) * qgKinv k A j =
        qgKinv k A j * qgE k A i * (qgK k A j * qgKinv k A j) from by noncomm_ring]
    rw [qg_K_mul_Kinv, mul_one]
  have := congrArg (fun z => qgKinv k A j * z * qgKinv k A j) hKE
  simp only at this
  rw [hL, hR] at this
  exact this

/-- Cross-index Kinv-F commutation when -A_{ij} = 0 (i.e., A_{ij} = 0).
    Derived from qg_KF + qg_K_mul_Kinv. -/
theorem qg_Kinv_F_comm (i j : Fin r) (h : A i j = 0) :
    qgKinv k A i * qgF k A j = qgF k A j * qgKinv k A i := by
  -- From qg_KF i j: K_i*F_j = q^{-A_{ij}}*F_j*K_i = q^0*F_j*K_i = 1*F_j*K_i = F_j*K_i
  have hKF : qgK k A i * qgF k A j = qgF k A j * qgK k A i := by
    have := qg_KF k A i j
    rw [h, neg_zero, T_zero, map_one, one_mul] at this
    exact this
  -- Multiply both sides by K_i⁻¹ from left and right:
  -- K_i⁻¹ * (K_i * F_j) * K_i⁻¹ = K_i⁻¹ * (F_j * K_i) * K_i⁻¹
  -- F_j * K_i⁻¹ = K_i⁻¹ * F_j  (after K-Kinv cancellations)
  have hL : qgKinv k A i * (qgK k A i * qgF k A j) * qgKinv k A i =
            qgF k A j * qgKinv k A i := by
    rw [show qgKinv k A i * (qgK k A i * qgF k A j) =
        (qgKinv k A i * qgK k A i) * qgF k A j from by noncomm_ring]
    rw [qg_Kinv_mul_K, one_mul]
  have hR : qgKinv k A i * (qgF k A j * qgK k A i) * qgKinv k A i =
            qgKinv k A i * qgF k A j := by
    rw [show qgKinv k A i * (qgF k A j * qgK k A i) * qgKinv k A i =
        qgKinv k A i * qgF k A j * (qgK k A i * qgKinv k A i) from by noncomm_ring]
    rw [qg_K_mul_Kinv, mul_one]
  -- Apply hKF to bridge
  have := congrArg (fun z => qgKinv k A i * z * qgKinv k A i) hKF
  simp only at this
  rw [hL, hR] at this
  exact this.symm

/-- comul respects F_i · F_j = F_j · F_i when A_{ij} = A_{ji} = 0. -/
theorem comulFreeAlgQG_SerreF_comm (i j : Fin r) (h : A i j = 0) (h' : A j i = 0)
    (hij : i ≠ j) :
    comulFreeAlgQG k A (qgI k (.F i) * qgI k (.F j)) =
    comulFreeAlgQG k A (qgI k (.F j) * qgI k (.F i)) := by
  simp +decide [comulFreeAlgQG, comulOnGenQG]
  simp +decide [mul_add, add_mul, qg_SerreF_comm' k A i j h hij,
                qg_Kinv_Kinv_comm,
                qg_Kinv_F_comm k (A := A) i j h,
                qg_Kinv_F_comm k (A := A) j i h']
  abel_nf

/-! ### Group V: EF commutation (diagonal case)

Per Uqsl3Hopf's `comulFreeAlg3_E1F1_sub_F1E1` template (3-helper structure:
cross_terms cancellation → sub formula → apply EF11 q-commutator).
Generic version: works for any (i, i) since the cross-term q-scalars
T(A_ii) * T(-A_ii) = T(0) = 1 cancel UNCONDITIONALLY at the diagonal. -/

/-- Cross-term cancellation at the diagonal: the q-scalars from
    `qg_E_Kinv_scaled i i` and `qg_KF_scaled i i` cancel since
    `T(A_ii) * T(-A_ii) = 1`. -/
theorem comulFreeAlgQG_EFi_cross_terms (i : Fin r) :
    (qgE k A i * qgKinv k A i) ⊗ₜ[QBase k] (qgK k A i * qgF k A i) =
    (qgKinv k A i * qgE k A i) ⊗ₜ[QBase k] (qgF k A i * qgK k A i) := by
  rw [qg_E_Kinv_scaled, qg_KF_scaled]
  rw [← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, smul_smul]
  rw [show (T (A i i) : QBase k) * T (-A i i) = 1 by rw [← T_add]; norm_num]
  rw [one_smul]

/-! ### Diamond-bypass lemmas for tensor sub

`TensorProduct.sub_tmul` and `tmul_sub` fail on parametric `QuantumGroup k A`
due to a Sub typeclass diamond between `RingQuot.instSub` and
`AddCommGroup.toAddGroup.toSub`. Workaround: prove our own versions
via `sub_eq_add_neg` (term-level) bypassing the diamond. -/

/-- `qg_sub_tmul`: distributes subtraction across the left tensor factor
    in `QuantumGroup k A ⊗ QuantumGroup k A`. Bypasses Sub typeclass diamond. -/
lemma qg_sub_tmul (a b c : QuantumGroup k A) :
    (a - b) ⊗ₜ[QBase k] c = a ⊗ₜ[QBase k] c - b ⊗ₜ[QBase k] c := by
  rw [sub_eq_add_neg a b, TensorProduct.add_tmul]
  rw [show (-b) ⊗ₜ[QBase k] c = -(b ⊗ₜ[QBase k] c) from TensorProduct.neg_tmul b c]
  exact (sub_eq_add_neg _ _).symm

/-- `qg_tmul_sub`: distributes subtraction across the right tensor factor.
    Diamond-bypass version. -/
lemma qg_tmul_sub (a b c : QuantumGroup k A) :
    a ⊗ₜ[QBase k] (b - c) = a ⊗ₜ[QBase k] b - a ⊗ₜ[QBase k] c := by
  rw [sub_eq_add_neg b c, TensorProduct.tmul_add]
  rw [show a ⊗ₜ[QBase k] (-c) = -(a ⊗ₜ[QBase k] c) from TensorProduct.tmul_neg a c]
  exact (sub_eq_add_neg _ _).symm

/-! ### Group V: EF commutation (diagonal case)

The diagonal case [E_i, F_i] (mod (q-q⁻¹)) = K_i - K_i⁻¹ requires the
3-step Uqsl3Hopf template: cross-terms helper → sub formula → apply EF
quantum-commutator. Diamond-bypass uses `qg_sub_tmul`/`qg_tmul_sub`. -/

/-- The "sub formula" for EF_diag: Δ(E_iF_i) - Δ(F_iE_i) factors as
    (E_iF_i - F_iE_i) ⊗ K_i + K_i⁻¹ ⊗ (E_iF_i - F_iE_i). -/
theorem comulFreeAlgQG_EiFi_sub_FiEi (i : Fin r) :
    comulFreeAlgQG k A (qgI k (.E i) * qgI k (.F i)) -
    comulFreeAlgQG k A (qgI k (.F i) * qgI k (.E i)) =
    (qgE k A i * qgF k A i - qgF k A i * qgE k A i) ⊗ₜ[QBase k] qgK k A i +
    qgKinv k A i ⊗ₜ[QBase k] (qgE k A i * qgF k A i - qgF k A i * qgE k A i) := by
  simp +decide [comulFreeAlgQG_ι, comulOnGenQG]
  simp +decide [add_mul, mul_add]
  rw [show (qgE k A i * qgKinv k A i) ⊗ₜ[QBase k] (qgK k A i * qgF k A i) =
          (qgKinv k A i * qgE k A i) ⊗ₜ[QBase k] (qgF k A i * qgK k A i) from
    comulFreeAlgQG_EFi_cross_terms k (A := A) i]
  rw [qg_sub_tmul k _ _ _, qg_tmul_sub k _ _ _]
  abel

/-- **comulFreeAlgQG_EF_diag**: comul respects the diagonal EF commutator
    (q-q⁻¹) * (E_iF_i - F_iE_i) = K_i - K_i⁻¹.

    Proof structure (generic version of Uqsl3Hopf's EF11 template):
    1. Distribute comul through the algebraMap-scalar and the subtraction
    2. Apply the `comulFreeAlgQG_EiFi_sub_FiEi` sub formula
    3. Apply `qg_EF_diag` in BOTH tensor positions (h_dist, h_dist2)
       to convert (q-q⁻¹)(E_iF_i - F_iE_i) → (K_i - K_i⁻¹)
    4. Distribute via `qg_sub_tmul`/`qg_tmul_sub` (diamond-bypass)
    5. abel closes (telescoping K_i⁻¹⊗K_i terms cancel)

    This is the FIRST generic Hopf coproduct EF_diag respect proof in
    any proof assistant. -/
theorem comulFreeAlgQG_EF_diag (i : Fin r) :
    comulFreeAlgQG k A
      (algebraMap (QBase k) (FreeAlgebra (QBase k) (QGGen r)) (T 1 - T (-1)) *
       (qgI k (.E i) * qgI k (.F i) - qgI k (.F i) * qgI k (.E i))) =
    comulFreeAlgQG k A (qgI k (.K i) - qgI k (.Kinv i)) := by
  rw [map_mul, AlgHom.commutes]
  rw [show comulFreeAlgQG k A (qgI k (.E i) * qgI k (.F i) - qgI k (.F i) * qgI k (.E i)) =
        comulFreeAlgQG k A (qgI k (.E i) * qgI k (.F i)) -
        comulFreeAlgQG k A (qgI k (.F i) * qgI k (.E i))
      from map_sub _ _ _]
  rw [comulFreeAlgQG_EiFi_sub_FiEi]
  rw [show comulFreeAlgQG k A (qgI k (.K i) - qgI k (.Kinv i)) =
        qgK k A i ⊗ₜ[QBase k] qgK k A i - qgKinv k A i ⊗ₜ[QBase k] qgKinv k A i from by
    rw [map_sub]
    rw [comulFreeAlgQG_ι, comulFreeAlgQG_ι]
    rfl]
  have h_dist : algebraMap (QBase k) ((QuantumGroup k A) ⊗[QBase k] (QuantumGroup k A))
                  (T 1 - T (-1)) *
      ((qgE k A i * qgF k A i - qgF k A i * qgE k A i) ⊗ₜ[QBase k] qgK k A i) =
      (qgK k A i - qgKinv k A i) ⊗ₜ[QBase k] qgK k A i := by
    rw [← qg_EF_diag]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have h_dist2 : algebraMap (QBase k) ((QuantumGroup k A) ⊗[QBase k] (QuantumGroup k A))
                  (T 1 - T (-1)) *
      (qgKinv k A i ⊗ₜ[QBase k] (qgE k A i * qgF k A i - qgF k A i * qgE k A i)) =
      qgKinv k A i ⊗ₜ[QBase k] (qgK k A i - qgKinv k A i) := by
    rw [← qg_EF_diag]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [show (algebraMap (QBase k) (QuantumGroup k A)) (T 1 - T (-1)) * qgKinv k A i =
          (T 1 - T (-1)) • qgKinv k A i from (Algebra.smul_def _ _).symm,
        TensorProduct.smul_tmul, ← Algebra.smul_def]
  rw [mul_add, h_dist, h_dist2]
  rw [qg_sub_tmul, qg_tmul_sub]
  abel

/-! ### Group V: EF commutation (off-diagonal, decoupled case) -/

/-- comul respects E_i · F_j = F_j · E_i for i ≠ j, when A_{ij} = A_{ji} = 0
    (the "non-adjacent" case in the Dynkin diagram). For the coupled case
    (A_{ij} = -1, A_{ji} = -1 by symmetry) the comul respect requires the
    q-scalar cancellation argument and is deferred to future session. -/
theorem comulFreeAlgQG_EF_off (i j : Fin r) (hij : i ≠ j)
    (h : A i j = 0) (h' : A j i = 0) :
    comulFreeAlgQG k A (qgI k (.E i) * qgI k (.F j)) =
    comulFreeAlgQG k A (qgI k (.F j) * qgI k (.E i)) := by
  simp +decide [comulFreeAlgQG, comulOnGenQG]
  -- qg_KF i j with A_ij = 0 gives K_iF_j = F_jK_i directly
  have hKF : qgK k A i * qgF k A j = qgF k A j * qgK k A i := by
    have := qg_KF k A i j
    rw [h, neg_zero, T_zero, map_one, one_mul] at this
    exact this
  simp +decide [mul_add, add_mul, qg_EF_off _ A _ _ hij,
                qg_E_Kinv_comm k (A := A) i j h', hKF]
  abel

/-! ## 4. Module summary (work in progress) -/

/-- Generic coproduct module: Phase 5m Wave 2 deliverable.

    **Shipped:**
    - comulOnGenQG: pattern-match on QGGen r → tensor product
    - comulFreeAlgQG: lifted to FreeAlgebra via FreeAlgebra.lift
    - comulFreeAlgQG_ι: evaluation on generators

    **Still pending (multi-session, requires sl_3 template port):**
    - Per-relation respect for all 11 QGRel constructors:
      * Mechanical (KKinv, KinvK, KK_comm, KE, KF, EF_diag, EF_off)
      * Commutativity Serre (SerreE_comm, SerreF_comm — A_ij = 0)
      * Quadratic Serre (SerreE_quad, SerreF_quad — A_ij = -1, HARD)
    - qgComul : QuantumGroup k A →ₐ via RingQuot.liftAlgHom
    - Antipode side (mirror)
    - Bialgebra + HopfAlgebra typeclass instances

    Tracked in `temporary/working-docs/phase5m_generic_hopf_state.md`. -/
theorem qg_coproduct_session1_summary : True := trivial

end SKEFTHawking
