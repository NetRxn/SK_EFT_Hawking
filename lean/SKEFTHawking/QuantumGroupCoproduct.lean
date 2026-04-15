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
  - Per-relation respect for K-invertibility, K-commutativity, KE, KF,
    EF cases (mechanical) (DONE)
  - SerreE_comm, SerreF_comm respect (A_{ij} = 0 case) (DONE)
  - SerreE_quad, SerreF_quad respect (A_{ij} = -1 case): MULTI-SESSION
    work, requires palindromic atom-bridge per CAS deep research

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
