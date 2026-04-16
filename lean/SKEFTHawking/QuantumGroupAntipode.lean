/-
Phase 5m Wave 2: Generic Antipode S for U_q(𝔤)

Defines the antipode on the generic quantum group QuantumGroup k A
(parameterized by Cartan matrix A) using the standard Drinfeld-Jimbo
formulas:

  S(E_i) = -E_i K_i⁻¹
  S(F_i) = -K_i F_i
  S(K_i) = K_i⁻¹,  S(K_i⁻¹) = K_i

The antipode is an algebra ANTI-homomorphism: S(ab) = S(b)S(a). We encode
this via FreeAlgebra.lift into (QuantumGroup k A)ᵐᵒᵖ, then compose with
MulOpposite.unop.

References:
  Kassel, "Quantum Groups" (Springer, 1995), Ch. VI
  Uqsl3Hopf.lean (5235 LOC, sl_3-specific template)
-/

import Mathlib
import SKEFTHawking.QuantumGroupCoproduct

open LaurentPolynomial

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k] {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}

/-! ## 1. Antipode on Generators -/

/-- Antipode on generators of U_q(𝔤). Standard Drinfeld-Jimbo formulas:
    S(E_i) = -E_i K_i⁻¹, S(F_i) = -K_i F_i,
    S(K_i) = K_i⁻¹, S(K_i⁻¹) = K_i. -/
def antipodeOnGenQG (A : Matrix (Fin r) (Fin r) ℤ) : QGGen r → QuantumGroup k A
  | .E i    => -(qgE k A i * qgKinv k A i)
  | .F i    => -(qgK k A i * qgF k A i)
  | .K i    => qgKinv k A i
  | .Kinv i => qgK k A i

/-- Antipode lifted to the free algebra → (QuantumGroup k A)ᵐᵒᵖ.
    Uses MulOpposite to encode the anti-homomorphism property S(ab)=S(b)S(a). -/
def antipodeFreeAlgQG (A : Matrix (Fin r) (Fin r) ℤ) :
    FreeAlgebra (QBase k) (QGGen r) →ₐ[QBase k] (QuantumGroup k A)ᵐᵒᵖ :=
  FreeAlgebra.lift (QBase k) (fun x => MulOpposite.op (antipodeOnGenQG k A x))

theorem antipodeFreeAlgQG_ι (A : Matrix (Fin r) (Fin r) ℤ) (x : QGGen r) :
    antipodeFreeAlgQG k A (FreeAlgebra.ι (QBase k) x) =
    MulOpposite.op (antipodeOnGenQG k A x) := by
  unfold antipodeFreeAlgQG; exact FreeAlgebra.lift_ι_apply _ _

private abbrev qgI' (x : QGGen r) : FreeAlgebra (QBase k) (QGGen r) :=
  FreeAlgebra.ι (QBase k) x

/-! ### Diamond-bypass helpers for negation in QuantumGroup

Same pattern as qg_sub_tmul in QuantumGroupCoproduct.lean: RingQuot's Neg
instance clashes with Ring's Neg, blocking `neg_mul` / `mul_neg`. -/

-- Verify Ring axiom compatibility with RingQuot instances
private example (a : QuantumGroup k A) : a + (-a) = 0 := add_neg_cancel a
private example (a b c : QuantumGroup k A) : (a + b) * c = a * c + b * c := add_mul a b c
private example (a : QuantumGroup k A) : (0 : QuantumGroup k A) * a = 0 := zero_mul a

-- Bypass RingQuot Add/Neg diamond: add_mul uses RingQuot.instAdd, but
-- eq_neg_of_add_eq_zero_left needs AddGroup.toAdd. respectTransparency
-- false bridges the gap for the `exact` elaboration.
-- Fix: `letI : NonUnitalNonAssocRing` locally fixes the instance synthesis
-- path so neg_mul/mul_neg can pattern-match. Used 20+ times in Uqsl3Hopf.
lemma qg_neg_mul (a b : QuantumGroup k A) : (-a) * b = -(a * b) := by
  letI : NonUnitalNonAssocRing (QuantumGroup k A) := inferInstance
  exact neg_mul a b

lemma qg_mul_neg (a b : QuantumGroup k A) : a * (-b) = -(a * b) := by
  letI : NonUnitalNonAssocRing (QuantumGroup k A) := inferInstance
  exact mul_neg a b

/-! ## 2. Per-relation antipode respect helpers (mechanical cases)

Groups I-IV are mechanical: K-invertibility, K-commutativity, KE, KF. -/

/-! ### Group I: K-invertibility -/

theorem antipodeFreeAlgQG_KKinv (i : Fin r) :
    antipodeFreeAlgQG k A (qgI' k (.K i) * qgI' k (.Kinv i)) =
    (1 : (QuantumGroup k A)ᵐᵒᵖ) := by
  rw [map_mul]
  erw [antipodeFreeAlgQG_ι, antipodeFreeAlgQG_ι]
  simp only [antipodeOnGenQG, ← MulOpposite.op_mul, qg_K_mul_Kinv, MulOpposite.op_one]

theorem antipodeFreeAlgQG_KinvK (i : Fin r) :
    antipodeFreeAlgQG k A (qgI' k (.Kinv i) * qgI' k (.K i)) =
    (1 : (QuantumGroup k A)ᵐᵒᵖ) := by
  rw [map_mul]
  erw [antipodeFreeAlgQG_ι, antipodeFreeAlgQG_ι]
  simp only [antipodeOnGenQG, ← MulOpposite.op_mul, qg_Kinv_mul_K, MulOpposite.op_one]

/-! ### Group II: K-commutativity -/

theorem antipodeFreeAlgQG_KK_comm (i j : Fin r) :
    antipodeFreeAlgQG k A (qgI' k (.K i) * qgI' k (.K j)) =
    antipodeFreeAlgQG k A (qgI' k (.K j) * qgI' k (.K i)) := by
  rw [map_mul, map_mul]
  erw [antipodeFreeAlgQG_ι (k := k) (A := A) (.K i),
       antipodeFreeAlgQG_ι (k := k) (A := A) (.K j)]
  simp only [antipodeOnGenQG, ← MulOpposite.op_mul]
  congr 1
  exact (qg_Kinv_Kinv_comm (A := A) k i j).symm

/-! ### Group III: K-E conjugation

S(K_i · E_j) = S(E_j) · S(K_i) [anti-hom] = (-E_j K_j⁻¹) · K_i⁻¹
S(q^{A_ij} · E_j · K_i) = q^{A_ij} · S(K_i) · S(E_j) = q^{A_ij} · K_i⁻¹ · (-E_j K_j⁻¹)
Equal via E_j · K_i⁻¹ = q^{A_ij} · K_i⁻¹ · E_j (from qg_E_Kinv_scaled). -/

private theorem anti_KE_helper (i j : Fin r) :
    qgE k A j * qgKinv k A j * qgKinv k A i =
    (T (A i j) : QBase k) • (qgKinv k A i * qgE k A j * qgKinv k A j) := by
  rw [show qgE k A j * qgKinv k A j * qgKinv k A i =
      (qgE k A j * qgKinv k A i) * qgKinv k A j from by
    rw [mul_assoc, qg_Kinv_Kinv_comm (A := A) k j i, ← mul_assoc]]
  rw [qg_E_Kinv_scaled k j i, smul_mul_assoc]

theorem antipodeFreeAlgQG_KE (i j : Fin r) :
    antipodeFreeAlgQG k A (qgI' k (.K i) * qgI' k (.E j)) =
    antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T (A i j)) * qgI' k (.E j) * qgI' k (.K i)) := by
  rw [show antipodeFreeAlgQG k A (qgI' k (.K i) * qgI' k (.E j)) =
      MulOpposite.op (-(qgE k A j * qgKinv k A j) * qgKinv k A i) by
    rw [map_mul]; erw [antipodeFreeAlgQG_ι, antipodeFreeAlgQG_ι]
    simp [antipodeOnGenQG, ← MulOpposite.op_neg, ← MulOpposite.op_mul]]
  rw [show antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T (A i j)) * qgI' k (.E j) * qgI' k (.K i)) =
      MulOpposite.op (qgKinv k A i * (-(qgE k A j * qgKinv k A j) *
        (algebraMap (QBase k) (QuantumGroup k A)) (T (A i j)))) by
    rw [map_mul, map_mul, AlgHom.commutes]
    erw [antipodeFreeAlgQG_ι, antipodeFreeAlgQG_ι]
    simp [antipodeOnGenQG, ← MulOpposite.op_neg, ← MulOpposite.op_mul]]
  congr 1
  rw [qg_neg_mul,
      show qgKinv k A i * (-(qgE k A j * qgKinv k A j) *
        (algebraMap (QBase k) (QuantumGroup k A)) (T (A i j))) =
      -(qgKinv k A i * (qgE k A j * qgKinv k A j) *
        (algebraMap (QBase k) (QuantumGroup k A)) (T (A i j))) from by
    rw [qg_neg_mul, qg_mul_neg]; noncomm_ring]
  congr 1
  rw [anti_KE_helper, Algebra.smul_def, Algebra.commutes (T (A i j))]; noncomm_ring

/-! ### Group IV: K-F conjugation

S(K_i · F_j) = S(F_j) · S(K_i) = (-K_j F_j) · K_i⁻¹
S(q^{-A_ij} · F_j · K_i) = q^{-A_ij} · S(K_i) · S(F_j) = q^{-A_ij} · K_i⁻¹ · (-K_j F_j)
Equal via K_j · K_i⁻¹ = K_i⁻¹ · K_j and F_j · K_i⁻¹ commutation. -/

private theorem qg_F_Kinv_scaled (i j : Fin r) :
    qgF k A j * qgKinv k A i = (T (-A i j) : QBase k) • (qgKinv k A i * qgF k A j) := by
  have h := qg_Kinv_F_scaled k (A := A) i j
  calc qgF k A j * qgKinv k A i
      = (T (-A i j) : QBase k) • ((T (A i j) : QBase k) • (qgF k A j * qgKinv k A i)) := by
        rw [smul_smul, show (T (-A i j) : QBase k) * T (A i j) = 1 from by
          rw [← T_add]; norm_num]; rw [one_smul]
    _ = (T (-A i j) : QBase k) • (qgKinv k A i * qgF k A j) := by rw [h]

private theorem anti_KF_helper (i j : Fin r) :
    qgK k A j * qgF k A j * qgKinv k A i =
    (T (-A i j) : QBase k) • (qgKinv k A i * qgK k A j * qgF k A j) := by
  rw [show qgK k A j * qgF k A j * qgKinv k A i =
      qgK k A j * (qgF k A j * qgKinv k A i) from by noncomm_ring,
      qg_F_Kinv_scaled k i j, mul_smul_comm]
  congr 1; rw [← mul_assoc, qg_K_Kinv_comm k j i, mul_assoc]

theorem antipodeFreeAlgQG_KF (i j : Fin r) :
    antipodeFreeAlgQG k A (qgI' k (.K i) * qgI' k (.F j)) =
    antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T (-(A i j))) * qgI' k (.F j) * qgI' k (.K i)) := by
  rw [show antipodeFreeAlgQG k A (qgI' k (.K i) * qgI' k (.F j)) =
      MulOpposite.op (-(qgK k A j * qgF k A j) * qgKinv k A i) by
    rw [map_mul]; erw [antipodeFreeAlgQG_ι, antipodeFreeAlgQG_ι]
    simp [antipodeOnGenQG, ← MulOpposite.op_neg, ← MulOpposite.op_mul]]
  rw [show antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T (-(A i j))) * qgI' k (.F j) * qgI' k (.K i)) =
      MulOpposite.op (qgKinv k A i * (-(qgK k A j * qgF k A j) *
        (algebraMap (QBase k) (QuantumGroup k A)) (T (-(A i j))))) by
    rw [map_mul, map_mul, AlgHom.commutes]
    erw [antipodeFreeAlgQG_ι, antipodeFreeAlgQG_ι]
    simp [antipodeOnGenQG, ← MulOpposite.op_neg, ← MulOpposite.op_mul]]
  congr 1
  rw [qg_neg_mul,
      show qgKinv k A i * (-(qgK k A j * qgF k A j) *
        (algebraMap (QBase k) (QuantumGroup k A)) (T (-(A i j)))) =
      -(qgKinv k A i * (qgK k A j * qgF k A j) *
        (algebraMap (QBase k) (QuantumGroup k A)) (T (-(A i j)))) from by
    rw [qg_neg_mul, qg_mul_neg]; noncomm_ring]
  congr 1
  rw [anti_KF_helper, Algebra.smul_def, Algebra.commutes (T (-(A i j)))]; noncomm_ring

/-! ### Group V: EF commutation -/

theorem antipodeFreeAlgQG_EF_diag (i : Fin r) :
    antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T 1 - T (-1)) *
       (qgI' k (.E i) * qgI' k (.F i) - qgI' k (.F i) * qgI' k (.E i))) =
    antipodeFreeAlgQG k A (qgI' k (.K i) - qgI' k (.Kinv i)) := by
  sorry

theorem antipodeFreeAlgQG_EF_off (i j : Fin r) (hij : i ≠ j) (hsym : A i j = A j i) :
    antipodeFreeAlgQG k A (qgI' k (.E i) * qgI' k (.F j)) =
    antipodeFreeAlgQG k A (qgI' k (.F j) * qgI' k (.E i)) := by
  sorry

/-! ### Groups VI/VII: Serre commutativity -/

theorem antipodeFreeAlgQG_SerreE_comm (i j : Fin r) (h : A i j = 0) (h' : A j i = 0)
    (hij : i ≠ j) :
    antipodeFreeAlgQG k A (qgI' k (.E i) * qgI' k (.E j)) =
    antipodeFreeAlgQG k A (qgI' k (.E j) * qgI' k (.E i)) := by
  rw [map_mul, map_mul]
  erw [antipodeFreeAlgQG_ι (k := k) (A := A) (.E i),
       antipodeFreeAlgQG_ι (k := k) (A := A) (.E j)]
  simp only [antipodeOnGenQG, ← MulOpposite.op_neg, ← MulOpposite.op_mul]
  congr 1
  -- Goal: -(E_j*Kinv_j) * -(E_i*Kinv_i) = -(E_i*Kinv_i) * -(E_j*Kinv_j)
  rw [qg_neg_mul, qg_mul_neg, qg_neg_mul, qg_mul_neg]
  -- -(-(E_j*Kinv_j*E_i*Kinv_i)) = -(-(E_i*Kinv_i*E_j*Kinv_j))
  -- = E_j*Kinv_j*E_i*Kinv_i = E_i*Kinv_i*E_j*Kinv_j
  congr 1
  -- Swap Kinv past E on each side, then use E-comm + Kinv-comm
  conv_lhs => rw [show qgE k A j * qgKinv k A j * (qgE k A i * qgKinv k A i) =
    qgE k A j * (qgKinv k A j * qgE k A i) * qgKinv k A i from by noncomm_ring,
    (qg_E_Kinv_comm k i j h').symm]
  conv_rhs => rw [show qgE k A i * qgKinv k A i * (qgE k A j * qgKinv k A j) =
    qgE k A i * (qgKinv k A i * qgE k A j) * qgKinv k A j from by noncomm_ring,
    (qg_E_Kinv_comm k j i h).symm]
  rw [show qgE k A j * (qgE k A i * qgKinv k A j) * qgKinv k A i =
    qgE k A j * qgE k A i * (qgKinv k A j * qgKinv k A i) from by noncomm_ring,
    show qgE k A i * (qgE k A j * qgKinv k A i) * qgKinv k A j =
    qgE k A i * qgE k A j * (qgKinv k A i * qgKinv k A j) from by noncomm_ring,
    qg_SerreE_comm k A i j h hij, qg_Kinv_Kinv_comm (A := A) k j i]

theorem antipodeFreeAlgQG_SerreF_comm (i j : Fin r) (h : A i j = 0) (h' : A j i = 0)
    (hij : i ≠ j) :
    antipodeFreeAlgQG k A (qgI' k (.F i) * qgI' k (.F j)) =
    antipodeFreeAlgQG k A (qgI' k (.F j) * qgI' k (.F i)) := by
  rw [map_mul, map_mul]
  erw [antipodeFreeAlgQG_ι (k := k) (A := A) (.F i),
       antipodeFreeAlgQG_ι (k := k) (A := A) (.F j)]
  simp only [antipodeOnGenQG, ← MulOpposite.op_neg, ← MulOpposite.op_mul]
  congr 1
  rw [qg_neg_mul, qg_mul_neg, qg_neg_mul, qg_mul_neg]
  congr 1
  -- K_j*F_j * K_i*F_i = K_i*F_i * K_j*F_j
  -- Uses: F_j*K_i = K_i*F_j (A_ij=0 via KF), K commute
  have hFjKi : qgF k A j * qgK k A i = qgK k A i * qgF k A j := by
    have := qg_KF k (A := A) i j; rw [h, neg_zero, T_zero, map_one, one_mul] at this
    exact this.symm
  have hFiKj : qgF k A i * qgK k A j = qgK k A j * qgF k A i := by
    have := qg_KF k (A := A) j i; rw [h', neg_zero, T_zero, map_one, one_mul] at this
    exact this.symm
  rw [show qgK k A j * qgF k A j * (qgK k A i * qgF k A i) =
      qgK k A j * (qgF k A j * qgK k A i) * qgF k A i from by noncomm_ring,
      hFjKi,
      show qgK k A i * qgF k A i * (qgK k A j * qgF k A j) =
      qgK k A i * (qgF k A i * qgK k A j) * qgF k A j from by noncomm_ring,
      hFiKj]
  congr 1
  rw [show qgK k A j * (qgK k A i * qgF k A j) * qgF k A i =
    qgK k A j * qgK k A i * (qgF k A j * qgF k A i) from by noncomm_ring,
    show qgK k A i * (qgK k A j * qgF k A i) * qgF k A j =
    qgK k A i * qgK k A j * (qgF k A i * qgF k A j) from by noncomm_ring,
    qg_SerreF_comm' k A i j h hij, qg_KK_comm k A j i]

/-! ### Groups VI/VII: Serre quadratic (HARD, multi-session) -/

theorem antipodeFreeAlgQG_SerreE_quad (i j : Fin r)
    (h : A i j = -1) (hii : A i i = 2) (hsym : A j i = -1) :
    antipodeFreeAlgQG k A
      (qgI' k (.E i) * qgI' k (.E i) * qgI' k (.E j) +
       qgI' k (.E j) * qgI' k (.E i) * qgI' k (.E i)) =
    antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T 1 + T (-1)) *
       qgI' k (.E i) * qgI' k (.E j) * qgI' k (.E i)) := by
  sorry

theorem antipodeFreeAlgQG_SerreF_quad (i j : Fin r)
    (h : A i j = -1) (hii : A i i = 2) (hsym : A j i = -1) :
    antipodeFreeAlgQG k A
      (qgI' k (.F i) * qgI' k (.F i) * qgI' k (.F j) +
       qgI' k (.F j) * qgI' k (.F i) * qgI' k (.F i)) =
    antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T 1 + T (-1)) *
       qgI' k (.F i) * qgI' k (.F j) * qgI' k (.F i)) := by
  sorry

end SKEFTHawking
