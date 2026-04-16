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

private theorem anti_EF_diag_KFEKinv (i : Fin r) :
    qgK k A i * qgF k A i * (qgE k A i * qgKinv k A i) = qgF k A i * qgE k A i := by
  have hKF := qg_KF_scaled k (A := A) i i
  have hKE : qgK k A i * qgE k A i = (T (A i i) : QBase k) • (qgE k A i * qgK k A i) := by
    have := qg_KE k A i i
    rwa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul] at this
  rw [show qgK k A i * qgF k A i * (qgE k A i * qgKinv k A i) =
      qgK k A i * qgF k A i * qgE k A i * qgKinv k A i from by noncomm_ring,
      hKF, smul_mul_assoc, smul_mul_assoc,
      show qgF k A i * qgK k A i * qgE k A i = qgF k A i * (qgK k A i * qgE k A i) from by
        noncomm_ring,
      hKE, mul_smul_comm, smul_mul_assoc, smul_smul,
      show (T (-A i i) : QBase k) * T (A i i) = 1 from by rw [← T_add]; norm_num, one_smul,
      show qgF k A i * (qgE k A i * qgK k A i) * qgKinv k A i =
        qgF k A i * qgE k A i * (qgK k A i * qgKinv k A i) from by noncomm_ring,
      qg_K_mul_Kinv, mul_one]

private theorem anti_EF_diag_EKinvKF (i : Fin r) :
    qgE k A i * qgKinv k A i * (qgK k A i * qgF k A i) = qgE k A i * qgF k A i := by
  rw [show qgE k A i * qgKinv k A i * (qgK k A i * qgF k A i) =
      qgE k A i * (qgKinv k A i * qgK k A i) * qgF k A i from by noncomm_ring,
      qg_Kinv_mul_K, mul_one]

theorem antipodeFreeAlgQG_EF_diag (i : Fin r) :
    antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T 1 - T (-1)) *
       (qgI' k (.E i) * qgI' k (.F i) - qgI' k (.F i) * qgI' k (.E i))) =
    antipodeFreeAlgQG k A (qgI' k (.K i) - qgI' k (.Kinv i)) := by
  simp only [map_sub, map_mul, AlgHom.commutes, antipodeFreeAlgQG, antipodeOnGenQG,
             FreeAlgebra.lift_ι_apply]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_neg,
             MulOpposite.unop_op]
  letI : NonUnitalNonAssocRing (QuantumGroup k A) := inferInstance
  simp only [neg_mul, mul_neg, neg_neg]
  rw [anti_EF_diag_KFEKinv k, anti_EF_diag_EKinvKF k]
  -- Goal has MulOpposite.unop (algebraMap ... (T ...)) — simplify to algebraMap
  simp only [MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  -- Goal: (F_i*E_i - E_i*F_i) * (algebraMap(T1) - algebraMap(T(-1))) = Kinv_i - K_i
  rw [show (algebraMap (QBase k) (QuantumGroup k A)) (T 1) -
      (algebraMap (QBase k) (QuantumGroup k A)) (T (-1)) =
      (algebraMap (QBase k) (QuantumGroup k A)) (T 1 - T (-1)) from (map_sub _ _ _).symm,
      (Algebra.commutes (T 1 - T (-1)) (qgF k A i * qgE k A i - qgE k A i * qgF k A i)).symm,
      show qgF k A i * qgE k A i - qgE k A i * qgF k A i =
        -(qgE k A i * qgF k A i - qgF k A i * qgE k A i) from by noncomm_ring,
      mul_neg, qg_EF_diag]
  noncomm_ring

private theorem anti_EF_off_helper (i j : Fin r) (hij : i ≠ j) (hsym : A i j = A j i) :
    qgK k A j * qgF k A j * (qgE k A i * qgKinv k A i) =
    qgE k A i * qgKinv k A i * (qgK k A j * qgF k A j) := by
  -- Move E_i left: F_j*E_i = E_i*F_j (EF_off), K_j*E_i = T(A_ji)*E_i*K_j (KE)
  -- Move Kinv_i left: F_j*Kinv_i = T(-A_ij)*Kinv_i*F_j, K_j*Kinv_i = Kinv_i*K_j
  -- Net q-factor: T(A_ji)*T(-A_ij) = T(A_ij)*T(-A_ij) = 1 (by hsym)
  have hFE := qg_EF_off k A i j hij       -- E_i*F_j = F_j*E_i
  have hKE : qgK k A j * qgE k A i = (T (A j i) : QBase k) • (qgE k A i * qgK k A j) := by
    have := qg_KE k A j i
    rwa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul] at this
  have hFK := qg_F_Kinv_scaled k (A := A) i j  -- F_j*Kinv_i = T(-A_ij)•(Kinv_i*F_j)
  have hKKinv := qg_K_Kinv_comm k (A := A) j i     -- K_j*Kinv_i = Kinv_i*K_j
  -- Strategy: move E_i left (via EF_off + KE), move Kinv_i left (via F_Kinv_scaled + K_Kinv_comm)
  -- Net q-factor: T(A_ji)*T(-A_ij) = 1 (by hsym)
  rw [show qgK k A j * qgF k A j * (qgE k A i * qgKinv k A i) =
    qgK k A j * (qgF k A j * qgE k A i) * qgKinv k A i from by noncomm_ring, ← hFE,
    show qgK k A j * (qgE k A i * qgF k A j) = (qgK k A j * qgE k A i) * qgF k A j from by
      noncomm_ring, hKE, smul_mul_assoc, smul_mul_assoc,
    show qgE k A i * qgK k A j * qgF k A j * qgKinv k A i =
      qgE k A i * qgK k A j * (qgF k A j * qgKinv k A i) from by noncomm_ring, hFK,
    mul_smul_comm]
  congr 1
  rw [show qgE k A i * qgK k A j * (qgKinv k A i * qgF k A j) =
    qgE k A i * (qgK k A j * qgKinv k A i) * qgF k A j from by noncomm_ring, hKKinv]
  rw [smul_smul, show (T (A j i) : QBase k) * T (-A i j) = 1 from by
    rw [hsym, ← T_add]; norm_num, one_smul]; noncomm_ring

theorem antipodeFreeAlgQG_EF_off (i j : Fin r) (hij : i ≠ j) (hsym : A i j = A j i) :
    antipodeFreeAlgQG k A (qgI' k (.E i) * qgI' k (.F j)) =
    antipodeFreeAlgQG k A (qgI' k (.F j) * qgI' k (.E i)) := by
  rw [map_mul, map_mul]
  erw [antipodeFreeAlgQG_ι (k := k) (A := A) (.E i),
       antipodeFreeAlgQG_ι (k := k) (A := A) (.F j)]
  simp only [antipodeOnGenQG, ← MulOpposite.op_neg, ← MulOpposite.op_mul]
  congr 1
  rw [qg_neg_mul, qg_mul_neg, qg_neg_mul, qg_mul_neg]
  congr 1
  congr 1; exact anti_EF_off_helper k i j hij hsym

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

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem antipodeFreeAlgQG_SerreE_quad (i j : Fin r)
    (h : A i j = -1) (hii : A i i = 2) (hsym : A j i = -1) (hjj : A j j = 2) :
    antipodeFreeAlgQG k A
      (qgI' k (.E i) * qgI' k (.E i) * qgI' k (.E j) +
       qgI' k (.E j) * qgI' k (.E i) * qgI' k (.E i)) =
    antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T 1 + T (-1)) *
       qgI' k (.E i) * qgI' k (.E j) * qgI' k (.E i)) := by
  -- Expand both sides directly (skip sub_eq_zero to avoid MulOpposite Sub diamond)
  simp only [map_add, map_mul, AlgHom.commutes,
             antipodeFreeAlgQG, antipodeOnGenQG, FreeAlgebra.lift_ι_apply]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_add, MulOpposite.unop_mul,
             MulOpposite.unop_op,
             MulOpposite.algebraMap_apply, mul_assoc]
  -- Phase 4: handle negation via letI + neg_mul/mul_neg
  letI : NonUnitalNonAssocRing (QuantumGroup k A) := inferInstance
  simp only [neg_mul, mul_neg, neg_neg]
  -- Phase 5: push E·Kinv to Kinv·E (same-index)
  simp_rw [qg_E_Kinv_scaled k (A := A) i i, qg_E_Kinv_scaled k (A := A) j j]
  -- Phase 6: convert trailing algebraMap to smul, collect scalars
  have hcentral : ∀ (r : QBase k) (x : QuantumGroup k A),
      x * algebraMap (QBase k) (QuantumGroup k A) r = r • x :=
    fun r x => by erw [Algebra.smul_def, Algebra.commutes]
  have hcentral_left : ∀ (r : QBase k) (x : QuantumGroup k A),
      algebraMap (QBase k) (QuantumGroup k A) r * x = r • x :=
    fun r x => by rw [Algebra.smul_def]
  simp only [mul_add, mul_one, hcentral, hcentral_left]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← T_add]
  norm_num [T_zero]
  simp only [one_smul, ← mul_assoc]
  -- Phase 7: Kinv·E commutation helpers for all index pairs
  have hKinvE_ii : qgKinv k A i * qgE k A i =
      (T (-2) : QBase k) • (qgE k A i * qgKinv k A i) := by
    rw [qg_E_Kinv_scaled k (A := A) i i, hii]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hKinvE_jj : qgKinv k A j * qgE k A j =
      (T (-2) : QBase k) • (qgE k A j * qgKinv k A j) := by
    rw [qg_E_Kinv_scaled k (A := A) j j, hjj]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hKinvE_ij : qgKinv k A i * qgE k A j =
      (T 1 : QBase k) • (qgE k A j * qgKinv k A i) := by
    rw [qg_E_Kinv_scaled k (A := A) j i, h]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hKinvE_ji : qgKinv k A j * qgE k A i =
      (T 1 : QBase k) • (qgE k A i * qgKinv k A j) := by
    rw [qg_E_Kinv_scaled k (A := A) i j, hsym]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  -- Phase 8: push all Kinv right past E
  simp only [mul_assoc, hKinvE_ii, hKinvE_jj, hKinvE_ij, hKinvE_ji,
             mul_smul_comm, smul_mul_assoc, smul_smul] at ⊢
  simp only [← T_add] at ⊢
  -- Phase 9: apply pure Serre right-multiplied by Kinv chain
  have hSE := qg_SerreE_quad_smul k i j h
  have h_mul := congr_arg
    (⇑(LinearMap.mulRight (QBase k)
        (qgKinv k A i * qgKinv k A i * qgKinv k A j))) hSE
  simp only [map_add, map_sub, map_zero, LinearMap.mulRight_apply,
             LinearMap.map_smul_of_tower] at h_mul
  -- Helpers for atom-equality proofs
  have move_alg_left : ∀ (r : QBase k) (x y : QuantumGroup k A),
      x * ((algebraMap (QBase k) (QuantumGroup k A)) r * y) =
      (algebraMap (QBase k) (QuantumGroup k A)) r * (x * y) := by
    intros r x y; rw [← mul_assoc, (Algebra.commutes r x).symm, mul_assoc]
  have alg_T_cancel3 : ∀ (a b c : ℤ) (x : QuantumGroup k A), a + b + c = 0 →
      (algebraMap (QBase k) (QuantumGroup k A)) (T a) *
        ((algebraMap (QBase k) (QuantumGroup k A)) (T b) *
          ((algebraMap (QBase k) (QuantumGroup k A)) (T c) * x)) = x := by
    intros a b c x habc
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, ← T_add, ← T_add, habc,
        T_zero, map_one, one_mul]
  -- hA2: E_i²E_j · Kinv³ = (E_i·Kinv_i)²·(E_j·Kinv_j) via 3 E_Kinv_scaled applications
  -- Net scalar: T(A_ij)*T(A_ii)*T(A_ij) = T(-1)*T(2)*T(-1) = T(0) = 1
  have hA2 : qgE k A i * (qgE k A i * (qgE k A j *
      (qgKinv k A i * (qgKinv k A i * qgKinv k A j)))) =
    qgE k A i * (qgKinv k A i * (qgE k A i * (qgKinv k A i * (qgE k A j * qgKinv k A j)))) := by
    -- Expose and commute E_j past Kinv_i
    rw [show qgE k A i * (qgE k A i * (qgE k A j *
        (qgKinv k A i * (qgKinv k A i * qgKinv k A j)))) =
      qgE k A i * (qgE k A i * ((qgE k A j * qgKinv k A i) *
        (qgKinv k A i * qgKinv k A j))) from by noncomm_ring,
      qg_E_Kinv_scaled k j i, h]
    simp only [smul_mul_assoc, mul_smul_comm]
    -- Step 2: expose E_i·Kinv_i inside the T(-1)•, apply E_Kinv_scaled
    rw [show (T (-1) : QBase k) • (qgE k A i * (qgE k A i *
        (qgKinv k A i * qgE k A j * (qgKinv k A i * qgKinv k A j)))) =
      (T (-1) : QBase k) • (qgE k A i * ((qgE k A i * qgKinv k A i) *
        (qgE k A j * (qgKinv k A i * qgKinv k A j)))) from by congr 1; noncomm_ring,
      qg_E_Kinv_scaled k i i, hii]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    -- Step 3: expose E_j·Kinv_i inside the (T(-1)*T(2))•
    rw [show (T (-1) * T 2 : QBase k) • (qgE k A i * ((qgKinv k A i * qgE k A i) *
        (qgE k A j * (qgKinv k A i * qgKinv k A j)))) =
      (T (-1) * T 2 : QBase k) • (qgE k A i * (qgKinv k A i * qgE k A i *
        ((qgE k A j * qgKinv k A i) * qgKinv k A j))) from by congr 1; noncomm_ring,
      qg_E_Kinv_scaled k j i, h]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    -- Cancel: T(-1)*T(2)*T(-1) = T(0) = 1
    rw [show (T (-1) * T 2 * T (-1) : QBase k) = 1 from by rw [← T_add, ← T_add]; norm_num,
        one_smul]
    noncomm_ring
  -- hA1: E_jE_i² · Kinv³ = (E_j·Kinv_j)·(E_i·Kinv_i)² (with Kinv chain reorder)
  have hA1 : qgE k A j * (qgE k A i * (qgE k A i *
      (qgKinv k A i * (qgKinv k A i * qgKinv k A j)))) =
    qgE k A j * (qgKinv k A j * (qgE k A i * (qgKinv k A i * (qgE k A i * qgKinv k A i)))) := by
    -- Reorder Kinv chain: Kinv_i²Kinv_j → Kinv_jKinv_i² (via Kinv_Kinv_comm)
    rw [show qgKinv k A i * (qgKinv k A i * qgKinv k A j) =
      qgKinv k A j * qgKinv k A i * qgKinv k A i from by
      rw [mul_assoc, qg_Kinv_Kinv_comm (A := A) k i j, ← mul_assoc,
          qg_Kinv_Kinv_comm (A := A) k i j, mul_assoc]]
    -- Step 1: expose E_i·Kinv_j
    rw [show qgE k A j * (qgE k A i * (qgE k A i *
        (qgKinv k A j * qgKinv k A i * qgKinv k A i))) =
      qgE k A j * (qgE k A i * ((qgE k A i * qgKinv k A j) *
        (qgKinv k A i * qgKinv k A i))) from by noncomm_ring,
      qg_E_Kinv_scaled k i j, hsym]
    simp only [smul_mul_assoc, mul_smul_comm]
    -- Step 2: expose E_i·Kinv_j (second)
    rw [show (T (-1) : QBase k) • (qgE k A j * (qgE k A i *
        ((qgKinv k A j * qgE k A i) * (qgKinv k A i * qgKinv k A i)))) =
      (T (-1) : QBase k) • (qgE k A j * ((qgE k A i * qgKinv k A j) *
        (qgE k A i * (qgKinv k A i * qgKinv k A i)))) from by congr 1; noncomm_ring,
      qg_E_Kinv_scaled k i j, hsym]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    -- Step 3: expose E_i·Kinv_i (same-index pair interleaving) — LHS only
    conv_lhs =>
      rw [show (T (-1) * T (-1) : QBase k) • (qgE k A j *
          ((qgKinv k A j * qgE k A i) * (qgE k A i * (qgKinv k A i * qgKinv k A i)))) =
        (T (-1) * T (-1) : QBase k) • (qgE k A j *
          (qgKinv k A j * qgE k A i * ((qgE k A i * qgKinv k A i) * qgKinv k A i))) from by
        congr 1; noncomm_ring]
      rw [qg_E_Kinv_scaled k i i, hii]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    -- Cancel: T(-1)*T(-1)*T(2) = T(0) = 1
    rw [show (T (-1) * T (-1) * T 2 : QBase k) = 1 from by rw [← T_add, ← T_add]; norm_num,
        one_smul]
    noncomm_ring
  -- hB: E_iE_jE_i · Kinv³ = (E_i·Kinv_i)·(E_j·Kinv_j)·(E_i·Kinv_i)
  have hB : qgE k A i * (qgE k A j * (qgE k A i *
      (qgKinv k A i * (qgKinv k A i * qgKinv k A j)))) =
    qgE k A i * (qgKinv k A i * (qgE k A j * (qgKinv k A j * (qgE k A i * qgKinv k A i)))) := by
    -- Step 1: expose E_i·Kinv_i (innermost pair)
    conv_lhs =>
      rw [show qgE k A i * (qgE k A j * (qgE k A i *
          (qgKinv k A i * (qgKinv k A i * qgKinv k A j)))) =
        qgE k A i * (qgE k A j * ((qgE k A i * qgKinv k A i) *
          (qgKinv k A i * qgKinv k A j))) from by noncomm_ring]
      rw [qg_E_Kinv_scaled k i i, hii]
      simp only [smul_mul_assoc, mul_smul_comm]
    -- Step 2: expose E_j·Kinv_i (cross-index)
    conv_lhs =>
      rw [show (T 2 : QBase k) • (qgE k A i * (qgE k A j *
          ((qgKinv k A i * qgE k A i) * (qgKinv k A i * qgKinv k A j)))) =
        (T 2 : QBase k) • (qgE k A i * ((qgE k A j * qgKinv k A i) *
          (qgE k A i * (qgKinv k A i * qgKinv k A j)))) from by congr 1; noncomm_ring]
      rw [qg_E_Kinv_scaled k j i, h]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    -- Step 3: expose E_i·Kinv_j (cross-index, need Kinv reorder first)
    conv_lhs =>
      rw [show (T 2 * T (-1) : QBase k) • (qgE k A i *
          ((qgKinv k A i * qgE k A j) * (qgE k A i * (qgKinv k A i * qgKinv k A j)))) =
        (T 2 * T (-1) : QBase k) • (qgE k A i *
          (qgKinv k A i * qgE k A j * ((qgE k A i * qgKinv k A j) * qgKinv k A i))) from by
        congr 1; rw [qg_Kinv_Kinv_comm (A := A) k i j]; noncomm_ring]
      rw [qg_E_Kinv_scaled k i j, hsym]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    -- Cancel: T(2)*T(-1)*T(-1) = T(0) = 1
    rw [show (T 2 * T (-1) * T (-1) : QBase k) = 1 from by rw [← T_add, ← T_add]; norm_num,
        one_smul]
    noncomm_ring
  -- Right-associate h_mul to match atom helper patterns, then substitute
  simp only [mul_assoc] at h_mul
  rw [hA2, hA1, hB] at h_mul
  -- h_mul is now in dressed Serre form. Match goal.
  -- Goal has T-scalar expressions; h_mul is scalar-free after atom substitution.
  -- The goal's scalars all evaluate to T(0)=1 after Cartan substitution.
  simp only [hii, hjj] at ⊢
  norm_num at ⊢
  try simp only [T_zero, one_smul] at ⊢
  -- h_mul says A2-[2]B+A1=0, goal says -(A1)-(A2)=-(T(-1)B)-(T(1)B). Same equation.
  linear_combination (norm := module) -h_mul

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem antipodeFreeAlgQG_SerreF_quad (i j : Fin r)
    (h : A i j = -1) (hii : A i i = 2) (hsym : A j i = -1) (hjj : A j j = 2) :
    antipodeFreeAlgQG k A
      (qgI' k (.F i) * qgI' k (.F i) * qgI' k (.F j) +
       qgI' k (.F j) * qgI' k (.F i) * qgI' k (.F i)) =
    antipodeFreeAlgQG k A
      (algebraMap (QBase k) _ (T 1 + T (-1)) *
       qgI' k (.F i) * qgI' k (.F j) * qgI' k (.F i)) := by
  -- Mirror of SerreE_quad with K instead of Kinv, mulLeft instead of mulRight.
  -- Expand via AlgHom + extract from MulOpposite
  simp only [map_add, map_mul, AlgHom.commutes,
             antipodeFreeAlgQG, antipodeOnGenQG, FreeAlgebra.lift_ι_apply]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_add, MulOpposite.unop_mul,
             MulOpposite.unop_op,
             MulOpposite.algebraMap_apply, mul_assoc]
  -- Handle negation
  letI : NonUnitalNonAssocRing (QuantumGroup k A) := inferInstance
  simp only [neg_mul, mul_neg, neg_neg]
  -- Push K·F to F·K (same-index)
  simp_rw [qg_KF_scaled k (A := A) i i, qg_KF_scaled k (A := A) j j]
  -- Convert scalars + simplify
  have hcentral : ∀ (r : QBase k) (x : QuantumGroup k A),
      x * algebraMap (QBase k) (QuantumGroup k A) r = r • x :=
    fun r x => by erw [Algebra.smul_def, Algebra.commutes]
  have hcentral_left : ∀ (r : QBase k) (x : QuantumGroup k A),
      algebraMap (QBase k) (QuantumGroup k A) r * x = r • x :=
    fun r x => by rw [Algebra.smul_def]
  simp only [mul_add, mul_one, hcentral, hcentral_left]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← T_add]
  norm_num [T_zero]
  simp only [one_smul, ← mul_assoc]
  -- K·F commutation helpers
  have hKF_ii : qgK k A i * qgF k A i =
      (T (-2) : QBase k) • (qgF k A i * qgK k A i) := by
    rw [qg_KF_scaled k (A := A) i i, hii]
  have hKF_jj : qgK k A j * qgF k A j =
      (T (-2) : QBase k) • (qgF k A j * qgK k A j) := by
    rw [qg_KF_scaled k (A := A) j j, hjj]
  have hKF_ij : qgK k A i * qgF k A j =
      (T 1 : QBase k) • (qgF k A j * qgK k A i) := by
    rw [qg_KF_scaled k (A := A) i j, h]; norm_num
  have hKF_ji : qgK k A j * qgF k A i =
      (T 1 : QBase k) • (qgF k A i * qgK k A j) := by
    rw [qg_KF_scaled k (A := A) j i, hsym]; norm_num
  -- Phase 8: push K right past F in goal
  simp only [mul_assoc, hKF_ii, hKF_jj, hKF_ij, hKF_ji,
             mul_smul_comm, smul_mul_assoc, smul_smul] at ⊢
  simp only [← T_add] at ⊢
  -- Phase 9: apply pure Serre LEFT-multiplied by K chain
  have hSF := qg_SerreF_quad_smul k i j h
  have h_mul := congr_arg
    (⇑(LinearMap.mulLeft (QBase k)
        (qgK k A i * qgK k A i * qgK k A j))) hSF
  simp only [map_add, map_sub, map_zero, LinearMap.mulLeft_apply,
             LinearMap.map_smul_of_tower] at h_mul
  -- h_mul has K_chain·Serre(F) = 0. Goal has dressed Serre.
  -- Need atom helpers (same as E-side: hA2, hA1, hB) to push K RIGHT through F
  -- in h_mul, using conv_lhs + show/congr 1/noncomm_ring + hKF + scalar cancel.
  -- Then: simp only [hii, hjj, h, hsym] at h_mul ⊢; norm_num at h_mul ⊢;
  -- linear_combination (norm := module) -h_mul
  sorry

end SKEFTHawking
