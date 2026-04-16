/-
Phase 5m Wave 1 (strengthening): Instantiation Verification

Shows that the generic QuantumGroup k A recovers the hand-written definitions:
  - QuantumGroup k cartanA1  ≃ₐ  Uqsl2 k   (rank 1, type A₁)
  - QuantumGroup k cartanA2  ≃ₐ  Uqsl3 k   (rank 2, type A₂)

The equivalence is constructed by:
  1. Defining AlgHom in each direction via FreeAlgebra.lift → RingQuot.liftAlgHom
  2. Showing roundtrip = id via RingQuot.ringQuot_ext' + FreeAlgebra.hom_ext
  3. Packaging as AlgEquiv.ofAlgHom

Zero sorry. Zero axioms (beyond propext/choice/quot.sound + native_decide).
-/

import Mathlib
import SKEFTHawking.QuantumGroupGeneric
import SKEFTHawking.Uqsl2
import SKEFTHawking.Uqsl3

open LaurentPolynomial

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k]

/-! ## Part I: QuantumGroup k cartanA1 ≃ₐ Uqsl2 k -/

section A1

/-! ### Forward map: QuantumGroup k cartanA1 → Uqsl2 k -/

/-- Generator map: QGGen 1 → Uqsl2 k. -/
private def qgGenToUqsl2 : QGGen 1 → Uqsl2 k
  | .E _ => uqE k
  | .F _ => uqF k
  | .K _ => uqK k
  | .Kinv _ => uqKinv k

/-- Lift of the generator map to the free algebra. -/
private def qgA1ToUqsl2Free : FreeAlgebra (QBase k) (QGGen 1) →ₐ[QBase k] Uqsl2 k :=
  FreeAlgebra.lift (QBase k) (qgGenToUqsl2 k)

/-- The free-algebra lift respects QGRel for cartanA1. -/
private theorem qgA1ToUqsl2Free_respect :
    ∀ a b : FreeAlgebra (QBase k) (QGGen 1),
      QGRel k cartanA1 a b → qgA1ToUqsl2Free k a = qgA1ToUqsl2Free k b := by
  intro a b h
  cases h with
  | KKinv i =>
    simp only [qgA1ToUqsl2Free, FreeAlgebra.lift_ι_apply, map_mul, map_one, qgGenToUqsl2]
    exact uq_K_mul_Kinv k
  | KinvK i =>
    simp only [qgA1ToUqsl2Free, FreeAlgebra.lift_ι_apply, map_mul, map_one, qgGenToUqsl2]
    exact uq_Kinv_mul_K k
  | KK_comm i j =>
    fin_cases i <;> fin_cases j <;> rfl
  | KE i j =>
    fin_cases i <;> fin_cases j
    simp only [qgA1ToUqsl2Free, FreeAlgebra.lift_ι_apply, map_mul, qgGenToUqsl2,
      AlgHom.commutes]
    show uqK k * uqE k = algebraMap (QBase k) (Uqsl2 k) (T (cartanA1 0 0)) * uqE k * uqK k
    rw [show cartanA1 0 0 = 2 from by native_decide]
    exact uq_KE k
  | KF i j =>
    fin_cases i <;> fin_cases j
    simp only [qgA1ToUqsl2Free, FreeAlgebra.lift_ι_apply, map_mul, qgGenToUqsl2,
      AlgHom.commutes]
    show uqK k * uqF k = algebraMap (QBase k) (Uqsl2 k) (T (-(cartanA1 0 0))) * uqF k * uqK k
    rw [show -(cartanA1 0 0) = (-2 : ℤ) from by native_decide]
    exact uq_KF k
  | EF_diag i =>
    fin_cases i
    have h := uq_serre k
    rw [map_sub (algebraMap (QBase k) (Uqsl2 k))] at h
    simp only [qgA1ToUqsl2Free, map_mul, map_sub, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl2, AlgHom.commutes]
    exact h
  | EF_off i j hij =>
    fin_cases i <;> fin_cases j <;> exact absurd rfl hij
  | SerreE_comm i j _ hij =>
    fin_cases i <;> fin_cases j <;> exact absurd rfl hij
  | SerreE_quad i j hA =>
    fin_cases i <;> fin_cases j <;> simp [cartanA1] at hA
  | SerreF_comm i j _ hij =>
    fin_cases i <;> fin_cases j <;> exact absurd rfl hij
  | SerreF_quad i j hA =>
    fin_cases i <;> fin_cases j <;> simp [cartanA1] at hA

/-- The descended AlgHom: QuantumGroup k cartanA1 →ₐ Uqsl2 k. -/
noncomputable def qgA1ToUqsl2 : QuantumGroup k cartanA1 →ₐ[QBase k] Uqsl2 k :=
  RingQuot.liftAlgHom (QBase k)
    ⟨qgA1ToUqsl2Free k, qgA1ToUqsl2Free_respect k⟩

/-- Forward map sends E to E. -/
theorem qgA1ToUqsl2_E :
    qgA1ToUqsl2 k (qgE k cartanA1 0) = uqE k := by
  simp [qgA1ToUqsl2, qgE, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA1ToUqsl2Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl2]

/-- Forward map sends F to F. -/
theorem qgA1ToUqsl2_F :
    qgA1ToUqsl2 k (qgF k cartanA1 0) = uqF k := by
  simp [qgA1ToUqsl2, qgF, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA1ToUqsl2Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl2]

/-- Forward map sends K to K. -/
theorem qgA1ToUqsl2_K :
    qgA1ToUqsl2 k (qgK k cartanA1 0) = uqK k := by
  simp [qgA1ToUqsl2, qgK, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA1ToUqsl2Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl2]

/-- Forward map sends K⁻¹ to K⁻¹. -/
theorem qgA1ToUqsl2_Kinv :
    qgA1ToUqsl2 k (qgKinv k cartanA1 0) = uqKinv k := by
  simp [qgA1ToUqsl2, qgKinv, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA1ToUqsl2Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl2]

/-! ### Backward map: Uqsl2 k → QuantumGroup k cartanA1 -/

/-- Generator map: Uqsl2Gen → QuantumGroup k cartanA1. -/
private def uqsl2GenToQG : Uqsl2Gen → QuantumGroup k cartanA1
  | .E => qgE k cartanA1 0
  | .F => qgF k cartanA1 0
  | .K => qgK k cartanA1 0
  | .Kinv => qgKinv k cartanA1 0

/-- Lift of the backward generator map to the free algebra. -/
private def uqsl2ToQGA1Free :
    FreeAlgebra (QBase k) Uqsl2Gen →ₐ[QBase k] QuantumGroup k cartanA1 :=
  FreeAlgebra.lift (QBase k) (uqsl2GenToQG k)

/-- The free-algebra lift respects ChevalleyRel. -/
private theorem uqsl2ToQGA1Free_respect :
    ∀ a b : FreeAlgebra (QBase k) Uqsl2Gen,
      ChevalleyRel k a b → uqsl2ToQGA1Free k a = uqsl2ToQGA1Free k b := by
  intro a b h
  cases h with
  | KKinv =>
    simp only [uqsl2ToQGA1Free, FreeAlgebra.lift_ι_apply, map_mul, map_one, uqsl2GenToQG]
    exact qg_K_mul_Kinv k cartanA1 0
  | KinvK =>
    simp only [uqsl2ToQGA1Free, FreeAlgebra.lift_ι_apply, map_mul, map_one, uqsl2GenToQG]
    exact qg_Kinv_mul_K k cartanA1 0
  | KE =>
    simp only [uqsl2ToQGA1Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl2GenToQG,
      AlgHom.commutes]
    have h := qg_KE k cartanA1 0 0
    rw [show cartanA1 0 0 = 2 from by native_decide] at h; exact h
  | KF =>
    simp only [uqsl2ToQGA1Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl2GenToQG,
      AlgHom.commutes]
    have h := qg_KF k cartanA1 0 0
    rw [show -(cartanA1 0 0) = (-2 : ℤ) from by native_decide] at h; exact h
  | Serre =>
    have h := qg_EF_diag k cartanA1 0
    rw [map_sub (algebraMap (QBase k) (QuantumGroup k cartanA1))] at h
    simp only [uqsl2ToQGA1Free, map_mul, map_sub, FreeAlgebra.lift_ι_apply,
      uqsl2GenToQG, AlgHom.commutes]
    exact h

/-- The descended AlgHom: Uqsl2 k →ₐ QuantumGroup k cartanA1. -/
noncomputable def uqsl2ToQGA1 : Uqsl2 k →ₐ[QBase k] QuantumGroup k cartanA1 :=
  RingQuot.liftAlgHom (QBase k)
    ⟨uqsl2ToQGA1Free k, uqsl2ToQGA1Free_respect k⟩

/-- Backward map sends E to E. -/
theorem uqsl2ToQGA1_E :
    uqsl2ToQGA1 k (uqE k) = qgE k cartanA1 0 := by
  simp [uqsl2ToQGA1, uqE, uqsl2Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl2ToQGA1Free, FreeAlgebra.lift_ι_apply, uqsl2GenToQG]

/-- Backward map sends F to F. -/
theorem uqsl2ToQGA1_F :
    uqsl2ToQGA1 k (uqF k) = qgF k cartanA1 0 := by
  simp [uqsl2ToQGA1, uqF, uqsl2Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl2ToQGA1Free, FreeAlgebra.lift_ι_apply, uqsl2GenToQG]

/-- Backward map sends K to K. -/
theorem uqsl2ToQGA1_K :
    uqsl2ToQGA1 k (uqK k) = qgK k cartanA1 0 := by
  simp [uqsl2ToQGA1, uqK, uqsl2Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl2ToQGA1Free, FreeAlgebra.lift_ι_apply, uqsl2GenToQG]

/-- Backward map sends K⁻¹ to K⁻¹. -/
theorem uqsl2ToQGA1_Kinv :
    uqsl2ToQGA1 k (uqKinv k) = qgKinv k cartanA1 0 := by
  simp [uqsl2ToQGA1, uqKinv, uqsl2Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl2ToQGA1Free, FreeAlgebra.lift_ι_apply, uqsl2GenToQG]

/-! ### AlgEquiv via ext -/

/-- The backward-then-forward composition is the identity on QuantumGroup k cartanA1.
    Proof via RingQuot.ringQuot_ext' + FreeAlgebra.hom_ext. -/
private theorem qgA1_comp_id :
    (uqsl2ToQGA1 k).comp (qgA1ToUqsl2 k) = AlgHom.id (QBase k) (QuantumGroup k cartanA1) := by
  -- ext fires ringQuot_ext' then FreeAlgebra.hom_ext, giving generator cases
  ext x
  cases x with
  | E i =>
    fin_cases i
    simp [AlgHom.comp_apply, qgA1ToUqsl2, qgA1ToUqsl2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl2, uqsl2ToQGA1_E, qgE, qgMk]
  | F i =>
    fin_cases i
    simp [AlgHom.comp_apply, qgA1ToUqsl2, qgA1ToUqsl2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl2, uqsl2ToQGA1_F, qgF, qgMk]
  | K i =>
    fin_cases i
    simp [AlgHom.comp_apply, qgA1ToUqsl2, qgA1ToUqsl2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl2, uqsl2ToQGA1_K, qgK, qgMk]
  | Kinv i =>
    fin_cases i
    simp [AlgHom.comp_apply, qgA1ToUqsl2, qgA1ToUqsl2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl2, uqsl2ToQGA1_Kinv, qgKinv, qgMk]

/-- The forward-then-backward composition is the identity on Uqsl2 k. -/
private theorem uqsl2_comp_id :
    (qgA1ToUqsl2 k).comp (uqsl2ToQGA1 k) = AlgHom.id (QBase k) (Uqsl2 k) := by
  ext x
  cases x with
  | E =>
    simp [AlgHom.comp_apply, uqsl2ToQGA1, uqsl2ToQGA1Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl2GenToQG, qgA1ToUqsl2_E, uqE, uqsl2Mk]
  | F =>
    simp [AlgHom.comp_apply, uqsl2ToQGA1, uqsl2ToQGA1Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl2GenToQG, qgA1ToUqsl2_F, uqF, uqsl2Mk]
  | K =>
    simp [AlgHom.comp_apply, uqsl2ToQGA1, uqsl2ToQGA1Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl2GenToQG, qgA1ToUqsl2_K, uqK, uqsl2Mk]
  | Kinv =>
    simp [AlgHom.comp_apply, uqsl2ToQGA1, uqsl2ToQGA1Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl2GenToQG, qgA1ToUqsl2_Kinv, uqKinv, uqsl2Mk]

/-- **QuantumGroup k cartanA1 ≃ₐ Uqsl2 k**: the generic A₁ quantum group
    is isomorphic to the hand-written U_q(sl₂). -/
noncomputable def qgA1EquivUqsl2 :
    QuantumGroup k cartanA1 ≃ₐ[QBase k] Uqsl2 k :=
  AlgEquiv.ofAlgHom
    (qgA1ToUqsl2 k)
    (uqsl2ToQGA1 k)
    (uqsl2_comp_id k)
    (qgA1_comp_id k)

end A1

/-! ## Part II: QuantumGroup k cartanA2 ≃ₐ Uqsl3 k -/

section A2

/-! ### Forward map: QuantumGroup k cartanA2 → Uqsl3 k -/

/-- Generator map: QGGen 2 → Uqsl3 k. -/
private def qgGenToUqsl3 : QGGen 2 → Uqsl3 k
  | .E ⟨0, _⟩ => uq3E1 k
  | .E ⟨1, _⟩ => uq3E2 k
  | .F ⟨0, _⟩ => uq3F1 k
  | .F ⟨1, _⟩ => uq3F2 k
  | .K ⟨0, _⟩ => uq3K1 k
  | .K ⟨1, _⟩ => uq3K2 k
  | .Kinv ⟨0, _⟩ => uq3K1inv k
  | .Kinv ⟨1, _⟩ => uq3K2inv k

/-- Lift of the generator map to the free algebra. -/
private def qgA2ToUqsl3Free : FreeAlgebra (QBase k) (QGGen 2) →ₐ[QBase k] Uqsl3 k :=
  FreeAlgebra.lift (QBase k) (qgGenToUqsl3 k)

/-- The free-algebra lift respects QGRel for cartanA2.

This is the main technical lemma: each of the 11 QGRel constructor types must be
shown to hold in Uqsl3 k. For Fin 2, this expands to ~21 concrete cases matching
the hand-written ChevalleyRelSl3. Vacuous cases (no zero off-diagonal in A₂) are
discharged by contradiction. -/
private theorem qgA2ToUqsl3Free_respect :
    ∀ a b : FreeAlgebra (QBase k) (QGGen 2),
      QGRel k cartanA2 a b → qgA2ToUqsl3Free k a = qgA2ToUqsl3Free k b := by
  intro a b h
  cases h with
  | KKinv i =>
    fin_cases i <;> simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul,
      map_one, qgGenToUqsl3] <;>
    first | exact uq3_K1_mul_K1inv k | exact uq3_K2_mul_K2inv k
  | KinvK i =>
    fin_cases i <;> simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul,
      map_one, qgGenToUqsl3] <;>
    first | exact uq3_K1inv_mul_K1 k | exact uq3_K2inv_mul_K2 k
  | KK_comm i j =>
    fin_cases i <;> fin_cases j <;>
    simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul, qgGenToUqsl3] <;>
    first | rfl | exact uq3_K1K2_comm k | exact (uq3_K1K2_comm k).symm
  | KE i j =>
    fin_cases i <;> fin_cases j <;> (
      simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul, qgGenToUqsl3,
        AlgHom.commutes]
      show _ = algebraMap (QBase k) (Uqsl3 k) (T (cartanA2 _ _)) * _ * _
    ) <;> (try native_decide) <;>
    first | exact uq3_K1E1 k | exact uq3_K1E2 k | exact uq3_K2E1 k | exact uq3_K2E2 k
  | KF i j =>
    fin_cases i <;> fin_cases j <;> (
      simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul, qgGenToUqsl3,
        AlgHom.commutes]
      show _ = algebraMap (QBase k) (Uqsl3 k) (T (-(cartanA2 _ _))) * _ * _
    ) <;> (try native_decide) <;>
    first | exact uq3_K1F1 k | exact uq3_K1F2 k | exact uq3_K2F1 k | exact uq3_K2F2 k
  | EF_diag i =>
    fin_cases i <;> (
      simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul, map_sub,
        qgGenToUqsl3, AlgHom.commutes]
    )
    · -- i = 0: match uq3_EF11
      have h := uq3_EF11 k
      rw [map_sub (algebraMap (QBase k) (Uqsl3 k))] at h; exact h
    · -- i = 1: match uq3_EF22
      have h := uq3_EF22 k
      rw [map_sub (algebraMap (QBase k) (Uqsl3 k))] at h; exact h
  | EF_off i j hij =>
    fin_cases i <;> fin_cases j <;> (
      simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul, qgGenToUqsl3]
    ) <;> (try exact absurd rfl hij) <;>
    first | exact uq3_E1F2_comm k | exact uq3_E2F1_comm k
  | SerreE_comm i j hA hij =>
    -- cartanA2 has no zero off-diagonal entries (all -1), so this is vacuous
    fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl hij | (simp [cartanA2] at hA)
  | SerreE_quad i j hA =>
    fin_cases i <;> fin_cases j <;> (
      simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul, map_add, map_pow,
        qgGenToUqsl3, AlgHom.commutes]
    ) <;> (try simp [cartanA2] at hA)
    · -- (i,j) = (0,1): match SerreE12
      have h := uq3_SerreE12 k
      simp only [map_add (algebraMap (QBase k) (Uqsl3 k))] at h
      simp only [sq, ← mul_assoc]; exact h
    · -- (i,j) = (1,0): match SerreE21
      have h := uq3_SerreE21 k
      simp only [map_add (algebraMap (QBase k) (Uqsl3 k))] at h
      simp only [sq, ← mul_assoc]; exact h
  | SerreF_comm i j hA hij =>
    fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl hij | (simp [cartanA2] at hA)
  | SerreF_quad i j hA =>
    fin_cases i <;> fin_cases j <;> (
      simp only [qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, map_mul, map_add, map_pow,
        qgGenToUqsl3, AlgHom.commutes]
    ) <;> (try simp [cartanA2] at hA)
    · -- (i,j) = (0,1): match SerreF12
      have h := uq3_SerreF12 k
      simp only [map_add (algebraMap (QBase k) (Uqsl3 k))] at h
      simp only [sq, ← mul_assoc]; exact h
    · -- (i,j) = (1,0): match SerreF21
      have h := uq3_SerreF21 k
      simp only [map_add (algebraMap (QBase k) (Uqsl3 k))] at h
      simp only [sq, ← mul_assoc]; exact h

/-- The descended AlgHom: QuantumGroup k cartanA2 →ₐ Uqsl3 k. -/
noncomputable def qgA2ToUqsl3 : QuantumGroup k cartanA2 →ₐ[QBase k] Uqsl3 k :=
  RingQuot.liftAlgHom (QBase k)
    ⟨qgA2ToUqsl3Free k, qgA2ToUqsl3Free_respect k⟩

-- Forward evaluation lemmas (8 generators)
theorem qgA2ToUqsl3_E1 : qgA2ToUqsl3 k (qgE k cartanA2 0) = uq3E1 k := by
  simp [qgA2ToUqsl3, qgE, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl3]
theorem qgA2ToUqsl3_E2 : qgA2ToUqsl3 k (qgE k cartanA2 1) = uq3E2 k := by
  simp [qgA2ToUqsl3, qgE, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl3]
theorem qgA2ToUqsl3_F1 : qgA2ToUqsl3 k (qgF k cartanA2 0) = uq3F1 k := by
  simp [qgA2ToUqsl3, qgF, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl3]
theorem qgA2ToUqsl3_F2 : qgA2ToUqsl3 k (qgF k cartanA2 1) = uq3F2 k := by
  simp [qgA2ToUqsl3, qgF, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl3]
theorem qgA2ToUqsl3_K1 : qgA2ToUqsl3 k (qgK k cartanA2 0) = uq3K1 k := by
  simp [qgA2ToUqsl3, qgK, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl3]
theorem qgA2ToUqsl3_K2 : qgA2ToUqsl3 k (qgK k cartanA2 1) = uq3K2 k := by
  simp [qgA2ToUqsl3, qgK, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl3]
theorem qgA2ToUqsl3_K1inv : qgA2ToUqsl3 k (qgKinv k cartanA2 0) = uq3K1inv k := by
  simp [qgA2ToUqsl3, qgKinv, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl3]
theorem qgA2ToUqsl3_K2inv : qgA2ToUqsl3 k (qgKinv k cartanA2 1) = uq3K2inv k := by
  simp [qgA2ToUqsl3, qgKinv, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    qgA2ToUqsl3Free, FreeAlgebra.lift_ι_apply, qgGenToUqsl3]

/-! ### Backward map: Uqsl3 k → QuantumGroup k cartanA2 -/

/-- Generator map: Uqsl3Gen → QuantumGroup k cartanA2. -/
private def uqsl3GenToQG : Uqsl3Gen → QuantumGroup k cartanA2
  | .E1 => qgE k cartanA2 0
  | .E2 => qgE k cartanA2 1
  | .F1 => qgF k cartanA2 0
  | .F2 => qgF k cartanA2 1
  | .K1 => qgK k cartanA2 0
  | .K2 => qgK k cartanA2 1
  | .K1inv => qgKinv k cartanA2 0
  | .K2inv => qgKinv k cartanA2 1

/-- Lift of the backward generator map to the free algebra. -/
private def uqsl3ToQGA2Free :
    FreeAlgebra (QBase k) Uqsl3Gen →ₐ[QBase k] QuantumGroup k cartanA2 :=
  FreeAlgebra.lift (QBase k) (uqsl3GenToQG k)

/-- The free-algebra lift respects ChevalleyRelSl3. -/
private theorem uqsl3ToQGA2Free_respect :
    ∀ a b : FreeAlgebra (QBase k) Uqsl3Gen,
      ChevalleyRelSl3 k a b → uqsl3ToQGA2Free k a = uqsl3ToQGA2Free k b := by
  intro a b h
  cases h with
  | K1K1inv =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, map_one, uqsl3GenToQG]
    exact qg_K_mul_Kinv k cartanA2 0
  | K1invK1 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, map_one, uqsl3GenToQG]
    exact qg_Kinv_mul_K k cartanA2 0
  | K2K2inv =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, map_one, uqsl3GenToQG]
    exact qg_K_mul_Kinv k cartanA2 1
  | K2invK2 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, map_one, uqsl3GenToQG]
    exact qg_Kinv_mul_K k cartanA2 1
  | K1K2 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG]
    exact qg_KK_comm k cartanA2 0 1
  | K1E1 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG,
      AlgHom.commutes]
    have h := qg_KE k cartanA2 0 0
    rw [show cartanA2 0 0 = 2 from by native_decide] at h; exact h
  | K1E2 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG,
      AlgHom.commutes]
    have h := qg_KE k cartanA2 0 1
    rw [show cartanA2 0 1 = -1 from by native_decide] at h; exact h
  | K2E1 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG,
      AlgHom.commutes]
    have h := qg_KE k cartanA2 1 0
    rw [show cartanA2 1 0 = -1 from by native_decide] at h; exact h
  | K2E2 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG,
      AlgHom.commutes]
    have h := qg_KE k cartanA2 1 1
    rw [show cartanA2 1 1 = 2 from by native_decide] at h; exact h
  | K1F1 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG,
      AlgHom.commutes]
    have h := qg_KF k cartanA2 0 0
    rw [show -(cartanA2 0 0) = (-2 : ℤ) from by native_decide] at h; exact h
  | K1F2 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG,
      AlgHom.commutes]
    have h := qg_KF k cartanA2 0 1
    rw [show -(cartanA2 0 1) = (1 : ℤ) from by native_decide] at h; exact h
  | K2F1 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG,
      AlgHom.commutes]
    have h := qg_KF k cartanA2 1 0
    rw [show -(cartanA2 1 0) = (1 : ℤ) from by native_decide] at h; exact h
  | K2F2 =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG,
      AlgHom.commutes]
    have h := qg_KF k cartanA2 1 1
    rw [show -(cartanA2 1 1) = (-2 : ℤ) from by native_decide] at h; exact h
  | EF11 =>
    have h := qg_EF_diag k cartanA2 0
    rw [map_sub (algebraMap (QBase k) (QuantumGroup k cartanA2))] at h
    simp only [uqsl3ToQGA2Free, map_mul, map_sub, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, AlgHom.commutes]
    exact h
  | EF22 =>
    have h := qg_EF_diag k cartanA2 1
    rw [map_sub (algebraMap (QBase k) (QuantumGroup k cartanA2))] at h
    simp only [uqsl3ToQGA2Free, map_mul, map_sub, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, AlgHom.commutes]
    exact h
  | E1F2comm =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG]
    exact qg_EF_off k cartanA2 0 1 (by decide)
  | E2F1comm =>
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, uqsl3GenToQG]
    exact qg_EF_off k cartanA2 1 0 (by decide)
  | SerreE12 =>
    have h := qg_SerreE_quad k cartanA2 0 1 (by native_decide : cartanA2 0 1 = -1)
    simp only [map_add (algebraMap (QBase k) (QuantumGroup k cartanA2)), sq, ← mul_assoc] at h
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, map_add,
      uqsl3GenToQG, AlgHom.commutes]
    exact h
  | SerreE21 =>
    have h := qg_SerreE_quad k cartanA2 1 0 (by native_decide : cartanA2 1 0 = -1)
    simp only [map_add (algebraMap (QBase k) (QuantumGroup k cartanA2)), sq, ← mul_assoc] at h
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, map_add,
      uqsl3GenToQG, AlgHom.commutes]
    exact h
  | SerreF12 =>
    have h := qg_SerreF_quad k cartanA2 0 1 (by native_decide : cartanA2 0 1 = -1)
    simp only [map_add (algebraMap (QBase k) (QuantumGroup k cartanA2)), sq, ← mul_assoc] at h
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, map_add,
      uqsl3GenToQG, AlgHom.commutes]
    exact h
  | SerreF21 =>
    have h := qg_SerreF_quad k cartanA2 1 0 (by native_decide : cartanA2 1 0 = -1)
    simp only [map_add (algebraMap (QBase k) (QuantumGroup k cartanA2)), sq, ← mul_assoc] at h
    simp only [uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, map_mul, map_add,
      uqsl3GenToQG, AlgHom.commutes]
    exact h

/-- The descended AlgHom: Uqsl3 k →ₐ QuantumGroup k cartanA2. -/
noncomputable def uqsl3ToQGA2 : Uqsl3 k →ₐ[QBase k] QuantumGroup k cartanA2 :=
  RingQuot.liftAlgHom (QBase k)
    ⟨uqsl3ToQGA2Free k, uqsl3ToQGA2Free_respect k⟩

-- Backward evaluation lemmas (8 generators)
theorem uqsl3ToQGA2_E1 : uqsl3ToQGA2 k (uq3E1 k) = qgE k cartanA2 0 := by
  simp [uqsl3ToQGA2, uq3E1, uqsl3Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, uqsl3GenToQG]
theorem uqsl3ToQGA2_E2 : uqsl3ToQGA2 k (uq3E2 k) = qgE k cartanA2 1 := by
  simp [uqsl3ToQGA2, uq3E2, uqsl3Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, uqsl3GenToQG]
theorem uqsl3ToQGA2_F1 : uqsl3ToQGA2 k (uq3F1 k) = qgF k cartanA2 0 := by
  simp [uqsl3ToQGA2, uq3F1, uqsl3Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, uqsl3GenToQG]
theorem uqsl3ToQGA2_F2 : uqsl3ToQGA2 k (uq3F2 k) = qgF k cartanA2 1 := by
  simp [uqsl3ToQGA2, uq3F2, uqsl3Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, uqsl3GenToQG]
theorem uqsl3ToQGA2_K1 : uqsl3ToQGA2 k (uq3K1 k) = qgK k cartanA2 0 := by
  simp [uqsl3ToQGA2, uq3K1, uqsl3Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, uqsl3GenToQG]
theorem uqsl3ToQGA2_K2 : uqsl3ToQGA2 k (uq3K2 k) = qgK k cartanA2 1 := by
  simp [uqsl3ToQGA2, uq3K2, uqsl3Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, uqsl3GenToQG]
theorem uqsl3ToQGA2_K1inv : uqsl3ToQGA2 k (uq3K1inv k) = qgKinv k cartanA2 0 := by
  simp [uqsl3ToQGA2, uq3K1inv, uqsl3Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, uqsl3GenToQG]
theorem uqsl3ToQGA2_K2inv : uqsl3ToQGA2 k (uq3K2inv k) = qgKinv k cartanA2 1 := by
  simp [uqsl3ToQGA2, uq3K2inv, uqsl3Mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    uqsl3ToQGA2Free, FreeAlgebra.lift_ι_apply, uqsl3GenToQG]

/-! ### AlgEquiv via ext -/

private theorem qgA2_comp_id :
    (uqsl3ToQGA2 k).comp (qgA2ToUqsl3 k) =
    AlgHom.id (QBase k) (QuantumGroup k cartanA2) := by
  ext x
  cases x with
  | E i =>
    fin_cases i <;> simp [AlgHom.comp_apply, qgA2ToUqsl3, qgA2ToUqsl3Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl3, uqsl3ToQGA2_E1, uqsl3ToQGA2_E2, qgE, qgMk]
  | F i =>
    fin_cases i <;> simp [AlgHom.comp_apply, qgA2ToUqsl3, qgA2ToUqsl3Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl3, uqsl3ToQGA2_F1, uqsl3ToQGA2_F2, qgF, qgMk]
  | K i =>
    fin_cases i <;> simp [AlgHom.comp_apply, qgA2ToUqsl3, qgA2ToUqsl3Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl3, uqsl3ToQGA2_K1, uqsl3ToQGA2_K2, qgK, qgMk]
  | Kinv i =>
    fin_cases i <;> simp [AlgHom.comp_apply, qgA2ToUqsl3, qgA2ToUqsl3Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      qgGenToUqsl3, uqsl3ToQGA2_K1inv, uqsl3ToQGA2_K2inv, qgKinv, qgMk]

private theorem uqsl3_comp_id :
    (qgA2ToUqsl3 k).comp (uqsl3ToQGA2 k) = AlgHom.id (QBase k) (Uqsl3 k) := by
  ext x
  cases x with
  | E1 => simp [AlgHom.comp_apply, uqsl3ToQGA2, uqsl3ToQGA2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, qgA2ToUqsl3_E1, uq3E1, uqsl3Mk]
  | E2 => simp [AlgHom.comp_apply, uqsl3ToQGA2, uqsl3ToQGA2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, qgA2ToUqsl3_E2, uq3E2, uqsl3Mk]
  | F1 => simp [AlgHom.comp_apply, uqsl3ToQGA2, uqsl3ToQGA2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, qgA2ToUqsl3_F1, uq3F1, uqsl3Mk]
  | F2 => simp [AlgHom.comp_apply, uqsl3ToQGA2, uqsl3ToQGA2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, qgA2ToUqsl3_F2, uq3F2, uqsl3Mk]
  | K1 => simp [AlgHom.comp_apply, uqsl3ToQGA2, uqsl3ToQGA2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, qgA2ToUqsl3_K1, uq3K1, uqsl3Mk]
  | K2 => simp [AlgHom.comp_apply, uqsl3ToQGA2, uqsl3ToQGA2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, qgA2ToUqsl3_K2, uq3K2, uqsl3Mk]
  | K1inv => simp [AlgHom.comp_apply, uqsl3ToQGA2, uqsl3ToQGA2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, qgA2ToUqsl3_K1inv, uq3K1inv, uqsl3Mk]
  | K2inv => simp [AlgHom.comp_apply, uqsl3ToQGA2, uqsl3ToQGA2Free,
      RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply,
      uqsl3GenToQG, qgA2ToUqsl3_K2inv, uq3K2inv, uqsl3Mk]

/-- **QuantumGroup k cartanA2 ≃ₐ Uqsl3 k**: the generic A₂ quantum group
    is isomorphic to the hand-written U_q(sl₃). -/
noncomputable def qgA2EquivUqsl3 :
    QuantumGroup k cartanA2 ≃ₐ[QBase k] Uqsl3 k :=
  AlgEquiv.ofAlgHom
    (qgA2ToUqsl3 k)
    (uqsl3ToQGA2 k)
    (uqsl3_comp_id k)
    (qgA2_comp_id k)

end A2

/-! ## Module Summary -/

/--
QuantumGroupInstantiation: verifies the generic U_q(𝔤) framework recovers
hand-written quantum groups.
  - QuantumGroup k cartanA1 ≃ₐ Uqsl2 k (4-generator bijection, full AlgEquiv)
  - QuantumGroup k cartanA2 ≃ₐ Uqsl3 k (8-generator bijection, full AlgEquiv)
  - All generator evaluations verified (forward and backward)
  - Roundtrip proofs via RingQuot.ringQuot_ext' + FreeAlgebra.hom_ext
  - Zero sorry.
-/
theorem quantum_group_instantiation_summary : True := trivial

end SKEFTHawking
