/-
Phase 5i Wave 2: U_q(sl₃) Hopf Algebra Structure

Wires the coproduct Δ, counit ε, and antipode S into Mathlib's
Bialgebra and HopfAlgebra typeclasses for U_q(sl₃).

Coproduct (on generators, extended as algebra homomorphism):
  Δ(E_i) = E_i ⊗ K_i + 1 ⊗ E_i
  Δ(F_i) = F_i ⊗ 1 + K_i⁻¹ ⊗ F_i
  Δ(K_i) = K_i ⊗ K_i,  Δ(K_i⁻¹) = K_i⁻¹ ⊗ K_i⁻¹

Counit: ε(E_i) = ε(F_i) = 0, ε(K_i) = ε(K_i⁻¹) = 1

Antipode (algebra anti-homomorphism):
  S(K_i) = K_i⁻¹,  S(K_i⁻¹) = K_i
  S(E_i) = −E_i K_i⁻¹,  S(F_i) = −K_i F_i

Same architecture as Uqsl2Hopf.lean. 21 relation-respect proofs for each map.

References:
  Kassel, "Quantum Groups" (Springer, 1995), Ch. VI
  Lit-Search/Phase-5j/U_q(sl_3) complete technical specification...
-/

import Mathlib
import SKEFTHawking.Uqsl3

open LaurentPolynomial TensorProduct

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k]

-- Local copies of private helpers from Uqsl3
private abbrev scal3' (r : LaurentPolynomial k) :
    FreeAlgebra (LaurentPolynomial k) Uqsl3Gen :=
  algebraMap (LaurentPolynomial k) (FreeAlgebra (LaurentPolynomial k) Uqsl3Gen) r

private abbrev gen3 (x : Uqsl3Gen) : FreeAlgebra (LaurentPolynomial k) Uqsl3Gen :=
  FreeAlgebra.ι (LaurentPolynomial k) x

-- Tensor product Ring instance
noncomputable instance uq3TensorRing :
    Ring ((Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) :=
  @Algebra.TensorProduct.instRing (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) _ _ _ _ _

/-! ## 1. Coproduct Δ -/

/-- Coproduct on generators of U_q(sl₃).
  Δ(E_i) = E_i ⊗ K_i + 1 ⊗ E_i
  Δ(F_i) = F_i ⊗ 1 + K_i⁻¹ ⊗ F_i
  Δ(K_i) = K_i ⊗ K_i,  Δ(K_i⁻¹) = K_i⁻¹ ⊗ K_i⁻¹ -/
private def comulOnGen3 : Uqsl3Gen → (Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)
  | .E1    => uq3E1 k ⊗ₜ uq3K1 k + 1 ⊗ₜ uq3E1 k
  | .E2    => uq3E2 k ⊗ₜ uq3K2 k + 1 ⊗ₜ uq3E2 k
  | .F1    => uq3F1 k ⊗ₜ 1 + uq3K1inv k ⊗ₜ uq3F1 k
  | .F2    => uq3F2 k ⊗ₜ 1 + uq3K2inv k ⊗ₜ uq3F2 k
  | .K1    => uq3K1 k ⊗ₜ uq3K1 k
  | .K1inv => uq3K1inv k ⊗ₜ uq3K1inv k
  | .K2    => uq3K2 k ⊗ₜ uq3K2 k
  | .K2inv => uq3K2inv k ⊗ₜ uq3K2inv k

/-- Coproduct lifted to the free algebra. -/
private def comulFreeAlg3 :
    FreeAlgebra (LaurentPolynomial k) Uqsl3Gen →ₐ[LaurentPolynomial k]
    (Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k) :=
  FreeAlgebra.lift (LaurentPolynomial k) (comulOnGen3 k)

/-- comulFreeAlg3 on a generator equals comulOnGen3. -/
private theorem comulFreeAlg3_ι (x : Uqsl3Gen) :
    comulFreeAlg3 k (FreeAlgebra.ι (LaurentPolynomial k) x) = comulOnGen3 k x := by
  unfold comulFreeAlg3; exact FreeAlgebra.lift_ι_apply _ _

set_option backward.isDefEq.respectTransparency false in
noncomputable instance uq3Tensor_intScalarTower :
    IsScalarTower ℤ (LaurentPolynomial k)
      (Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k) :=
  IsScalarTower.of_algebraMap_smul (fun r x => by
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul])

set_option backward.isDefEq.respectTransparency false in
noncomputable instance uq3Laurent_intAlgebra :
    Algebra ℤ (LaurentPolynomial k) := inferInstance

/-! ### Derived commutation lemmas (cross-index K/K⁻¹ commutations) -/

open Uqsl3Gen

/-- K₁·K₂⁻¹ = K₂⁻¹·K₁ (derived from K₁K₂ = K₂K₁ + K-invertibility). -/
private theorem uq3_K1_K2inv_comm : uq3K1 k * uq3K2inv k = uq3K2inv k * uq3K1 k := by
  have h := uq3_K1K2_comm k
  calc uq3K1 k * uq3K2inv k
      = uq3K2inv k * uq3K2 k * uq3K1 k * uq3K2inv k := by
        rw [uq3_K2inv_mul_K2, one_mul]
    _ = uq3K2inv k * (uq3K2 k * uq3K1 k) * uq3K2inv k := by noncomm_ring
    _ = uq3K2inv k * (uq3K1 k * uq3K2 k) * uq3K2inv k := by rw [← h]
    _ = uq3K2inv k * uq3K1 k * (uq3K2 k * uq3K2inv k) := by noncomm_ring
    _ = uq3K2inv k * uq3K1 k := by rw [uq3_K2_mul_K2inv, mul_one]

/-- K₂·K₁⁻¹ = K₁⁻¹·K₂. -/
private theorem uq3_K2_K1inv_comm : uq3K2 k * uq3K1inv k = uq3K1inv k * uq3K2 k := by
  have h := uq3_K1K2_comm k
  calc uq3K2 k * uq3K1inv k
      = uq3K1inv k * uq3K1 k * uq3K2 k * uq3K1inv k := by
        rw [uq3_K1inv_mul_K1, one_mul]
    _ = uq3K1inv k * (uq3K1 k * uq3K2 k) * uq3K1inv k := by noncomm_ring
    _ = uq3K1inv k * (uq3K2 k * uq3K1 k) * uq3K1inv k := by rw [h]
    _ = uq3K1inv k * uq3K2 k * (uq3K1 k * uq3K1inv k) := by noncomm_ring
    _ = uq3K1inv k * uq3K2 k := by rw [uq3_K1_mul_K1inv, mul_one]

/-- K₁⁻¹·K₂⁻¹ = K₂⁻¹·K₁⁻¹. -/
private theorem uq3_K1inv_K2inv_comm : uq3K1inv k * uq3K2inv k = uq3K2inv k * uq3K1inv k := by
  -- Multiply on the left by K₁·K₂ and use K₁K₂ = K₂K₁ plus invertibility.
  have hlcancel : uq3K1 k * uq3K2 k * (uq3K1inv k * uq3K2inv k) = 1 := by
    rw [uq3_K1K2_comm]
    rw [mul_assoc, ← mul_assoc (uq3K1 k) (uq3K1inv k), uq3_K1_mul_K1inv, one_mul,
        uq3_K2_mul_K2inv]
  have hrcancel : uq3K1 k * uq3K2 k * (uq3K2inv k * uq3K1inv k) = 1 := by
    rw [mul_assoc, ← mul_assoc (uq3K2 k) (uq3K2inv k), uq3_K2_mul_K2inv, one_mul,
        uq3_K1_mul_K1inv]
  -- Both (K₁⁻¹·K₂⁻¹) and (K₂⁻¹·K₁⁻¹) are right-inverses of K₁·K₂; right inverses
  -- in a ring are equal when a left inverse exists.
  have hLinv : uq3K2inv k * uq3K1inv k * (uq3K1 k * uq3K2 k) = 1 := by
    rw [show uq3K2inv k * uq3K1inv k * (uq3K1 k * uq3K2 k) =
          uq3K2inv k * (uq3K1inv k * uq3K1 k) * uq3K2 k from by noncomm_ring,
        uq3_K1inv_mul_K1, mul_one, uq3_K2inv_mul_K2]
  -- If c * a = 1 and a * b = 1 and a * b' = 1 then b = b'.
  calc uq3K1inv k * uq3K2inv k
      = 1 * (uq3K1inv k * uq3K2inv k) := (one_mul _).symm
    _ = uq3K2inv k * uq3K1inv k * (uq3K1 k * uq3K2 k) * (uq3K1inv k * uq3K2inv k) := by
        rw [hLinv]
    _ = uq3K2inv k * uq3K1inv k * (uq3K1 k * uq3K2 k * (uq3K1inv k * uq3K2inv k)) := by
        noncomm_ring
    _ = uq3K2inv k * uq3K1inv k * 1 := by rw [hlcancel]
    _ = uq3K2inv k * uq3K1inv k := mul_one _

/-! ### Derived E·K⁻¹ and K⁻¹·F commutations -/

/-- General pattern: from `K_i · E_j = q^a · E_j · K_i`, derive `E_j · K_i⁻¹ = q^a · K_i⁻¹ · E_j`. -/
private theorem uq3_E1_mul_K1inv :
    uq3E1 k * uq3K1inv k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3K1inv k * uq3E1 k := by
  have h := uq3_K1E1 k
  calc uq3E1 k * uq3K1inv k
      = uq3K1inv k * uq3K1 k * uq3E1 k * uq3K1inv k := by
        rw [uq3_K1inv_mul_K1, one_mul]
    _ = uq3K1inv k * (uq3K1 k * uq3E1 k) * uq3K1inv k := by noncomm_ring
    _ = uq3K1inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3E1 k * uq3K1 k) *
          uq3K1inv k := by rw [h]
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
          (uq3K1inv k * uq3E1 k) * (uq3K1 k * uq3K1inv k) := by
        rw [show uq3K1inv k *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3E1 k * uq3K1 k) =
              uq3K1inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
                uq3E1 k * uq3K1 k from by noncomm_ring,
            show uq3K1inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) =
              algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3K1inv k from
              (Algebra.commutes _ _).symm]
        noncomm_ring
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3K1inv k * uq3E1 k := by
        rw [uq3_K1_mul_K1inv, mul_one]; noncomm_ring

private theorem uq3_E2_mul_K2inv :
    uq3E2 k * uq3K2inv k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3K2inv k * uq3E2 k := by
  have h := uq3_K2E2 k
  calc uq3E2 k * uq3K2inv k
      = uq3K2inv k * uq3K2 k * uq3E2 k * uq3K2inv k := by
        rw [uq3_K2inv_mul_K2, one_mul]
    _ = uq3K2inv k * (uq3K2 k * uq3E2 k) * uq3K2inv k := by noncomm_ring
    _ = uq3K2inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3E2 k * uq3K2 k) *
          uq3K2inv k := by rw [h]
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
          (uq3K2inv k * uq3E2 k) * (uq3K2 k * uq3K2inv k) := by
        rw [show uq3K2inv k *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3E2 k * uq3K2 k) =
              uq3K2inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
                uq3E2 k * uq3K2 k from by noncomm_ring,
            show uq3K2inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) =
              algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3K2inv k from
              (Algebra.commutes _ _).symm]
        noncomm_ring
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3K2inv k * uq3E2 k := by
        rw [uq3_K2_mul_K2inv, mul_one]; noncomm_ring

private theorem uq3_E1_mul_K2inv :
    uq3E1 k * uq3K2inv k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3K2inv k * uq3E1 k := by
  have h := uq3_K2E1 k
  calc uq3E1 k * uq3K2inv k
      = uq3K2inv k * uq3K2 k * uq3E1 k * uq3K2inv k := by
        rw [uq3_K2inv_mul_K2, one_mul]
    _ = uq3K2inv k * (uq3K2 k * uq3E1 k) * uq3K2inv k := by noncomm_ring
    _ = uq3K2inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3E1 k * uq3K2 k) *
          uq3K2inv k := by rw [h]
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
          (uq3K2inv k * uq3E1 k) * (uq3K2 k * uq3K2inv k) := by
        rw [show uq3K2inv k *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3E1 k * uq3K2 k) =
              uq3K2inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
                uq3E1 k * uq3K2 k from by noncomm_ring,
            show uq3K2inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) =
              algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3K2inv k from
              (Algebra.commutes _ _).symm]
        noncomm_ring
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3K2inv k * uq3E1 k := by
        rw [uq3_K2_mul_K2inv, mul_one]; noncomm_ring

private theorem uq3_E2_mul_K1inv :
    uq3E2 k * uq3K1inv k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3K1inv k * uq3E2 k := by
  have h := uq3_K1E2 k
  calc uq3E2 k * uq3K1inv k
      = uq3K1inv k * uq3K1 k * uq3E2 k * uq3K1inv k := by
        rw [uq3_K1inv_mul_K1, one_mul]
    _ = uq3K1inv k * (uq3K1 k * uq3E2 k) * uq3K1inv k := by noncomm_ring
    _ = uq3K1inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3E2 k * uq3K1 k) *
          uq3K1inv k := by rw [h]
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
          (uq3K1inv k * uq3E2 k) * (uq3K1 k * uq3K1inv k) := by
        rw [show uq3K1inv k *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3E2 k * uq3K1 k) =
              uq3K1inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
                uq3E2 k * uq3K1 k from by noncomm_ring,
            show uq3K1inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) =
              algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3K1inv k from
              (Algebra.commutes _ _).symm]
        noncomm_ring
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3K1inv k * uq3E2 k := by
        rw [uq3_K1_mul_K1inv, mul_one]; noncomm_ring

private theorem uq3_K1inv_mul_F1 :
    uq3K1inv k * uq3F1 k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3F1 k * uq3K1inv k := by
  have h := uq3_K1F1 k
  calc uq3K1inv k * uq3F1 k
      = uq3K1inv k * uq3F1 k * uq3K1 k * uq3K1inv k := by
        rw [mul_assoc (uq3K1inv k * uq3F1 k), uq3_K1_mul_K1inv, mul_one]
    _ = uq3K1inv k * (uq3F1 k * uq3K1 k) * uq3K1inv k := by noncomm_ring
    _ = uq3K1inv k *
          (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
            (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2)) * uq3F1 k * uq3K1 k)) *
          uq3K1inv k := by
        have hT : algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
                  algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2)) = 1 := by
          rw [← map_mul, ← T_add]; norm_num
        rw [show algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2)) * uq3F1 k * uq3K1 k) =
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
                algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2))) * uq3F1 k * uq3K1 k from by
            noncomm_ring,
            hT, one_mul]
    _ = uq3K1inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
          (uq3K1 k * uq3F1 k)) * uq3K1inv k := by rw [← h]
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
          (uq3K1inv k * uq3K1 k) * uq3F1 k * uq3K1inv k := by
        rw [show uq3K1inv k *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * (uq3K1 k * uq3F1 k)) =
              uq3K1inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
                uq3K1 k * uq3F1 k from by noncomm_ring,
            show uq3K1inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) =
              algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3K1inv k from
              (Algebra.commutes _ _).symm]
        noncomm_ring
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3F1 k * uq3K1inv k := by
        rw [uq3_K1inv_mul_K1, mul_one]

private theorem uq3_K2inv_mul_F2 :
    uq3K2inv k * uq3F2 k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3F2 k * uq3K2inv k := by
  have h := uq3_K2F2 k
  calc uq3K2inv k * uq3F2 k
      = uq3K2inv k * uq3F2 k * uq3K2 k * uq3K2inv k := by
        rw [mul_assoc (uq3K2inv k * uq3F2 k), uq3_K2_mul_K2inv, mul_one]
    _ = uq3K2inv k * (uq3F2 k * uq3K2 k) * uq3K2inv k := by noncomm_ring
    _ = uq3K2inv k *
          (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
            (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2)) * uq3F2 k * uq3K2 k)) *
          uq3K2inv k := by
        have hT : algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
                  algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2)) = 1 := by
          rw [← map_mul, ← T_add]; norm_num
        rw [show algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2)) * uq3F2 k * uq3K2 k) =
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
                algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2))) * uq3F2 k * uq3K2 k from by
            noncomm_ring,
            hT, one_mul]
    _ = uq3K2inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
          (uq3K2 k * uq3F2 k)) * uq3K2inv k := by rw [← h]
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
          (uq3K2inv k * uq3K2 k) * uq3F2 k * uq3K2inv k := by
        rw [show uq3K2inv k *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * (uq3K2 k * uq3F2 k)) =
              uq3K2inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) *
                uq3K2 k * uq3F2 k from by noncomm_ring,
            show uq3K2inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) =
              algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3K2inv k from
              (Algebra.commutes _ _).symm]
        noncomm_ring
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2) * uq3F2 k * uq3K2inv k := by
        rw [uq3_K2inv_mul_K2, mul_one]

private theorem uq3_K1inv_mul_F2 :
    uq3K1inv k * uq3F2 k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3F2 k * uq3K1inv k := by
  have h := uq3_K1F2 k
  calc uq3K1inv k * uq3F2 k
      = uq3K1inv k * uq3F2 k * uq3K1 k * uq3K1inv k := by
        rw [mul_assoc (uq3K1inv k * uq3F2 k), uq3_K1_mul_K1inv, mul_one]
    _ = uq3K1inv k * (uq3F2 k * uq3K1 k) * uq3K1inv k := by noncomm_ring
    _ = uq3K1inv k *
          (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
            (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1) * uq3F2 k * uq3K1 k)) *
          uq3K1inv k := by
        have hT : algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
                  algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1) = 1 := by
          rw [← map_mul, ← T_add]; norm_num
        rw [show algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1) * uq3F2 k * uq3K1 k) =
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
                algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1)) * uq3F2 k * uq3K1 k from by
            noncomm_ring,
            hT, one_mul]
    _ = uq3K1inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
          (uq3K1 k * uq3F2 k)) * uq3K1inv k := by rw [← h]
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
          (uq3K1inv k * uq3K1 k) * uq3F2 k * uq3K1inv k := by
        rw [show uq3K1inv k *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * (uq3K1 k * uq3F2 k)) =
              uq3K1inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
                uq3K1 k * uq3F2 k from by noncomm_ring,
            show uq3K1inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) =
              algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3K1inv k from
              (Algebra.commutes _ _).symm]
        noncomm_ring
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3F2 k * uq3K1inv k := by
        rw [uq3_K1inv_mul_K1, mul_one]

private theorem uq3_K2inv_mul_F1 :
    uq3K2inv k * uq3F1 k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3F1 k * uq3K2inv k := by
  have h := uq3_K2F1 k
  calc uq3K2inv k * uq3F1 k
      = uq3K2inv k * uq3F1 k * uq3K2 k * uq3K2inv k := by
        rw [mul_assoc (uq3K2inv k * uq3F1 k), uq3_K2_mul_K2inv, mul_one]
    _ = uq3K2inv k * (uq3F1 k * uq3K2 k) * uq3K2inv k := by noncomm_ring
    _ = uq3K2inv k *
          (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
            (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1) * uq3F1 k * uq3K2 k)) *
          uq3K2inv k := by
        have hT : algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
                  algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1) = 1 := by
          rw [← map_mul, ← T_add]; norm_num
        rw [show algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1) * uq3F1 k * uq3K2 k) =
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
                algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1)) * uq3F1 k * uq3K2 k from by
            noncomm_ring,
            hT, one_mul]
    _ = uq3K2inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
          (uq3K2 k * uq3F1 k)) * uq3K2inv k := by rw [← h]
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
          (uq3K2inv k * uq3K2 k) * uq3F1 k * uq3K2inv k := by
        rw [show uq3K2inv k *
              (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * (uq3K2 k * uq3F1 k)) =
              uq3K2inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) *
                uq3K2 k * uq3F1 k from by noncomm_ring,
            show uq3K2inv k * algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) =
              algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3K2inv k from
              (Algebra.commutes _ _).symm]
        noncomm_ring
    _ = algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1)) * uq3F1 k * uq3K2inv k := by
        rw [uq3_K2inv_mul_K2, mul_one]

/-- F_i · K_j⁻¹ commutations (derived from K_j · F_i relations). -/
private theorem uq3_F1_mul_K2inv :
    uq3F1 k * uq3K2inv k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1) * uq3K2inv k * uq3F1 k := by
  -- From K₂·F₁ = T(1)·F₁·K₂, derive F₁·K₂⁻¹ = T(1)·K₂⁻¹·F₁.
  have h : uq3K2 k * uq3F1 k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F1 k * uq3K2 k := uq3_K2F1 k
  calc uq3F1 k * uq3K2inv k
      = (uq3K2inv k * uq3K2 k) * uq3F1 k * uq3K2inv k := by
        rw [uq3_K2inv_mul_K2, one_mul]
    _ = uq3K2inv k * (uq3K2 k * uq3F1 k) * uq3K2inv k := by noncomm_ring
    _ = uq3K2inv k * ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F1 k *
          uq3K2 k) * uq3K2inv k := by rw [h]
    _ = (uq3K2inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1)) * uq3F1 k *
          (uq3K2 k * uq3K2inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3K2inv k * uq3F1 k *
          (uq3K2 k * uq3K2inv k) := by
        rw [(Algebra.commutes (R := LaurentPolynomial k) (A := Uqsl3 k)
              (T 1) (uq3K2inv k)).symm]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3K2inv k * uq3F1 k * 1 := by
        rw [uq3_K2_mul_K2inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3K2inv k * uq3F1 k := mul_one _

private theorem uq3_F2_mul_K1inv :
    uq3F2 k * uq3K1inv k =
    algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1) * uq3K1inv k * uq3F2 k := by
  have h : uq3K1 k * uq3F2 k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F2 k * uq3K1 k := uq3_K1F2 k
  calc uq3F2 k * uq3K1inv k
      = (uq3K1inv k * uq3K1 k) * uq3F2 k * uq3K1inv k := by
        rw [uq3_K1inv_mul_K1, one_mul]
    _ = uq3K1inv k * (uq3K1 k * uq3F2 k) * uq3K1inv k := by noncomm_ring
    _ = uq3K1inv k * ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F2 k *
          uq3K1 k) * uq3K1inv k := by rw [h]
    _ = (uq3K1inv k * (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1)) * uq3F2 k *
          (uq3K1 k * uq3K1inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3K1inv k * uq3F2 k *
          (uq3K1 k * uq3K1inv k) := by
        rw [(Algebra.commutes (R := LaurentPolynomial k) (A := Uqsl3 k)
              (T 1) (uq3K1inv k)).symm]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3K1inv k * uq3F2 k * 1 := by
        rw [uq3_K1_mul_K1inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3K1inv k * uq3F2 k := mul_one _

/-! ### Per-relation coproduct helpers (21 Chevalley relations) -/

/- Group I: K-invertibility (4 helpers) -/

private theorem comulFreeAlg3_K1K1inv :
    comulFreeAlg3 k (gen3 k K1 * gen3 k K1inv) =
    (1 : (Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) := by
  have h : comulFreeAlg3 k (gen3 k K1) * comulFreeAlg3 k (gen3 k K1inv) = 1 ⊗ₜ 1 := by
    erw [comulFreeAlg3_ι, comulFreeAlg3_ι, Algebra.TensorProduct.tmul_mul_tmul]
    rw [uq3_K1_mul_K1inv]
  convert h using 1
  exact map_mul _ _ _

private theorem comulFreeAlg3_K1invK1 :
    comulFreeAlg3 k (gen3 k K1inv * gen3 k K1) =
    (1 : (Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) := by
  have h : comulFreeAlg3 k (gen3 k K1inv) * comulFreeAlg3 k (gen3 k K1) = 1 ⊗ₜ 1 := by
    erw [comulFreeAlg3_ι, comulFreeAlg3_ι, Algebra.TensorProduct.tmul_mul_tmul]
    rw [uq3_K1inv_mul_K1]
  convert h using 1
  exact map_mul _ _ _

private theorem comulFreeAlg3_K2K2inv :
    comulFreeAlg3 k (gen3 k K2 * gen3 k K2inv) =
    (1 : (Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) := by
  have h : comulFreeAlg3 k (gen3 k K2) * comulFreeAlg3 k (gen3 k K2inv) = 1 ⊗ₜ 1 := by
    erw [comulFreeAlg3_ι, comulFreeAlg3_ι, Algebra.TensorProduct.tmul_mul_tmul]
    rw [uq3_K2_mul_K2inv]
  convert h using 1
  exact map_mul _ _ _

private theorem comulFreeAlg3_K2invK2 :
    comulFreeAlg3 k (gen3 k K2inv * gen3 k K2) =
    (1 : (Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) := by
  have h : comulFreeAlg3 k (gen3 k K2inv) * comulFreeAlg3 k (gen3 k K2) = 1 ⊗ₜ 1 := by
    erw [comulFreeAlg3_ι, comulFreeAlg3_ι, Algebra.TensorProduct.tmul_mul_tmul]
    rw [uq3_K2inv_mul_K2]
  convert h using 1
  exact map_mul _ _ _

/- Group II: K-commutativity (1 helper) -/

private theorem comulFreeAlg3_K1K2 :
    comulFreeAlg3 k (gen3 k K1 * gen3 k K2) =
    comulFreeAlg3 k (gen3 k K2 * gen3 k K1) := by
  have hL : comulFreeAlg3 k (gen3 k K1 * gen3 k K2) =
            (uq3K1 k * uq3K2 k) ⊗ₜ (uq3K1 k * uq3K2 k) := by
    rw [map_mul]; erw [comulFreeAlg3_ι, comulFreeAlg3_ι, Algebra.TensorProduct.tmul_mul_tmul]
  have hR : comulFreeAlg3 k (gen3 k K2 * gen3 k K1) =
            (uq3K2 k * uq3K1 k) ⊗ₜ (uq3K2 k * uq3K1 k) := by
    rw [map_mul]; erw [comulFreeAlg3_ι, comulFreeAlg3_ι, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hL, hR, uq3_K1K2_comm]

/- Group III: K-E conjugation (4 helpers) -/

private theorem comulFreeAlg3_K1E1 :
    comulFreeAlg3 k (gen3 k K1 * gen3 k E1) =
    comulFreeAlg3 k (scal3' k (T 2) * gen3 k E1 * gen3 k K1) := by
  simp +decide [comulFreeAlg3, comulOnGen3]
  simp +decide [mul_add, add_mul, mul_assoc, uq3_K1E1]
  simp +decide [mul_assoc, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']

private theorem comulFreeAlg3_K1E2 :
    comulFreeAlg3 k (gen3 k K1 * gen3 k E2) =
    comulFreeAlg3 k (scal3' k (T (-1)) * gen3 k E2 * gen3 k K1) := by
  simp +decide [comulFreeAlg3, comulOnGen3]
  simp +decide [mul_add, add_mul, mul_assoc, uq3_K1E2]
  simp +decide [mul_assoc, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
                uq3_K1K2_comm]

private theorem comulFreeAlg3_K2E1 :
    comulFreeAlg3 k (gen3 k K2 * gen3 k E1) =
    comulFreeAlg3 k (scal3' k (T (-1)) * gen3 k E1 * gen3 k K2) := by
  simp +decide [comulFreeAlg3, comulOnGen3]
  simp +decide [mul_add, add_mul, mul_assoc, uq3_K2E1]
  simp +decide [mul_assoc, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
                uq3_K1K2_comm]

private theorem comulFreeAlg3_K2E2 :
    comulFreeAlg3 k (gen3 k K2 * gen3 k E2) =
    comulFreeAlg3 k (scal3' k (T 2) * gen3 k E2 * gen3 k K2) := by
  simp +decide [comulFreeAlg3, comulOnGen3]
  simp +decide [mul_add, add_mul, mul_assoc, uq3_K2E2]
  simp +decide [mul_assoc, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']

/- Group IV: K-F conjugation (4 helpers) -/

private theorem comulFreeAlg3_K1F1 :
    comulFreeAlg3 k (gen3 k K1 * gen3 k F1) =
    comulFreeAlg3 k (scal3' k (T (-2)) * gen3 k F1 * gen3 k K1) := by
  simp +decide [comulFreeAlg3, comulOnGen3]
  simp +decide [mul_add, add_mul, mul_assoc, uq3_K1F1]
  simp +decide only [uq3_K1_mul_K1inv, uq3_K1inv_mul_K1]
  simp +decide [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
                TensorProduct.tmul_smul]

private theorem comulFreeAlg3_K1F2 :
    comulFreeAlg3 k (gen3 k K1 * gen3 k F2) =
    comulFreeAlg3 k (scal3' k (T 1) * gen3 k F2 * gen3 k K1) := by
  simp +decide [comulFreeAlg3, comulOnGen3]
  simp +decide [mul_add, add_mul, mul_assoc, uq3_K1F2]
  simp +decide only [uq3_K1_K2inv_comm]
  simp +decide [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
                TensorProduct.tmul_smul]

private theorem comulFreeAlg3_K2F1 :
    comulFreeAlg3 k (gen3 k K2 * gen3 k F1) =
    comulFreeAlg3 k (scal3' k (T 1) * gen3 k F1 * gen3 k K2) := by
  simp +decide [comulFreeAlg3, comulOnGen3]
  simp +decide [mul_add, add_mul, mul_assoc, uq3_K2F1]
  simp +decide only [uq3_K2_K1inv_comm]
  simp +decide [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
                TensorProduct.tmul_smul]

private theorem comulFreeAlg3_K2F2 :
    comulFreeAlg3 k (gen3 k K2 * gen3 k F2) =
    comulFreeAlg3 k (scal3' k (T (-2)) * gen3 k F2 * gen3 k K2) := by
  simp +decide [comulFreeAlg3, comulOnGen3]
  simp +decide [mul_add, add_mul, mul_assoc, uq3_K2F2]
  simp +decide only [uq3_K2_mul_K2inv, uq3_K2inv_mul_K2]
  simp +decide [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
                TensorProduct.tmul_smul]

/- Group V: EF commutation (4 helpers) -/

/-- Cross-term swap: E_i·K_i⁻¹ ⊗ K_i·F_i = K_i⁻¹·E_i ⊗ F_i·K_i (same index, signs cancel). -/
private theorem comulFreeAlg3_EF1_cross_terms :
    (uq3E1 k * uq3K1inv k) ⊗ₜ[LaurentPolynomial k] (uq3K1 k * uq3F1 k) =
    (uq3K1inv k * uq3E1 k) ⊗ₜ[LaurentPolynomial k] (uq3F1 k * uq3K1 k) := by
  rw [uq3_E1_mul_K1inv, uq3_K1F1]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul, smul_smul,
        show (T 2 : LaurentPolynomial k) * T (-2) = 1 from by rw [← T_add]; norm_num]

private theorem comulFreeAlg3_EF2_cross_terms :
    (uq3E2 k * uq3K2inv k) ⊗ₜ[LaurentPolynomial k] (uq3K2 k * uq3F2 k) =
    (uq3K2inv k * uq3E2 k) ⊗ₜ[LaurentPolynomial k] (uq3F2 k * uq3K2 k) := by
  rw [uq3_E2_mul_K2inv, uq3_K2F2]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul, smul_smul,
        show (T 2 : LaurentPolynomial k) * T (-2) = 1 from by rw [← T_add]; norm_num]

/-- Δ(E₁F₁) - Δ(F₁E₁) = (E₁F₁ - F₁E₁)⊗K₁ + K₁⁻¹⊗(E₁F₁ - F₁E₁). -/
private theorem comulFreeAlg3_E1F1_sub_F1E1 :
    comulFreeAlg3 k (gen3 k E1 * gen3 k F1) -
    comulFreeAlg3 k (gen3 k F1 * gen3 k E1) =
    (uq3E1 k * uq3F1 k - uq3F1 k * uq3E1 k) ⊗ₜ[LaurentPolynomial k] uq3K1 k +
    uq3K1inv k ⊗ₜ[LaurentPolynomial k] (uq3E1 k * uq3F1 k - uq3F1 k * uq3E1 k) := by
  rw [sub_eq_iff_eq_add]
  simp +decide [comulFreeAlg3_ι, comulOnGen3]
  simp +decide [add_mul, mul_add, mul_assoc, add_assoc, sub_eq_add_neg]
  rw [show (uq3E1 k * uq3K1inv k) ⊗ₜ[LaurentPolynomial k] (uq3K1 k * uq3F1 k) =
          (uq3K1inv k * uq3E1 k) ⊗ₜ[LaurentPolynomial k] (uq3F1 k * uq3K1 k) from
    comulFreeAlg3_EF1_cross_terms k]
  abel_nf
  simp +decide [add_comm, add_left_comm, add_assoc, TensorProduct.add_tmul, TensorProduct.tmul_add]
  simp +decide [← add_assoc, ← TensorProduct.tmul_add, ← TensorProduct.add_tmul]

private theorem comulFreeAlg3_E2F2_sub_F2E2 :
    comulFreeAlg3 k (gen3 k E2 * gen3 k F2) -
    comulFreeAlg3 k (gen3 k F2 * gen3 k E2) =
    (uq3E2 k * uq3F2 k - uq3F2 k * uq3E2 k) ⊗ₜ[LaurentPolynomial k] uq3K2 k +
    uq3K2inv k ⊗ₜ[LaurentPolynomial k] (uq3E2 k * uq3F2 k - uq3F2 k * uq3E2 k) := by
  rw [sub_eq_iff_eq_add]
  simp +decide [comulFreeAlg3_ι, comulOnGen3]
  simp +decide [add_mul, mul_add, mul_assoc, add_assoc, sub_eq_add_neg]
  rw [show (uq3E2 k * uq3K2inv k) ⊗ₜ[LaurentPolynomial k] (uq3K2 k * uq3F2 k) =
          (uq3K2inv k * uq3E2 k) ⊗ₜ[LaurentPolynomial k] (uq3F2 k * uq3K2 k) from
    comulFreeAlg3_EF2_cross_terms k]
  abel_nf
  simp +decide [add_comm, add_left_comm, add_assoc, TensorProduct.add_tmul, TensorProduct.tmul_add]
  simp +decide [← add_assoc, ← TensorProduct.tmul_add, ← TensorProduct.add_tmul]

/-- Apply EF11 q-commutator inside the tensor product: scale * [Δ(E₁F₁) - Δ(F₁E₁)] = Δ(K₁) - Δ(K₁⁻¹). -/
private theorem comulFreeAlg3_EF11_apply_serre :
    algebraMap (LaurentPolynomial k)
      ((Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) (T 1 - T (-1)) *
    ((uq3E1 k * uq3F1 k - uq3F1 k * uq3E1 k) ⊗ₜ[LaurentPolynomial k] uq3K1 k +
     uq3K1inv k ⊗ₜ[LaurentPolynomial k] (uq3E1 k * uq3F1 k - uq3F1 k * uq3E1 k)) =
    uq3K1 k ⊗ₜ[LaurentPolynomial k] uq3K1 k -
    uq3K1inv k ⊗ₜ[LaurentPolynomial k] uq3K1inv k := by
  have h_dist : algebraMap (LaurentPolynomial k)
        ((Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) (T 1 - T (-1)) *
      ((uq3E1 k * uq3F1 k - uq3F1 k * uq3E1 k) ⊗ₜ[LaurentPolynomial k] uq3K1 k) =
      (uq3K1 k - uq3K1inv k) ⊗ₜ[LaurentPolynomial k] uq3K1 k := by
    rw [← uq3_EF11]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have h_dist2 : algebraMap (LaurentPolynomial k)
        ((Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) (T 1 - T (-1)) *
      (uq3K1inv k ⊗ₜ[LaurentPolynomial k] (uq3E1 k * uq3F1 k - uq3F1 k * uq3E1 k)) =
      uq3K1inv k ⊗ₜ[LaurentPolynomial k] (uq3K1 k - uq3K1inv k) := by
    rw [← uq3_EF11]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [show (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 - T (-1)) * uq3K1inv k =
          (T 1 - T (-1)) • uq3K1inv k from (Algebra.smul_def _ _).symm,
        TensorProduct.smul_tmul, ← Algebra.smul_def]
  rw [mul_add, h_dist, h_dist2]
  convert congr_arg₂ (· + ·)
    (TensorProduct.sub_tmul (uq3K1 k) (uq3K1inv k) (uq3K1 k))
    (TensorProduct.tmul_sub (uq3K1inv k) (uq3K1 k) (uq3K1inv k)) using 1
  abel

private theorem comulFreeAlg3_EF22_apply_serre :
    algebraMap (LaurentPolynomial k)
      ((Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) (T 1 - T (-1)) *
    ((uq3E2 k * uq3F2 k - uq3F2 k * uq3E2 k) ⊗ₜ[LaurentPolynomial k] uq3K2 k +
     uq3K2inv k ⊗ₜ[LaurentPolynomial k] (uq3E2 k * uq3F2 k - uq3F2 k * uq3E2 k)) =
    uq3K2 k ⊗ₜ[LaurentPolynomial k] uq3K2 k -
    uq3K2inv k ⊗ₜ[LaurentPolynomial k] uq3K2inv k := by
  have h_dist : algebraMap (LaurentPolynomial k)
        ((Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) (T 1 - T (-1)) *
      ((uq3E2 k * uq3F2 k - uq3F2 k * uq3E2 k) ⊗ₜ[LaurentPolynomial k] uq3K2 k) =
      (uq3K2 k - uq3K2inv k) ⊗ₜ[LaurentPolynomial k] uq3K2 k := by
    rw [← uq3_EF22]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have h_dist2 : algebraMap (LaurentPolynomial k)
        ((Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k)) (T 1 - T (-1)) *
      (uq3K2inv k ⊗ₜ[LaurentPolynomial k] (uq3E2 k * uq3F2 k - uq3F2 k * uq3E2 k)) =
      uq3K2inv k ⊗ₜ[LaurentPolynomial k] (uq3K2 k - uq3K2inv k) := by
    rw [← uq3_EF22]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [show (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 - T (-1)) * uq3K2inv k =
          (T 1 - T (-1)) • uq3K2inv k from (Algebra.smul_def _ _).symm,
        TensorProduct.smul_tmul, ← Algebra.smul_def]
  rw [mul_add, h_dist, h_dist2]
  convert congr_arg₂ (· + ·)
    (TensorProduct.sub_tmul (uq3K2 k) (uq3K2inv k) (uq3K2 k))
    (TensorProduct.tmul_sub (uq3K2inv k) (uq3K2 k) (uq3K2inv k)) using 1
  abel

private theorem comulFreeAlg3_EF11 :
    comulFreeAlg3 k
      (scal3' k (T 1 - T (-1)) * (gen3 k E1 * gen3 k F1 - gen3 k F1 * gen3 k E1)) =
    comulFreeAlg3 k (gen3 k K1 - gen3 k K1inv) := by
  -- LHS: scal3'(q-q⁻¹) * [comul(E1F1) - comul(F1E1)]
  rw [map_mul, map_sub]
  -- RHS: comul(K1) - comul(K1inv)
  rw [show comulFreeAlg3 k (gen3 k K1 - gen3 k K1inv) =
        comulFreeAlg3 k (gen3 k K1) - comulFreeAlg3 k (gen3 k K1inv) from map_sub _ _ _]
  erw [comulFreeAlg3_ι (k := k) K1, comulFreeAlg3_ι (k := k) K1inv]
  simp only [comulOnGen3, scal3', AlgHom.commutes]
  rw [comulFreeAlg3_E1F1_sub_F1E1]
  exact comulFreeAlg3_EF11_apply_serre k

private theorem comulFreeAlg3_EF22 :
    comulFreeAlg3 k
      (scal3' k (T 1 - T (-1)) * (gen3 k E2 * gen3 k F2 - gen3 k F2 * gen3 k E2)) =
    comulFreeAlg3 k (gen3 k K2 - gen3 k K2inv) := by
  rw [map_mul, map_sub]
  rw [show comulFreeAlg3 k (gen3 k K2 - gen3 k K2inv) =
        comulFreeAlg3 k (gen3 k K2) - comulFreeAlg3 k (gen3 k K2inv) from map_sub _ _ _]
  erw [comulFreeAlg3_ι (k := k) K2, comulFreeAlg3_ι (k := k) K2inv]
  simp only [comulOnGen3, scal3', AlgHom.commutes]
  rw [comulFreeAlg3_E2F2_sub_F2E2]
  exact comulFreeAlg3_EF22_apply_serre k

private theorem comulFreeAlg3_E1F2comm :
    comulFreeAlg3 k (gen3 k E1 * gen3 k F2) =
    comulFreeAlg3 k (gen3 k F2 * gen3 k E1) := by
  simp +decide [comulFreeAlg3, comulOnGen3, mul_add, add_mul,
                uq3_E1F2_comm, uq3_E1_mul_K2inv, uq3_K1F2]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul, smul_smul,
        show (T 1 : LaurentPolynomial k) * T (-1) = 1 from by rw [← T_add]; norm_num]
  abel

private theorem comulFreeAlg3_E2F1comm :
    comulFreeAlg3 k (gen3 k E2 * gen3 k F1) =
    comulFreeAlg3 k (gen3 k F1 * gen3 k E2) := by
  simp +decide [comulFreeAlg3, comulOnGen3, mul_add, add_mul,
                uq3_E2F1_comm, uq3_E2_mul_K1inv, uq3_K2F1]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul, smul_smul,
        show (T 1 : LaurentPolynomial k) * T (-1) = 1 from by rw [← T_add]; norm_num]
  abel

/- Groups VI/VII: q-Serre (4 helpers) — placeholders for Tranche B -/

/-! ### Sector infrastructure for q-Serre cubic compatibility

Following the Uqsl2AffineHopf.lean `sect_hSerreE01_*` pattern (L1560-2060), adapted
for sl_3's quadratic (not cubic) Serre relation. Scalars are T(2)/T(-1)/T(1) not
T(±2) throughout — the Cartan off-diagonal is -1 for sl_3. -/

-- === smul-form Serre relations (used by both comul and antipode Serre proofs) ===

/-- Serre E12 in smul form: E₁²E₂ - [2]_q·E₁E₂E₁ + E₂E₁² = 0 (equivalent to uq3_SerreE12). -/
private theorem sect3_hSerreE12_smul :
    uq3E1 k * uq3E1 k * uq3E2 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3E2 k * uq3E1 k) +
    uq3E2 k * uq3E1 k * uq3E1 k = 0 := by
  have h := uq3_SerreE12 k
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc,
      show uq3E1 k * uq3E1 k * uq3E2 k -
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 + T (-1)) *
            uq3E1 k * uq3E2 k * uq3E1 k +
          uq3E2 k * uq3E1 k * uq3E1 k =
          (uq3E1 k * uq3E1 k * uq3E2 k + uq3E2 k * uq3E1 k * uq3E1 k) -
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 + T (-1)) *
            uq3E1 k * uq3E2 k * uq3E1 k from by noncomm_ring, h]
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  exact sub_self _

private theorem sect3_hSerreE21_smul :
    uq3E2 k * uq3E2 k * uq3E1 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3E1 k * uq3E2 k) +
    uq3E1 k * uq3E2 k * uq3E2 k = 0 := by
  have h := uq3_SerreE21 k
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc,
      show uq3E2 k * uq3E2 k * uq3E1 k -
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 + T (-1)) *
            uq3E2 k * uq3E1 k * uq3E2 k +
          uq3E1 k * uq3E2 k * uq3E2 k =
          (uq3E2 k * uq3E2 k * uq3E1 k + uq3E1 k * uq3E2 k * uq3E2 k) -
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 + T (-1)) *
            uq3E2 k * uq3E1 k * uq3E2 k from by noncomm_ring, h]
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  exact sub_self _

private theorem sect3_hSerreF12_smul :
    uq3F1 k * uq3F1 k * uq3F2 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3F2 k * uq3F1 k) +
    uq3F2 k * uq3F1 k * uq3F1 k = 0 := by
  have h := uq3_SerreF12 k
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc,
      show uq3F1 k * uq3F1 k * uq3F2 k -
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 + T (-1)) *
            uq3F1 k * uq3F2 k * uq3F1 k +
          uq3F2 k * uq3F1 k * uq3F1 k =
          (uq3F1 k * uq3F1 k * uq3F2 k + uq3F2 k * uq3F1 k * uq3F1 k) -
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 + T (-1)) *
            uq3F1 k * uq3F2 k * uq3F1 k from by noncomm_ring, h]
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  exact sub_self _

private theorem sect3_hSerreF21_smul :
    uq3F2 k * uq3F2 k * uq3F1 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3F1 k * uq3F2 k) +
    uq3F1 k * uq3F2 k * uq3F2 k = 0 := by
  have h := uq3_SerreF21 k
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc,
      show uq3F2 k * uq3F2 k * uq3F1 k -
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 + T (-1)) *
            uq3F2 k * uq3F1 k * uq3F2 k +
          uq3F1 k * uq3F2 k * uq3F2 k =
          (uq3F2 k * uq3F2 k * uq3F1 k + uq3F1 k * uq3F2 k * uq3F2 k) -
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 + T (-1)) *
            uq3F2 k * uq3F1 k * uq3F2 k from by noncomm_ring, h]
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  exact sub_self _

-- === Base KE rewrites in smul and positional form ===
-- Pattern: each K_i E_j commutation gives two helpers (standalone + positional).

/-- K₁·E₁ = T(2)·E₁·K₁ in smul form. -/
private theorem sect3_hKE_smul_K1E1 :
    uq3K1 k * uq3E1 k = (T 2 : LaurentPolynomial k) • (uq3E1 k * uq3K1 k) := by
  rw [uq3_K1E1, Algebra.smul_def, mul_assoc]

private theorem sect3_hKE_at_K1E1 (x : Uqsl3 k) :
    x * uq3K1 k * uq3E1 k = (T 2 : LaurentPolynomial k) • (x * uq3E1 k * uq3K1 k) := by
  rw [mul_assoc x (uq3K1 k) (uq3E1 k), sect3_hKE_smul_K1E1, mul_smul_comm, ← mul_assoc]

/-- K₁·E₂ = T(-1)·E₂·K₁ in smul form. -/
private theorem sect3_hKE_smul_K1E2 :
    uq3K1 k * uq3E2 k = (T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3K1 k) := by
  rw [uq3_K1E2, Algebra.smul_def, mul_assoc]

private theorem sect3_hKE_at_K1E2 (x : Uqsl3 k) :
    x * uq3K1 k * uq3E2 k = (T (-1) : LaurentPolynomial k) • (x * uq3E2 k * uq3K1 k) := by
  rw [mul_assoc x (uq3K1 k) (uq3E2 k), sect3_hKE_smul_K1E2, mul_smul_comm, ← mul_assoc]

/-- K₂·E₁ = T(-1)·E₁·K₂ in smul form. -/
private theorem sect3_hKE_smul_K2E1 :
    uq3K2 k * uq3E1 k = (T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3K2 k) := by
  rw [uq3_K2E1, Algebra.smul_def, mul_assoc]

private theorem sect3_hKE_at_K2E1 (x : Uqsl3 k) :
    x * uq3K2 k * uq3E1 k = (T (-1) : LaurentPolynomial k) • (x * uq3E1 k * uq3K2 k) := by
  rw [mul_assoc x (uq3K2 k) (uq3E1 k), sect3_hKE_smul_K2E1, mul_smul_comm, ← mul_assoc]

/-- K₂·E₂ = T(2)·E₂·K₂ in smul form. -/
private theorem sect3_hKE_smul_K2E2 :
    uq3K2 k * uq3E2 k = (T 2 : LaurentPolynomial k) • (uq3E2 k * uq3K2 k) := by
  rw [uq3_K2E2, Algebra.smul_def, mul_assoc]

private theorem sect3_hKE_at_K2E2 (x : Uqsl3 k) :
    x * uq3K2 k * uq3E2 k = (T 2 : LaurentPolynomial k) • (x * uq3E2 k * uq3K2 k) := by
  rw [mul_assoc x (uq3K2 k) (uq3E2 k), sect3_hKE_smul_K2E2, mul_smul_comm, ← mul_assoc]

-- === F-side base KinvF rewrites (for F comul: Δ(F_i) = F_i ⊗ 1 + K_i⁻¹ ⊗ F_i) ===

/-- K₁⁻¹·F₁ = T(2)·F₁·K₁⁻¹ in smul form. -/
private theorem sect3_hKinvF_smul_K1invF1 :
    uq3K1inv k * uq3F1 k = (T 2 : LaurentPolynomial k) • (uq3F1 k * uq3K1inv k) := by
  rw [uq3_K1inv_mul_F1, Algebra.smul_def, mul_assoc]

private theorem sect3_hKinvF_at_K1invF1 (x : Uqsl3 k) :
    x * uq3K1inv k * uq3F1 k = (T 2 : LaurentPolynomial k) • (x * uq3F1 k * uq3K1inv k) := by
  rw [mul_assoc x (uq3K1inv k) (uq3F1 k), sect3_hKinvF_smul_K1invF1, mul_smul_comm, ← mul_assoc]

/-- K₁⁻¹·F₂ = T(-1)·F₂·K₁⁻¹ in smul form. -/
private theorem sect3_hKinvF_smul_K1invF2 :
    uq3K1inv k * uq3F2 k = (T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k) := by
  rw [uq3_K1inv_mul_F2, Algebra.smul_def, mul_assoc]

private theorem sect3_hKinvF_at_K1invF2 (x : Uqsl3 k) :
    x * uq3K1inv k * uq3F2 k = (T (-1) : LaurentPolynomial k) • (x * uq3F2 k * uq3K1inv k) := by
  rw [mul_assoc x (uq3K1inv k) (uq3F2 k), sect3_hKinvF_smul_K1invF2, mul_smul_comm, ← mul_assoc]

/-- K₂⁻¹·F₁ = T(-1)·F₁·K₂⁻¹ in smul form. -/
private theorem sect3_hKinvF_smul_K2invF1 :
    uq3K2inv k * uq3F1 k = (T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k) := by
  rw [uq3_K2inv_mul_F1, Algebra.smul_def, mul_assoc]

private theorem sect3_hKinvF_at_K2invF1 (x : Uqsl3 k) :
    x * uq3K2inv k * uq3F1 k = (T (-1) : LaurentPolynomial k) • (x * uq3F1 k * uq3K2inv k) := by
  rw [mul_assoc x (uq3K2inv k) (uq3F1 k), sect3_hKinvF_smul_K2invF1, mul_smul_comm, ← mul_assoc]

/-- K₂⁻¹·F₂ = T(2)·F₂·K₂⁻¹ in smul form. -/
private theorem sect3_hKinvF_smul_K2invF2 :
    uq3K2inv k * uq3F2 k = (T 2 : LaurentPolynomial k) • (uq3F2 k * uq3K2inv k) := by
  rw [uq3_K2inv_mul_F2, Algebra.smul_def, mul_assoc]

private theorem sect3_hKinvF_at_K2invF2 (x : Uqsl3 k) :
    x * uq3K2inv k * uq3F2 k = (T 2 : LaurentPolynomial k) • (x * uq3F2 k * uq3K2inv k) := by
  rw [mul_assoc x (uq3K2inv k) (uq3F2 k), sect3_hKinvF_smul_K2invF2, mul_smul_comm, ← mul_assoc]

-- === Sector identity helpers for SerreE12 q-Serre coproduct compatibility ===

/-- Sector (2,0): K₁²·E₂ - [2]·K₁·E₂·K₁ + E₂·K₁² = 0.
    sl_3 analog of `sect_hUqIdE01_30`. Proved by K₁·E₂ = T(-1)·E₂·K₁ commutation
    + coefficient identity T(-2) - [2]·T(-1) + 1 = 0. -/
private theorem sect3_hUqIdE12_20 :
    uq3K1 k * uq3K1 k * uq3E2 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3K1 k * uq3E2 k * uq3K1 k) +
    uq3E2 k * uq3K1 k * uq3K1 k = 0 := by
  have hKE_smul := sect3_hKE_smul_K1E2 k
  have hKE_at := sect3_hKE_at_K1E2 k
  have hK2E2 : uq3K1 k * uq3K1 k * uq3E2 k =
      (T (-2) : LaurentPolynomial k) • (uq3E2 k * uq3K1 k * uq3K1 k) := by
    rw [hKE_at, hKE_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK1E2K1 : uq3K1 k * uq3E2 k * uq3K1 k =
      (T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3K1 k * uq3K1 k) := by
    rw [hKE_smul]; simp only [smul_mul_assoc]
  rw [hK2E2, hK1E2K1, smul_smul]
  have factor : ∀ (r s : LaurentPolynomial k) (x : Uqsl3 k),
      r • x - s • x + x = (r - s + 1) • x := by intros; module
  rw [factor]
  have hcoef : (T (-2) - (T 1 + T (-1)) * T (-1) + 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show T (-2) - (T 0 + T (-2)) + 1 = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

/-- Sector (0,1): E₁²·K₂ - [2]·E₁·K₂·E₁ + K₂·E₁² = 0.
    sl_3 analog of `sect_hUqIdE01_01`. Pushes K₂ leftward through E₁'s. -/
private theorem sect3_hUqIdE12_01 :
    uq3E1 k * uq3E1 k * uq3K2 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3K2 k * uq3E1 k) +
    uq3K2 k * uq3E1 k * uq3E1 k = 0 := by
  have hKE_smul := sect3_hKE_smul_K2E1 k  -- K2·E1 = T(-1)•E1·K2
  have hKE_at := sect3_hKE_at_K2E1 k       -- x·K2·E1 = T(-1)•(x·E1·K2)
  -- E1·K2·E1 = E1·T(-1)•(E1·K2) = T(-1)•(E1·E1·K2) — apply via inner K2·E1
  have hE1K2E1 : uq3E1 k * uq3K2 k * uq3E1 k =
      (T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3E1 k * uq3K2 k) := by
    rw [show uq3E1 k * uq3K2 k * uq3E1 k = uq3E1 k * (uq3K2 k * uq3E1 k) from by noncomm_ring,
        hKE_smul]
    simp only [mul_smul_comm, ← mul_assoc]
  -- K2·E1·E1 = T(-1)•(E1·K2·E1) [inner K2E1] = T(-1)•T(-1)•(E1²K2) = T(-2)•(E1²K2)
  have hK2E1E1 : uq3K2 k * uq3E1 k * uq3E1 k =
      (T (-2) : LaurentPolynomial k) • (uq3E1 k * uq3E1 k * uq3K2 k) := by
    rw [show uq3K2 k * uq3E1 k * uq3E1 k = (uq3K2 k * uq3E1 k) * uq3E1 k from by noncomm_ring,
        hKE_smul]
    simp only [smul_mul_assoc]
    rw [show uq3E1 k * uq3K2 k * uq3E1 k = uq3E1 k * (uq3K2 k * uq3E1 k) from by noncomm_ring,
        hKE_smul]
    simp only [mul_smul_comm, smul_smul, ← mul_assoc]
    congr 1; rw [← T_add]; norm_num
  rw [hE1K2E1, hK2E1E1, smul_smul]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      x - s • x + t • x = (1 - s + t) • x := by intros; module
  rw [factor]
  have hcoef : (1 - (T 1 + T (-1)) * T (-1) + T (-2) : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 - (T 0 + T (-2)) + T (-2) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

/-- Sector (1,0) E1E2-left bracket: (E₁·K₁·K₂ + K₁·E₁·K₂) - [2]·K₁·K₂·E₁ = 0.
    Uses K₁·E₁ = T(2)·E₁·K₁, K-K commute, and K₁·K₂·E₁ = T(1)·E₁·K₁·K₂. -/
private theorem sect3_hUqIdE12_10_E1E2 :
    uq3E1 k * uq3K1 k * uq3K2 k + uq3K1 k * uq3E1 k * uq3K2 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3K1 k * uq3K2 k * uq3E1 k) = 0 := by
  have hK1E1_at := sect3_hKE_at_K1E1 k  -- x·K1·E1 = T(2)•(x·E1·K1)
  have hK2E1_smul := sect3_hKE_smul_K2E1 k  -- K2·E1 = T(-1)•(E1·K2)
  have hKK := uq3_K1K2_comm k  -- K1·K2 = K2·K1
  -- Reduce each to common atom: E1·K1·K2
  have hE1K1K2 : uq3E1 k * uq3K1 k * uq3K2 k = uq3E1 k * uq3K1 k * uq3K2 k := rfl
  have hK1E1K2 : uq3K1 k * uq3E1 k * uq3K2 k =
      (T 2 : LaurentPolynomial k) • (uq3E1 k * uq3K1 k * uq3K2 k) := by
    have : uq3K1 k * uq3E1 k * uq3K2 k =
        (T 2 : LaurentPolynomial k) • (uq3E1 k * uq3K1 k) * uq3K2 k := by
      rw [show uq3K1 k * uq3E1 k = (T 2 : LaurentPolynomial k) • (uq3E1 k * uq3K1 k) from
        sect3_hKE_smul_K1E1 k]
    rw [this, smul_mul_assoc]
  have hK1K2E1 : uq3K1 k * uq3K2 k * uq3E1 k =
      (T 1 : LaurentPolynomial k) • (uq3E1 k * uq3K1 k * uq3K2 k) := by
    -- K1·K2·E1 = K2·K1·E1 (KK commute) = K2·T(2)•(E1·K1) [K1E1] = T(2)•K2·E1·K1
    --         = T(2)•T(-1)•E1·K2·K1 [K2E1] = T(1)•E1·K2·K1 = T(1)•E1·K1·K2 [KK]
    rw [show uq3K1 k * uq3K2 k * uq3E1 k = uq3K2 k * (uq3K1 k * uq3E1 k) from by
      rw [show uq3K1 k * uq3K2 k = uq3K2 k * uq3K1 k from hKK]; noncomm_ring]
    rw [sect3_hKE_smul_K1E1, mul_smul_comm,
        show uq3K2 k * (uq3E1 k * uq3K1 k) = uq3K2 k * uq3E1 k * uq3K1 k from by noncomm_ring,
        hK2E1_smul, smul_mul_assoc, smul_smul,
        show uq3E1 k * uq3K2 k * uq3K1 k = uq3E1 k * uq3K1 k * uq3K2 k from by
          rw [mul_assoc, ← hKK, ← mul_assoc]]
    congr 1; rw [← T_add]; norm_num
  rw [hK1E1K2, hK1K2E1, smul_smul]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      x + s • x - t • x = (1 + s - t) • x := by intros; module
  rw [factor]
  have hcoef : (1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 + T 2 - (T 2 + T 0) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

/-- Sector (1,0) E2E1-left bracket: (K₂·E₁·K₁ + K₂·K₁·E₁) - [2]·E₁·K₂·K₁ = 0. -/
private theorem sect3_hUqIdE12_10_E2E1 :
    uq3K2 k * uq3E1 k * uq3K1 k + uq3K2 k * uq3K1 k * uq3E1 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3K2 k * uq3K1 k) = 0 := by
  have hK2E1_smul := sect3_hKE_smul_K2E1 k
  have hK1E1_smul := sect3_hKE_smul_K1E1 k
  have hKK := uq3_K1K2_comm k
  -- Reduce to common atom: E1·K1·K2 (or E1·K2·K1, equivalent via hKK)
  -- Target atom: E1·K2·K1 (matches RHS form)
  have hK2E1K1 : uq3K2 k * uq3E1 k * uq3K1 k =
      (T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3K2 k * uq3K1 k) := by
    rw [hK2E1_smul, smul_mul_assoc]
  have hK2K1E1 : uq3K2 k * uq3K1 k * uq3E1 k =
      (T 1 : LaurentPolynomial k) • (uq3E1 k * uq3K2 k * uq3K1 k) := by
    -- K2·K1·E1 = K1·K2·E1 (K-K commute) = K1·T(-1)•(E1·K2) = T(-1)•K1·E1·K2
    --         = T(-1)•T(2)•(E1·K1·K2) = T(1)•E1·K1·K2 = T(1)•E1·K2·K1
    rw [show uq3K2 k * uq3K1 k = uq3K1 k * uq3K2 k from hKK.symm]
    rw [show uq3K1 k * uq3K2 k * uq3E1 k = uq3K1 k * (uq3K2 k * uq3E1 k) from by noncomm_ring,
        hK2E1_smul, mul_smul_comm,
        show uq3K1 k * (uq3E1 k * uq3K2 k) = uq3K1 k * uq3E1 k * uq3K2 k from by noncomm_ring,
        hK1E1_smul, smul_mul_assoc, smul_smul]
    rw [show uq3E1 k * uq3K1 k * uq3K2 k = uq3E1 k * uq3K2 k * uq3K1 k from by
      rw [mul_assoc, hKK, ← mul_assoc]]
    congr 1; rw [← T_add]; norm_num
  rw [hK2E1K1, hK2K1E1]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      s • x + t • x - (T 1 + T (-1) : LaurentPolynomial k) • x =
      (s + t - (T 1 + T (-1))) • x := by intros; module
  rw [factor]
  have hcoef : (T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k) = 0 := by ring
  rw [hcoef, zero_smul]

/-- Sector (1,1) combined: 4 LHS atoms - [2]·(2 RHS atoms) = 0.
    Reduces atoms to A = E₁·E₂·K₁ and B = E₂·E₁·K₁ via K-E commutations,
    coefficients sum to 0 by [2] - [2] = 0 and 1 + T(2) - [2]·T(1) = 0. -/
private theorem sect3_hUqIdE12_11 :
    (uq3E1 k * uq3K1 k * uq3E2 k + uq3K1 k * uq3E1 k * uq3E2 k +
     uq3E2 k * uq3E1 k * uq3K1 k + uq3E2 k * uq3K1 k * uq3E1 k) -
    (T 1 + T (-1) : LaurentPolynomial k) •
      (uq3E1 k * uq3E2 k * uq3K1 k + uq3K1 k * uq3E2 k * uq3E1 k) = 0 := by
  have hK1E1 := sect3_hKE_smul_K1E1 k
  have hK1E2 := sect3_hKE_smul_K1E2 k
  -- Reduce atoms to A := E1·E2·K1 and B := E2·E1·K1
  have hE1K1E2 : uq3E1 k * uq3K1 k * uq3E2 k =
      (T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3E2 k * uq3K1 k) := by
    rw [show uq3E1 k * uq3K1 k * uq3E2 k = uq3E1 k * (uq3K1 k * uq3E2 k) from by noncomm_ring,
        hK1E2]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK1E1E2 : uq3K1 k * uq3E1 k * uq3E2 k =
      (T 1 : LaurentPolynomial k) • (uq3E1 k * uq3E2 k * uq3K1 k) := by
    rw [hK1E1, smul_mul_assoc,
        show uq3E1 k * uq3K1 k * uq3E2 k = uq3E1 k * (uq3K1 k * uq3E2 k) from by noncomm_ring,
        hK1E2, mul_smul_comm, smul_smul,
        show uq3E1 k * (uq3E2 k * uq3K1 k) = uq3E1 k * uq3E2 k * uq3K1 k from by noncomm_ring]
    congr 1; rw [← T_add]; norm_num
  have hE2K1E1 : uq3E2 k * uq3K1 k * uq3E1 k =
      (T 2 : LaurentPolynomial k) • (uq3E2 k * uq3E1 k * uq3K1 k) := by
    rw [show uq3E2 k * uq3K1 k * uq3E1 k = uq3E2 k * (uq3K1 k * uq3E1 k) from by noncomm_ring,
        hK1E1]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK1E2E1 : uq3K1 k * uq3E2 k * uq3E1 k =
      (T 1 : LaurentPolynomial k) • (uq3E2 k * uq3E1 k * uq3K1 k) := by
    rw [hK1E2, smul_mul_assoc,
        show uq3E2 k * uq3K1 k * uq3E1 k = uq3E2 k * (uq3K1 k * uq3E1 k) from by noncomm_ring,
        hK1E1, mul_smul_comm, smul_smul,
        show uq3E2 k * (uq3E1 k * uq3K1 k) = uq3E2 k * uq3E1 k * uq3K1 k from by noncomm_ring]
    congr 1; rw [← T_add]; norm_num
  rw [hE1K1E2, hK1E1E2, hE2K1E1, hK1E2E1]
  -- Goal: T(-1)•A + T(1)•A + B + T(2)•B - [2]•(A + T(1)•B) = 0
  -- Where A = E1·E2·K1 and B = E2·E1·K1
  have factor : ∀ (a b : Uqsl3 k),
      ((T (-1) : LaurentPolynomial k) • a + (T 1 : LaurentPolynomial k) • a +
       b + (T 2 : LaurentPolynomial k) • b) -
      ((T 1 + T (-1) : LaurentPolynomial k)) • (a + (T 1 : LaurentPolynomial k) • b) =
      ((T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k)) • a +
      ((1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k)) • b := by intros; module
  rw [factor]
  have hcoef_A : (T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k) = 0 := by ring
  have hcoef_B : (1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 + T 2 - (T 2 + T 0) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef_A, hcoef_B, zero_smul, zero_smul, add_zero]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem comulFreeAlg3_SerreE12 :
    comulFreeAlg3 k
      (gen3 k E1 * gen3 k E1 * gen3 k E2 + gen3 k E2 * gen3 k E1 * gen3 k E1) =
    comulFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k E1 * gen3 k E2 * gen3 k E1) := by
  rw [← sub_eq_zero, ← map_sub]
  -- Phase 1: expand Δ + tmul_mul_tmul + algebraMap → scalar
  simp only [scal3', map_sub, map_add, map_mul, AlgHom.commutes,
             comulFreeAlg3_ι, comulOnGen3, mul_add, add_mul,
             Algebra.TensorProduct.algebraMap_apply,
             Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [← Algebra.smul_def, smul_mul_assoc, smul_add, smul_sub]
  simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']
  -- Phase 2: build sector hypotheses via phi maps + map_zero
  let phi_LL : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip
      (uq3K1 k * uq3K1 k * uq3K2 k)
  let phi_RR : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (1 : Uqsl3 k)
  have hSerreS := sect3_hSerreE12_smul k
  have hSect00 :
      phi_LL (uq3E1 k * uq3E1 k * uq3E2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3E2 k * uq3E1 k) +
        uq3E2 k * uq3E1 k * uq3E1 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_LL
  have hSect21 :
      phi_RR (uq3E1 k * uq3E1 k * uq3E2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3E2 k * uq3E1 k) +
        uq3E2 k * uq3E1 k * uq3E1 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_RR
  rw [map_add phi_LL, map_sub phi_LL,
      LinearMap.map_smul_of_tower phi_LL] at hSect00
  rw [map_add phi_RR, map_sub phi_RR,
      LinearMap.map_smul_of_tower phi_RR] at hSect21
  simp only [phi_LL, phi_RR, LinearMap.flip_apply, TensorProduct.mk_apply]
    at hSect00 hSect21
  have hUqId01 := sect3_hUqIdE12_20 k
  let phi_01 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E1 k * uq3E1 k)
  have hSect01 :
      phi_01 (uq3K1 k * uq3K1 k * uq3E2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3K1 k * uq3E2 k * uq3K1 k) +
        uq3E2 k * uq3K1 k * uq3K1 k) = 0 := by
    rw [hUqId01]; exact map_zero phi_01
  rw [map_add phi_01, map_sub phi_01,
      LinearMap.map_smul_of_tower phi_01] at hSect01
  simp only [phi_01, TensorProduct.mk_apply] at hSect01
  have hUqId20 := sect3_hUqIdE12_01 k
  let phi_20 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E2 k)
  have hSect20 :
      phi_20 (uq3E1 k * uq3E1 k * uq3K2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3K2 k * uq3E1 k) +
        uq3K2 k * uq3E1 k * uq3E1 k) = 0 := by
    rw [hUqId20]; exact map_zero phi_20
  rw [map_add phi_20, map_sub phi_20,
      LinearMap.map_smul_of_tower phi_20] at hSect20
  simp only [phi_20, TensorProduct.mk_apply] at hSect20
  have hUqId10a := sect3_hUqIdE12_10_E1E2 k
  let phi_10a : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E1 k * uq3E2 k)
  have hSect10a :
      phi_10a (uq3E1 k * uq3K1 k * uq3K2 k + uq3K1 k * uq3E1 k * uq3K2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3K1 k * uq3K2 k * uq3E1 k)) = 0 := by
    rw [hUqId10a]; exact map_zero phi_10a
  rw [map_sub phi_10a, map_add phi_10a,
      LinearMap.map_smul_of_tower phi_10a] at hSect10a
  simp only [phi_10a, TensorProduct.mk_apply] at hSect10a
  have hUqId10b := sect3_hUqIdE12_10_E2E1 k
  let phi_10b : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E2 k * uq3E1 k)
  have hSect10b :
      phi_10b (uq3K2 k * uq3E1 k * uq3K1 k + uq3K2 k * uq3K1 k * uq3E1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3K2 k * uq3K1 k)) = 0 := by
    rw [hUqId10b]; exact map_zero phi_10b
  rw [map_sub phi_10b, map_add phi_10b,
      LinearMap.map_smul_of_tower phi_10b] at hSect10b
  simp only [phi_10b, TensorProduct.mk_apply] at hSect10b
  have hUqId11 := sect3_hUqIdE12_11 k
  let phi_11 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E1 k)
  have hSect11 :
      phi_11 ((uq3E1 k * uq3K1 k * uq3E2 k + uq3K1 k * uq3E1 k * uq3E2 k +
                uq3E2 k * uq3E1 k * uq3K1 k + uq3E2 k * uq3K1 k * uq3E1 k) -
        (T 1 + T (-1) : LaurentPolynomial k) •
          (uq3E1 k * uq3E2 k * uq3K1 k + uq3K1 k * uq3E2 k * uq3E1 k)) = 0 := by
    rw [hUqId11]; exact map_zero phi_11
  rw [map_sub phi_11, map_add phi_11, map_add phi_11, map_add phi_11,
      LinearMap.map_smul_of_tower phi_11, map_add phi_11] at hSect11
  simp only [phi_11, TensorProduct.mk_apply, TensorProduct.tmul_add, smul_add] at hSect11
  -- Phase 3: K-normalization on goal (K1²K2 canonical form)
  have hKK : uq3K2 k * uq3K1 k = uq3K1 k * uq3K2 k := (uq3_K1K2_comm k).symm
  have hKKK1 : uq3K2 k * uq3K1 k * uq3K1 k = uq3K1 k * uq3K1 k * uq3K2 k := by
    rw [hKK, mul_assoc, hKK, ← mul_assoc]
  have hKKK2 : uq3K1 k * uq3K2 k * uq3K1 k = uq3K1 k * uq3K1 k * uq3K2 k := by
    rw [mul_assoc, hKK, ← mul_assoc]
  have hKKK3 : uq3K2 k * uq3K1 k * uq3E1 k = uq3K1 k * uq3K2 k * uq3E1 k := by rw [hKK]
  simp_rw [hKKK1, hKKK2, hKKK3]
  -- Phase 4 (per Phase-5s research): normalize hypotheses + goal to common form,
  -- then linear_combination + abel! at .default transparency
  clear hSerreS hUqId01 hUqId20 hUqId10a hUqId10b hUqId11
  clear phi_LL phi_RR phi_01 phi_20 phi_10a phi_10b phi_11
  -- Canonical form: distribute combined scalars + tmul over additions.
  simp only [add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
             TensorProduct.smul_tmul'] at hSect00 hSect21 hSect01 hSect20 hSect10a hSect10b hSect11 ⊢
  linear_combination (norm := skip)
    hSect00 + hSect21 + hSect01 + hSect20 + hSect10a + hSect10b + hSect11
  -- Residual: K-commute on uq3K2·K1·E1 → K1·K2·E1 (final K-norm), then abel
  simp_rw [hKKK3]
  abel!

-- === Sector identity helpers for SerreE21 (mechanical 1↔2 swap of E12 sectors) ===

private theorem sect3_hUqIdE21_20 :
    uq3K2 k * uq3K2 k * uq3E1 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3K2 k * uq3E1 k * uq3K2 k) +
    uq3E1 k * uq3K2 k * uq3K2 k = 0 := by
  have hKE_smul := sect3_hKE_smul_K2E1 k
  have hKE_at := sect3_hKE_at_K2E1 k
  have hK2E1 : uq3K2 k * uq3K2 k * uq3E1 k =
      (T (-2) : LaurentPolynomial k) • (uq3E1 k * uq3K2 k * uq3K2 k) := by
    rw [hKE_at, hKE_smul]; simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK2E1K2 : uq3K2 k * uq3E1 k * uq3K2 k =
      (T (-1) : LaurentPolynomial k) • (uq3E1 k * uq3K2 k * uq3K2 k) := by
    rw [hKE_smul]; simp only [smul_mul_assoc]
  rw [hK2E1, hK2E1K2, smul_smul]
  have factor : ∀ (r s : LaurentPolynomial k) (x : Uqsl3 k),
      r • x - s • x + x = (r - s + 1) • x := by intros; module
  rw [factor]
  have hcoef : (T (-2) - (T 1 + T (-1)) * T (-1) + 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show T (-2) - (T 0 + T (-2)) + 1 = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdE21_01 :
    uq3E2 k * uq3E2 k * uq3K1 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3K1 k * uq3E2 k) +
    uq3K1 k * uq3E2 k * uq3E2 k = 0 := by
  have hKE_smul := sect3_hKE_smul_K1E2 k
  have hKE_at := sect3_hKE_at_K1E2 k
  have hE2K1E2 : uq3E2 k * uq3K1 k * uq3E2 k =
      (T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3E2 k * uq3K1 k) := by
    rw [show uq3E2 k * uq3K1 k * uq3E2 k = uq3E2 k * (uq3K1 k * uq3E2 k) from by noncomm_ring,
        hKE_smul]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK1E2E2 : uq3K1 k * uq3E2 k * uq3E2 k =
      (T (-2) : LaurentPolynomial k) • (uq3E2 k * uq3E2 k * uq3K1 k) := by
    rw [show uq3K1 k * uq3E2 k * uq3E2 k = (uq3K1 k * uq3E2 k) * uq3E2 k from by noncomm_ring,
        hKE_smul]
    simp only [smul_mul_assoc]
    rw [show uq3E2 k * uq3K1 k * uq3E2 k = uq3E2 k * (uq3K1 k * uq3E2 k) from by noncomm_ring,
        hKE_smul]
    simp only [mul_smul_comm, smul_smul, ← mul_assoc]
    congr 1; rw [← T_add]; norm_num
  rw [hE2K1E2, hK1E2E2, smul_smul]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      x - s • x + t • x = (1 - s + t) • x := by intros; module
  rw [factor]
  have hcoef : (1 - (T 1 + T (-1)) * T (-1) + T (-2) : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 - (T 0 + T (-2)) + T (-2) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdE21_10_E2E1 :
    uq3E2 k * uq3K2 k * uq3K1 k + uq3K2 k * uq3E2 k * uq3K1 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3K2 k * uq3K1 k * uq3E2 k) = 0 := by
  have hK2E2_at := sect3_hKE_at_K2E2 k
  have hK1E2_smul := sect3_hKE_smul_K1E2 k
  have hKK := uq3_K1K2_comm k
  have hE2K2K1 : uq3E2 k * uq3K2 k * uq3K1 k = uq3E2 k * uq3K2 k * uq3K1 k := rfl
  have hK2E2K1 : uq3K2 k * uq3E2 k * uq3K1 k =
      (T 2 : LaurentPolynomial k) • (uq3E2 k * uq3K2 k * uq3K1 k) := by
    have : uq3K2 k * uq3E2 k * uq3K1 k =
        (T 2 : LaurentPolynomial k) • (uq3E2 k * uq3K2 k) * uq3K1 k := by
      rw [show uq3K2 k * uq3E2 k = (T 2 : LaurentPolynomial k) • (uq3E2 k * uq3K2 k) from
        sect3_hKE_smul_K2E2 k]
    rw [this, smul_mul_assoc]
  have hK2K1E2 : uq3K2 k * uq3K1 k * uq3E2 k =
      (T 1 : LaurentPolynomial k) • (uq3E2 k * uq3K2 k * uq3K1 k) := by
    rw [show uq3K2 k * uq3K1 k * uq3E2 k = uq3K1 k * (uq3K2 k * uq3E2 k) from by
      rw [show uq3K2 k * uq3K1 k = uq3K1 k * uq3K2 k from hKK.symm]; noncomm_ring]
    rw [sect3_hKE_smul_K2E2, mul_smul_comm,
        show uq3K1 k * (uq3E2 k * uq3K2 k) = uq3K1 k * uq3E2 k * uq3K2 k from by noncomm_ring,
        hK1E2_smul, smul_mul_assoc, smul_smul,
        show uq3E2 k * uq3K1 k * uq3K2 k = uq3E2 k * uq3K2 k * uq3K1 k from by
          rw [mul_assoc, hKK, ← mul_assoc]]
    congr 1; rw [← T_add]; norm_num
  rw [hK2E2K1, hK2K1E2, smul_smul]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      x + s • x - t • x = (1 + s - t) • x := by intros; module
  rw [factor]
  have hcoef : (1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 + T 2 - (T 2 + T 0) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdE21_10_E1E2 :
    uq3K1 k * uq3E2 k * uq3K2 k + uq3K1 k * uq3K2 k * uq3E2 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3K1 k * uq3K2 k) = 0 := by
  have hK1E2_smul := sect3_hKE_smul_K1E2 k
  have hK2E2_smul := sect3_hKE_smul_K2E2 k
  have hKK := uq3_K1K2_comm k
  have hK1E2K2 : uq3K1 k * uq3E2 k * uq3K2 k =
      (T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3K1 k * uq3K2 k) := by
    rw [hK1E2_smul, smul_mul_assoc]
  have hK1K2E2 : uq3K1 k * uq3K2 k * uq3E2 k =
      (T 1 : LaurentPolynomial k) • (uq3E2 k * uq3K1 k * uq3K2 k) := by
    rw [show uq3K1 k * uq3K2 k = uq3K2 k * uq3K1 k from hKK]
    rw [show uq3K2 k * uq3K1 k * uq3E2 k = uq3K2 k * (uq3K1 k * uq3E2 k) from by noncomm_ring,
        hK1E2_smul, mul_smul_comm,
        show uq3K2 k * (uq3E2 k * uq3K1 k) = uq3K2 k * uq3E2 k * uq3K1 k from by noncomm_ring,
        hK2E2_smul, smul_mul_assoc, smul_smul]
    rw [show uq3E2 k * uq3K2 k * uq3K1 k = uq3E2 k * uq3K1 k * uq3K2 k from by
      rw [mul_assoc, ← hKK, ← mul_assoc]]
    congr 1; rw [← T_add]; norm_num
  rw [hK1E2K2, hK1K2E2]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      s • x + t • x - (T 1 + T (-1) : LaurentPolynomial k) • x =
      (s + t - (T 1 + T (-1))) • x := by intros; module
  rw [factor]
  have hcoef : (T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k) = 0 := by ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdE21_11 :
    (uq3E2 k * uq3K2 k * uq3E1 k + uq3K2 k * uq3E2 k * uq3E1 k +
     uq3E1 k * uq3E2 k * uq3K2 k + uq3E1 k * uq3K2 k * uq3E2 k) -
    (T 1 + T (-1) : LaurentPolynomial k) •
      (uq3E2 k * uq3E1 k * uq3K2 k + uq3K2 k * uq3E1 k * uq3E2 k) = 0 := by
  have hK2E2 := sect3_hKE_smul_K2E2 k
  have hK2E1 := sect3_hKE_smul_K2E1 k
  -- Reduce atoms to A := E2·E1·K2 and B := E1·E2·K2
  have hE2K2E1 : uq3E2 k * uq3K2 k * uq3E1 k =
      (T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3E1 k * uq3K2 k) := by
    rw [show uq3E2 k * uq3K2 k * uq3E1 k = uq3E2 k * (uq3K2 k * uq3E1 k) from by noncomm_ring,
        hK2E1]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK2E2E1 : uq3K2 k * uq3E2 k * uq3E1 k =
      (T 1 : LaurentPolynomial k) • (uq3E2 k * uq3E1 k * uq3K2 k) := by
    rw [hK2E2, smul_mul_assoc,
        show uq3E2 k * uq3K2 k * uq3E1 k = uq3E2 k * (uq3K2 k * uq3E1 k) from by noncomm_ring,
        hK2E1, mul_smul_comm, smul_smul,
        show uq3E2 k * (uq3E1 k * uq3K2 k) = uq3E2 k * uq3E1 k * uq3K2 k from by noncomm_ring]
    congr 1; rw [← T_add]; norm_num
  have hE1K2E2 : uq3E1 k * uq3K2 k * uq3E2 k =
      (T 2 : LaurentPolynomial k) • (uq3E1 k * uq3E2 k * uq3K2 k) := by
    rw [show uq3E1 k * uq3K2 k * uq3E2 k = uq3E1 k * (uq3K2 k * uq3E2 k) from by noncomm_ring,
        hK2E2]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK2E1E2 : uq3K2 k * uq3E1 k * uq3E2 k =
      (T 1 : LaurentPolynomial k) • (uq3E1 k * uq3E2 k * uq3K2 k) := by
    rw [hK2E1, smul_mul_assoc,
        show uq3E1 k * uq3K2 k * uq3E2 k = uq3E1 k * (uq3K2 k * uq3E2 k) from by noncomm_ring,
        hK2E2, mul_smul_comm, smul_smul,
        show uq3E1 k * (uq3E2 k * uq3K2 k) = uq3E1 k * uq3E2 k * uq3K2 k from by noncomm_ring]
    congr 1; rw [← T_add]; norm_num
  rw [hE2K2E1, hK2E2E1, hE1K2E2, hK2E1E2]
  have factor : ∀ (a b : Uqsl3 k),
      ((T (-1) : LaurentPolynomial k) • a + (T 1 : LaurentPolynomial k) • a +
       b + (T 2 : LaurentPolynomial k) • b) -
      ((T 1 + T (-1) : LaurentPolynomial k)) • (a + (T 1 : LaurentPolynomial k) • b) =
      ((T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k)) • a +
      ((1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k)) • b := by intros; module
  rw [factor]
  have hcoef_A : (T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k) = 0 := by ring
  have hcoef_B : (1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 + T 2 - (T 2 + T 0) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef_A, hcoef_B, zero_smul, zero_smul, add_zero]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem comulFreeAlg3_SerreE21 :
    comulFreeAlg3 k
      (gen3 k E2 * gen3 k E2 * gen3 k E1 + gen3 k E1 * gen3 k E2 * gen3 k E2) =
    comulFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k E2 * gen3 k E1 * gen3 k E2) := by
  rw [← sub_eq_zero, ← map_sub]
  simp only [scal3', map_sub, map_add, map_mul, AlgHom.commutes,
             comulFreeAlg3_ι, comulOnGen3, mul_add, add_mul,
             Algebra.TensorProduct.algebraMap_apply,
             Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [← Algebra.smul_def, smul_mul_assoc, smul_add, smul_sub]
  simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']
  let phi_LL : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip
      (uq3K2 k * uq3K2 k * uq3K1 k)
  let phi_RR : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (1 : Uqsl3 k)
  have hSerreS := sect3_hSerreE21_smul k
  have hSect00 :
      phi_LL (uq3E2 k * uq3E2 k * uq3E1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3E1 k * uq3E2 k) +
        uq3E1 k * uq3E2 k * uq3E2 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_LL
  have hSect21 :
      phi_RR (uq3E2 k * uq3E2 k * uq3E1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3E1 k * uq3E2 k) +
        uq3E1 k * uq3E2 k * uq3E2 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_RR
  rw [map_add phi_LL, map_sub phi_LL,
      LinearMap.map_smul_of_tower phi_LL] at hSect00
  rw [map_add phi_RR, map_sub phi_RR,
      LinearMap.map_smul_of_tower phi_RR] at hSect21
  simp only [phi_LL, phi_RR, LinearMap.flip_apply, TensorProduct.mk_apply]
    at hSect00 hSect21
  have hUqId01 := sect3_hUqIdE21_20 k
  let phi_01 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E2 k * uq3E2 k)
  have hSect01 :
      phi_01 (uq3K2 k * uq3K2 k * uq3E1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3K2 k * uq3E1 k * uq3K2 k) +
        uq3E1 k * uq3K2 k * uq3K2 k) = 0 := by
    rw [hUqId01]; exact map_zero phi_01
  rw [map_add phi_01, map_sub phi_01,
      LinearMap.map_smul_of_tower phi_01] at hSect01
  simp only [phi_01, TensorProduct.mk_apply] at hSect01
  have hUqId20 := sect3_hUqIdE21_01 k
  let phi_20 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E1 k)
  have hSect20 :
      phi_20 (uq3E2 k * uq3E2 k * uq3K1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3K1 k * uq3E2 k) +
        uq3K1 k * uq3E2 k * uq3E2 k) = 0 := by
    rw [hUqId20]; exact map_zero phi_20
  rw [map_add phi_20, map_sub phi_20,
      LinearMap.map_smul_of_tower phi_20] at hSect20
  simp only [phi_20, TensorProduct.mk_apply] at hSect20
  have hUqId10a := sect3_hUqIdE21_10_E2E1 k
  let phi_10a : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E2 k * uq3E1 k)
  have hSect10a :
      phi_10a (uq3E2 k * uq3K2 k * uq3K1 k + uq3K2 k * uq3E2 k * uq3K1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3K2 k * uq3K1 k * uq3E2 k)) = 0 := by
    rw [hUqId10a]; exact map_zero phi_10a
  rw [map_sub phi_10a, map_add phi_10a,
      LinearMap.map_smul_of_tower phi_10a] at hSect10a
  simp only [phi_10a, TensorProduct.mk_apply] at hSect10a
  have hUqId10b := sect3_hUqIdE21_10_E1E2 k
  let phi_10b : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E1 k * uq3E2 k)
  have hSect10b :
      phi_10b (uq3K1 k * uq3E2 k * uq3K2 k + uq3K1 k * uq3K2 k * uq3E2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3E2 k * uq3K1 k * uq3K2 k)) = 0 := by
    rw [hUqId10b]; exact map_zero phi_10b
  rw [map_sub phi_10b, map_add phi_10b,
      LinearMap.map_smul_of_tower phi_10b] at hSect10b
  simp only [phi_10b, TensorProduct.mk_apply] at hSect10b
  have hUqId11 := sect3_hUqIdE21_11 k
  let phi_11 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k) (uq3E2 k)
  have hSect11 :
      phi_11 ((uq3E2 k * uq3K2 k * uq3E1 k + uq3K2 k * uq3E2 k * uq3E1 k +
                uq3E1 k * uq3E2 k * uq3K2 k + uq3E1 k * uq3K2 k * uq3E2 k) -
        (T 1 + T (-1) : LaurentPolynomial k) •
          (uq3E2 k * uq3E1 k * uq3K2 k + uq3K2 k * uq3E1 k * uq3E2 k)) = 0 := by
    rw [hUqId11]; exact map_zero phi_11
  rw [map_sub phi_11, map_add phi_11, map_add phi_11, map_add phi_11,
      LinearMap.map_smul_of_tower phi_11, map_add phi_11] at hSect11
  simp only [phi_11, TensorProduct.mk_apply, TensorProduct.tmul_add, smul_add] at hSect11
  -- K-K commute helpers (analogous to E12 case)
  have hKK : uq3K1 k * uq3K2 k = uq3K2 k * uq3K1 k := uq3_K1K2_comm k
  have hKKK1 : uq3K1 k * uq3K2 k * uq3K2 k = uq3K2 k * uq3K2 k * uq3K1 k := by
    rw [hKK, mul_assoc, hKK, ← mul_assoc]
  have hKKK2 : uq3K2 k * uq3K1 k * uq3K2 k = uq3K2 k * uq3K2 k * uq3K1 k := by
    rw [mul_assoc, hKK, ← mul_assoc]
  have hKKK3 : uq3K1 k * uq3K2 k * uq3E2 k = uq3K2 k * uq3K1 k * uq3E2 k := by rw [hKK]
  simp_rw [hKKK1, hKKK2, hKKK3]
  clear hSerreS hUqId01 hUqId20 hUqId10a hUqId10b hUqId11
  clear phi_LL phi_RR phi_01 phi_20 phi_10a phi_10b phi_11
  simp only [add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
             TensorProduct.smul_tmul'] at hSect00 hSect21 hSect01 hSect20 hSect10a hSect10b hSect11 ⊢
  linear_combination (norm := skip)
    hSect00 + hSect21 + hSect01 + hSect20 + hSect10a + hSect10b + hSect11
  simp_rw [hKKK3]
  abel!

-- === Sector identity helpers for SerreF12 (F-side: K⁻¹·F commutations) ===

private theorem sect3_hUqIdF12_20 :
    uq3K1inv k * uq3K1inv k * uq3F2 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3K1inv k * uq3F2 k * uq3K1inv k) +
    uq3F2 k * uq3K1inv k * uq3K1inv k = 0 := by
  have hKF_smul := sect3_hKinvF_smul_K1invF2 k
  have hKF_at := sect3_hKinvF_at_K1invF2 k
  have hK2F2 : uq3K1inv k * uq3K1inv k * uq3F2 k =
      (T (-2) : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k * uq3K1inv k) := by
    rw [hKF_at, hKF_smul]; simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK1F2K1 : uq3K1inv k * uq3F2 k * uq3K1inv k =
      (T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k * uq3K1inv k) := by
    rw [hKF_smul]; simp only [smul_mul_assoc]
  rw [hK2F2, hK1F2K1, smul_smul]
  have factor : ∀ (r s : LaurentPolynomial k) (x : Uqsl3 k),
      r • x - s • x + x = (r - s + 1) • x := by intros; module
  rw [factor]
  have hcoef : (T (-2) - (T 1 + T (-1)) * T (-1) + 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show T (-2) - (T 0 + T (-2)) + 1 = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdF12_01 :
    uq3F1 k * uq3F1 k * uq3K2inv k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k * uq3F1 k) +
    uq3K2inv k * uq3F1 k * uq3F1 k = 0 := by
  have hKF_smul := sect3_hKinvF_smul_K2invF1 k
  have hKF_at := sect3_hKinvF_at_K2invF1 k
  have hF1K2F1 : uq3F1 k * uq3K2inv k * uq3F1 k =
      (T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3F1 k * uq3K2inv k) := by
    rw [show uq3F1 k * uq3K2inv k * uq3F1 k = uq3F1 k * (uq3K2inv k * uq3F1 k) from by noncomm_ring,
        hKF_smul]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK2F1F1 : uq3K2inv k * uq3F1 k * uq3F1 k =
      (T (-2) : LaurentPolynomial k) • (uq3F1 k * uq3F1 k * uq3K2inv k) := by
    rw [show uq3K2inv k * uq3F1 k * uq3F1 k = (uq3K2inv k * uq3F1 k) * uq3F1 k from by noncomm_ring,
        hKF_smul]
    simp only [smul_mul_assoc]
    rw [show uq3F1 k * uq3K2inv k * uq3F1 k = uq3F1 k * (uq3K2inv k * uq3F1 k) from by noncomm_ring,
        hKF_smul]
    simp only [mul_smul_comm, smul_smul, ← mul_assoc]
    congr 1; rw [← T_add]; norm_num
  rw [hF1K2F1, hK2F1F1, smul_smul]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      x - s • x + t • x = (1 - s + t) • x := by intros; module
  rw [factor]
  have hcoef : (1 - (T 1 + T (-1)) * T (-1) + T (-2) : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 - (T 0 + T (-2)) + T (-2) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdF12_10_F1F2 :
    uq3F1 k * uq3K1inv k * uq3K2inv k + uq3K1inv k * uq3F1 k * uq3K2inv k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3K1inv k * uq3K2inv k * uq3F1 k) = 0 := by
  have hK1invF1_at := sect3_hKinvF_at_K1invF1 k
  have hK2invF1_smul := sect3_hKinvF_smul_K2invF1 k
  have hKK := uq3_K1inv_K2inv_comm k
  have hF1K1K2 : uq3F1 k * uq3K1inv k * uq3K2inv k = uq3F1 k * uq3K1inv k * uq3K2inv k := rfl
  have hK1F1K2 : uq3K1inv k * uq3F1 k * uq3K2inv k =
      (T 2 : LaurentPolynomial k) • (uq3F1 k * uq3K1inv k * uq3K2inv k) := by
    have : uq3K1inv k * uq3F1 k * uq3K2inv k =
        (T 2 : LaurentPolynomial k) • (uq3F1 k * uq3K1inv k) * uq3K2inv k := by
      rw [show uq3K1inv k * uq3F1 k = (T 2 : LaurentPolynomial k) • (uq3F1 k * uq3K1inv k) from
        sect3_hKinvF_smul_K1invF1 k]
    rw [this, smul_mul_assoc]
  have hK1K2F1 : uq3K1inv k * uq3K2inv k * uq3F1 k =
      (T 1 : LaurentPolynomial k) • (uq3F1 k * uq3K1inv k * uq3K2inv k) := by
    rw [show uq3K1inv k * uq3K2inv k * uq3F1 k = uq3K2inv k * (uq3K1inv k * uq3F1 k) from by
      rw [show uq3K1inv k * uq3K2inv k = uq3K2inv k * uq3K1inv k from hKK]; noncomm_ring]
    rw [sect3_hKinvF_smul_K1invF1, mul_smul_comm,
        show uq3K2inv k * (uq3F1 k * uq3K1inv k) = uq3K2inv k * uq3F1 k * uq3K1inv k from by noncomm_ring,
        hK2invF1_smul, smul_mul_assoc, smul_smul,
        show uq3F1 k * uq3K2inv k * uq3K1inv k = uq3F1 k * uq3K1inv k * uq3K2inv k from by
          rw [mul_assoc, ← hKK, ← mul_assoc]]
    congr 1; rw [← T_add]; norm_num
  rw [hK1F1K2, hK1K2F1, smul_smul]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      x + s • x - t • x = (1 + s - t) • x := by intros; module
  rw [factor]
  have hcoef : (1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 + T 2 - (T 2 + T 0) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdF12_10_F2F1 :
    uq3K2inv k * uq3F1 k * uq3K1inv k + uq3K2inv k * uq3K1inv k * uq3F1 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k * uq3K1inv k) = 0 := by
  have hK2invF1_smul := sect3_hKinvF_smul_K2invF1 k
  have hK1invF1_smul := sect3_hKinvF_smul_K1invF1 k
  have hKK := uq3_K1inv_K2inv_comm k
  have hK2F1K1 : uq3K2inv k * uq3F1 k * uq3K1inv k =
      (T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k * uq3K1inv k) := by
    rw [hK2invF1_smul, smul_mul_assoc]
  have hK2K1F1 : uq3K2inv k * uq3K1inv k * uq3F1 k =
      (T 1 : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k * uq3K1inv k) := by
    rw [show uq3K2inv k * uq3K1inv k = uq3K1inv k * uq3K2inv k from hKK.symm]
    rw [show uq3K1inv k * uq3K2inv k * uq3F1 k = uq3K1inv k * (uq3K2inv k * uq3F1 k) from by noncomm_ring,
        hK2invF1_smul, mul_smul_comm,
        show uq3K1inv k * (uq3F1 k * uq3K2inv k) = uq3K1inv k * uq3F1 k * uq3K2inv k from by noncomm_ring,
        hK1invF1_smul, smul_mul_assoc, smul_smul]
    rw [show uq3F1 k * uq3K1inv k * uq3K2inv k = uq3F1 k * uq3K2inv k * uq3K1inv k from by
      rw [mul_assoc, hKK, ← mul_assoc]]
    congr 1; rw [← T_add]; norm_num
  rw [hK2F1K1, hK2K1F1]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      s • x + t • x - (T 1 + T (-1) : LaurentPolynomial k) • x =
      (s + t - (T 1 + T (-1))) • x := by intros; module
  rw [factor]
  have hcoef : (T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k) = 0 := by ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdF12_11 :
    (uq3F1 k * uq3K1inv k * uq3F2 k + uq3K1inv k * uq3F1 k * uq3F2 k +
     uq3F2 k * uq3F1 k * uq3K1inv k + uq3F2 k * uq3K1inv k * uq3F1 k) -
    (T 1 + T (-1) : LaurentPolynomial k) •
      (uq3F1 k * uq3F2 k * uq3K1inv k + uq3K1inv k * uq3F2 k * uq3F1 k) = 0 := by
  have hK1F1 := sect3_hKinvF_smul_K1invF1 k
  have hK1F2 := sect3_hKinvF_smul_K1invF2 k
  have hF1K1F2 : uq3F1 k * uq3K1inv k * uq3F2 k =
      (T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3F2 k * uq3K1inv k) := by
    rw [show uq3F1 k * uq3K1inv k * uq3F2 k = uq3F1 k * (uq3K1inv k * uq3F2 k) from by noncomm_ring,
        hK1F2]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK1F1F2 : uq3K1inv k * uq3F1 k * uq3F2 k =
      (T 1 : LaurentPolynomial k) • (uq3F1 k * uq3F2 k * uq3K1inv k) := by
    rw [hK1F1, smul_mul_assoc,
        show uq3F1 k * uq3K1inv k * uq3F2 k = uq3F1 k * (uq3K1inv k * uq3F2 k) from by noncomm_ring,
        hK1F2, mul_smul_comm, smul_smul,
        show uq3F1 k * (uq3F2 k * uq3K1inv k) = uq3F1 k * uq3F2 k * uq3K1inv k from by noncomm_ring]
    congr 1; rw [← T_add]; norm_num
  have hF2K1F1 : uq3F2 k * uq3K1inv k * uq3F1 k =
      (T 2 : LaurentPolynomial k) • (uq3F2 k * uq3F1 k * uq3K1inv k) := by
    rw [show uq3F2 k * uq3K1inv k * uq3F1 k = uq3F2 k * (uq3K1inv k * uq3F1 k) from by noncomm_ring,
        hK1F1]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK1F2F1 : uq3K1inv k * uq3F2 k * uq3F1 k =
      (T 1 : LaurentPolynomial k) • (uq3F2 k * uq3F1 k * uq3K1inv k) := by
    rw [hK1F2, smul_mul_assoc,
        show uq3F2 k * uq3K1inv k * uq3F1 k = uq3F2 k * (uq3K1inv k * uq3F1 k) from by noncomm_ring,
        hK1F1, mul_smul_comm, smul_smul,
        show uq3F2 k * (uq3F1 k * uq3K1inv k) = uq3F2 k * uq3F1 k * uq3K1inv k from by noncomm_ring]
    congr 1; rw [← T_add]; norm_num
  rw [hF1K1F2, hK1F1F2, hF2K1F1, hK1F2F1]
  have factor : ∀ (a b : Uqsl3 k),
      ((T (-1) : LaurentPolynomial k) • a + (T 1 : LaurentPolynomial k) • a +
       b + (T 2 : LaurentPolynomial k) • b) -
      ((T 1 + T (-1) : LaurentPolynomial k)) • (a + (T 1 : LaurentPolynomial k) • b) =
      ((T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k)) • a +
      ((1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k)) • b := by intros; module
  rw [factor]
  have hcoef_A : (T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k) = 0 := by ring
  have hcoef_B : (1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 + T 2 - (T 2 + T 0) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef_A, hcoef_B, zero_smul, zero_smul, add_zero]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem comulFreeAlg3_SerreF12 :
    comulFreeAlg3 k
      (gen3 k F1 * gen3 k F1 * gen3 k F2 + gen3 k F2 * gen3 k F1 * gen3 k F1) =
    comulFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k F1 * gen3 k F2 * gen3 k F1) := by
  rw [← sub_eq_zero, ← map_sub]
  simp only [scal3', map_sub, map_add, map_mul, AlgHom.commutes,
             comulFreeAlg3_ι, comulOnGen3, mul_add, add_mul,
             Algebra.TensorProduct.algebraMap_apply,
             Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [← Algebra.smul_def, smul_mul_assoc, smul_add, smul_sub]
  -- F-Serre flips left/right tensor convention. Sector (0,0) = (Serre on F's) ⊗ 1.
  -- Sector (j=2,k=1) = (K⁻¹·K⁻¹·K⁻¹) ⊗ Serre on F's.
  let phi_LL : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (1 : Uqsl3 k)
  let phi_RR : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)
      (uq3K1inv k * uq3K1inv k * uq3K2inv k)
  have hSerreS := sect3_hSerreF12_smul k
  have hSect00 :
      phi_LL (uq3F1 k * uq3F1 k * uq3F2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3F2 k * uq3F1 k) +
        uq3F2 k * uq3F1 k * uq3F1 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_LL
  have hSect21 :
      phi_RR (uq3F1 k * uq3F1 k * uq3F2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3F2 k * uq3F1 k) +
        uq3F2 k * uq3F1 k * uq3F1 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_RR
  rw [map_add phi_LL, map_sub phi_LL,
      LinearMap.map_smul_of_tower phi_LL] at hSect00
  rw [map_add phi_RR, map_sub phi_RR,
      LinearMap.map_smul_of_tower phi_RR] at hSect21
  simp only [phi_LL, phi_RR, LinearMap.flip_apply, TensorProduct.mk_apply]
    at hSect00 hSect21
  -- Sector (0,1): right factor = F1², left = K⁻¹·K⁻¹·F2 mix
  have hUqId01 := sect3_hUqIdF12_20 k
  let phi_01 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F1 k * uq3F1 k)
  have hSect01 :
      phi_01 (uq3K1inv k * uq3K1inv k * uq3F2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3K1inv k * uq3F2 k * uq3K1inv k) +
        uq3F2 k * uq3K1inv k * uq3K1inv k) = 0 := by
    rw [hUqId01]; exact map_zero phi_01
  rw [map_add phi_01, map_sub phi_01,
      LinearMap.map_smul_of_tower phi_01] at hSect01
  simp only [phi_01, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect01
  -- Sector (2,0): right factor = F2, left = F1·F1·K⁻¹ mix
  have hUqId20 := sect3_hUqIdF12_01 k
  let phi_20 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F2 k)
  have hSect20 :
      phi_20 (uq3F1 k * uq3F1 k * uq3K2inv k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k * uq3F1 k) +
        uq3K2inv k * uq3F1 k * uq3F1 k) = 0 := by
    rw [hUqId20]; exact map_zero phi_20
  rw [map_add phi_20, map_sub phi_20,
      LinearMap.map_smul_of_tower phi_20] at hSect20
  simp only [phi_20, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect20
  -- Sector (1,0) F1F2 right
  have hUqId10a := sect3_hUqIdF12_10_F1F2 k
  let phi_10a : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F1 k * uq3F2 k)
  have hSect10a :
      phi_10a (uq3F1 k * uq3K1inv k * uq3K2inv k + uq3K1inv k * uq3F1 k * uq3K2inv k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3K1inv k * uq3K2inv k * uq3F1 k)) = 0 := by
    rw [hUqId10a]; exact map_zero phi_10a
  rw [map_sub phi_10a, map_add phi_10a,
      LinearMap.map_smul_of_tower phi_10a] at hSect10a
  simp only [phi_10a, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect10a
  -- Sector (1,0) F2F1 right
  have hUqId10b := sect3_hUqIdF12_10_F2F1 k
  let phi_10b : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F2 k * uq3F1 k)
  have hSect10b :
      phi_10b (uq3K2inv k * uq3F1 k * uq3K1inv k + uq3K2inv k * uq3K1inv k * uq3F1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k * uq3K1inv k)) = 0 := by
    rw [hUqId10b]; exact map_zero phi_10b
  rw [map_sub phi_10b, map_add phi_10b,
      LinearMap.map_smul_of_tower phi_10b] at hSect10b
  simp only [phi_10b, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect10b
  -- Sector (1,1): right factor = F1
  have hUqId11 := sect3_hUqIdF12_11 k
  let phi_11 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F1 k)
  have hSect11 :
      phi_11 ((uq3F1 k * uq3K1inv k * uq3F2 k + uq3K1inv k * uq3F1 k * uq3F2 k +
                uq3F2 k * uq3F1 k * uq3K1inv k + uq3F2 k * uq3K1inv k * uq3F1 k) -
        (T 1 + T (-1) : LaurentPolynomial k) •
          (uq3F1 k * uq3F2 k * uq3K1inv k + uq3K1inv k * uq3F2 k * uq3F1 k)) = 0 := by
    rw [hUqId11]; exact map_zero phi_11
  rw [map_sub phi_11, map_add phi_11, map_add phi_11, map_add phi_11,
      LinearMap.map_smul_of_tower phi_11, map_add phi_11] at hSect11
  simp only [phi_11, LinearMap.flip_apply, TensorProduct.mk_apply,
             TensorProduct.add_tmul, smul_add] at hSect11
  -- K⁻¹-K⁻¹ commute helpers
  have hKK : uq3K2inv k * uq3K1inv k = uq3K1inv k * uq3K2inv k :=
    (uq3_K1inv_K2inv_comm k).symm
  have hKKK1 : uq3K2inv k * uq3K1inv k * uq3K1inv k =
      uq3K1inv k * uq3K1inv k * uq3K2inv k := by
    rw [hKK, mul_assoc, hKK, ← mul_assoc]
  have hKKK2 : uq3K1inv k * uq3K2inv k * uq3K1inv k =
      uq3K1inv k * uq3K1inv k * uq3K2inv k := by
    rw [mul_assoc, hKK, ← mul_assoc]
  have hKKK3 : uq3F1 k * uq3K2inv k * uq3K1inv k =
      uq3F1 k * uq3K1inv k * uq3K2inv k := by
    rw [mul_assoc, hKK, ← mul_assoc]
  simp_rw [hKKK1, hKKK2, hKKK3]
  clear hSerreS hUqId01 hUqId20 hUqId10a hUqId10b hUqId11
  clear phi_LL phi_RR phi_01 phi_20 phi_10a phi_10b phi_11
  simp only [add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
             TensorProduct.smul_tmul'] at hSect00 hSect21 hSect01 hSect20 hSect10a hSect10b hSect11 ⊢
  linear_combination (norm := skip)
    hSect00 + hSect21 + hSect01 + hSect20 + hSect10a + hSect10b + hSect11
  simp_rw [hKKK3]
  abel!

-- === Sector identity helpers for SerreF21 (mechanical 1↔2 swap of F12 sectors) ===

private theorem sect3_hUqIdF21_20 :
    uq3K2inv k * uq3K2inv k * uq3F1 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3K2inv k * uq3F1 k * uq3K2inv k) +
    uq3F1 k * uq3K2inv k * uq3K2inv k = 0 := by
  have hKF_smul := sect3_hKinvF_smul_K2invF1 k
  have hKF_at := sect3_hKinvF_at_K2invF1 k
  have hK2F1 : uq3K2inv k * uq3K2inv k * uq3F1 k =
      (T (-2) : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k * uq3K2inv k) := by
    rw [hKF_at, hKF_smul]; simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK2F1K2 : uq3K2inv k * uq3F1 k * uq3K2inv k =
      (T (-1) : LaurentPolynomial k) • (uq3F1 k * uq3K2inv k * uq3K2inv k) := by
    rw [hKF_smul]; simp only [smul_mul_assoc]
  rw [hK2F1, hK2F1K2, smul_smul]
  have factor : ∀ (r s : LaurentPolynomial k) (x : Uqsl3 k),
      r • x - s • x + x = (r - s + 1) • x := by intros; module
  rw [factor]
  have hcoef : (T (-2) - (T 1 + T (-1)) * T (-1) + 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show T (-2) - (T 0 + T (-2)) + 1 = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdF21_01 :
    uq3F2 k * uq3F2 k * uq3K1inv k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k * uq3F2 k) +
    uq3K1inv k * uq3F2 k * uq3F2 k = 0 := by
  have hKF_smul := sect3_hKinvF_smul_K1invF2 k
  have hKF_at := sect3_hKinvF_at_K1invF2 k
  have hF2K1F2 : uq3F2 k * uq3K1inv k * uq3F2 k =
      (T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3F2 k * uq3K1inv k) := by
    rw [show uq3F2 k * uq3K1inv k * uq3F2 k = uq3F2 k * (uq3K1inv k * uq3F2 k) from by noncomm_ring,
        hKF_smul]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK1F2F2 : uq3K1inv k * uq3F2 k * uq3F2 k =
      (T (-2) : LaurentPolynomial k) • (uq3F2 k * uq3F2 k * uq3K1inv k) := by
    rw [show uq3K1inv k * uq3F2 k * uq3F2 k = (uq3K1inv k * uq3F2 k) * uq3F2 k from by noncomm_ring,
        hKF_smul]
    simp only [smul_mul_assoc]
    rw [show uq3F2 k * uq3K1inv k * uq3F2 k = uq3F2 k * (uq3K1inv k * uq3F2 k) from by noncomm_ring,
        hKF_smul]
    simp only [mul_smul_comm, smul_smul, ← mul_assoc]
    congr 1; rw [← T_add]; norm_num
  rw [hF2K1F2, hK1F2F2, smul_smul]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      x - s • x + t • x = (1 - s + t) • x := by intros; module
  rw [factor]
  have hcoef : (1 - (T 1 + T (-1)) * T (-1) + T (-2) : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 - (T 0 + T (-2)) + T (-2) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdF21_10_F2F1 :
    uq3F2 k * uq3K2inv k * uq3K1inv k + uq3K2inv k * uq3F2 k * uq3K1inv k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3K2inv k * uq3K1inv k * uq3F2 k) = 0 := by
  have hK2invF2_at := sect3_hKinvF_at_K2invF2 k
  have hK1invF2_smul := sect3_hKinvF_smul_K1invF2 k
  have hKK := uq3_K1inv_K2inv_comm k
  have hF2K2K1 : uq3F2 k * uq3K2inv k * uq3K1inv k = uq3F2 k * uq3K2inv k * uq3K1inv k := rfl
  have hK2F2K1 : uq3K2inv k * uq3F2 k * uq3K1inv k =
      (T 2 : LaurentPolynomial k) • (uq3F2 k * uq3K2inv k * uq3K1inv k) := by
    have : uq3K2inv k * uq3F2 k * uq3K1inv k =
        (T 2 : LaurentPolynomial k) • (uq3F2 k * uq3K2inv k) * uq3K1inv k := by
      rw [show uq3K2inv k * uq3F2 k = (T 2 : LaurentPolynomial k) • (uq3F2 k * uq3K2inv k) from
        sect3_hKinvF_smul_K2invF2 k]
    rw [this, smul_mul_assoc]
  have hK2K1F2 : uq3K2inv k * uq3K1inv k * uq3F2 k =
      (T 1 : LaurentPolynomial k) • (uq3F2 k * uq3K2inv k * uq3K1inv k) := by
    rw [show uq3K2inv k * uq3K1inv k * uq3F2 k = uq3K1inv k * (uq3K2inv k * uq3F2 k) from by
      rw [show uq3K2inv k * uq3K1inv k = uq3K1inv k * uq3K2inv k from hKK.symm]; noncomm_ring]
    rw [sect3_hKinvF_smul_K2invF2, mul_smul_comm,
        show uq3K1inv k * (uq3F2 k * uq3K2inv k) = uq3K1inv k * uq3F2 k * uq3K2inv k from by noncomm_ring,
        hK1invF2_smul, smul_mul_assoc, smul_smul,
        show uq3F2 k * uq3K1inv k * uq3K2inv k = uq3F2 k * uq3K2inv k * uq3K1inv k from by
          rw [mul_assoc, hKK, ← mul_assoc]]
    congr 1; rw [← T_add]; norm_num
  rw [hK2F2K1, hK2K1F2, smul_smul]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      x + s • x - t • x = (1 + s - t) • x := by intros; module
  rw [factor]
  have hcoef : (1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 + T 2 - (T 2 + T 0) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdF21_10_F1F2 :
    uq3K1inv k * uq3F2 k * uq3K2inv k + uq3K1inv k * uq3K2inv k * uq3F2 k -
    (T 1 + T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k * uq3K2inv k) = 0 := by
  have hK1invF2_smul := sect3_hKinvF_smul_K1invF2 k
  have hK2invF2_smul := sect3_hKinvF_smul_K2invF2 k
  have hKK := uq3_K1inv_K2inv_comm k
  have hK1F2K2 : uq3K1inv k * uq3F2 k * uq3K2inv k =
      (T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k * uq3K2inv k) := by
    rw [hK1invF2_smul, smul_mul_assoc]
  have hK1K2F2 : uq3K1inv k * uq3K2inv k * uq3F2 k =
      (T 1 : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k * uq3K2inv k) := by
    rw [show uq3K1inv k * uq3K2inv k = uq3K2inv k * uq3K1inv k from hKK]
    rw [show uq3K2inv k * uq3K1inv k * uq3F2 k = uq3K2inv k * (uq3K1inv k * uq3F2 k) from by noncomm_ring,
        hK1invF2_smul, mul_smul_comm,
        show uq3K2inv k * (uq3F2 k * uq3K1inv k) = uq3K2inv k * uq3F2 k * uq3K1inv k from by noncomm_ring,
        hK2invF2_smul, smul_mul_assoc, smul_smul]
    rw [show uq3F2 k * uq3K2inv k * uq3K1inv k = uq3F2 k * uq3K1inv k * uq3K2inv k from by
      rw [mul_assoc, ← hKK, ← mul_assoc]]
    congr 1; rw [← T_add]; norm_num
  rw [hK1F2K2, hK1K2F2]
  have factor : ∀ (s t : LaurentPolynomial k) (x : Uqsl3 k),
      s • x + t • x - (T 1 + T (-1) : LaurentPolynomial k) • x =
      (s + t - (T 1 + T (-1))) • x := by intros; module
  rw [factor]
  have hcoef : (T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k) = 0 := by ring
  rw [hcoef, zero_smul]

private theorem sect3_hUqIdF21_11 :
    (uq3F2 k * uq3K2inv k * uq3F1 k + uq3K2inv k * uq3F2 k * uq3F1 k +
     uq3F1 k * uq3F2 k * uq3K2inv k + uq3F1 k * uq3K2inv k * uq3F2 k) -
    (T 1 + T (-1) : LaurentPolynomial k) •
      (uq3F2 k * uq3F1 k * uq3K2inv k + uq3K2inv k * uq3F1 k * uq3F2 k) = 0 := by
  have hK2F2 := sect3_hKinvF_smul_K2invF2 k
  have hK2F1 := sect3_hKinvF_smul_K2invF1 k
  have hF2K2F1 : uq3F2 k * uq3K2inv k * uq3F1 k =
      (T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3F1 k * uq3K2inv k) := by
    rw [show uq3F2 k * uq3K2inv k * uq3F1 k = uq3F2 k * (uq3K2inv k * uq3F1 k) from by noncomm_ring,
        hK2F1]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK2F2F1 : uq3K2inv k * uq3F2 k * uq3F1 k =
      (T 1 : LaurentPolynomial k) • (uq3F2 k * uq3F1 k * uq3K2inv k) := by
    rw [hK2F2, smul_mul_assoc,
        show uq3F2 k * uq3K2inv k * uq3F1 k = uq3F2 k * (uq3K2inv k * uq3F1 k) from by noncomm_ring,
        hK2F1, mul_smul_comm, smul_smul,
        show uq3F2 k * (uq3F1 k * uq3K2inv k) = uq3F2 k * uq3F1 k * uq3K2inv k from by noncomm_ring]
    congr 1; rw [← T_add]; norm_num
  have hF1K2F2 : uq3F1 k * uq3K2inv k * uq3F2 k =
      (T 2 : LaurentPolynomial k) • (uq3F1 k * uq3F2 k * uq3K2inv k) := by
    rw [show uq3F1 k * uq3K2inv k * uq3F2 k = uq3F1 k * (uq3K2inv k * uq3F2 k) from by noncomm_ring,
        hK2F2]
    simp only [mul_smul_comm, ← mul_assoc]
  have hK2F1F2 : uq3K2inv k * uq3F1 k * uq3F2 k =
      (T 1 : LaurentPolynomial k) • (uq3F1 k * uq3F2 k * uq3K2inv k) := by
    rw [hK2F1, smul_mul_assoc,
        show uq3F1 k * uq3K2inv k * uq3F2 k = uq3F1 k * (uq3K2inv k * uq3F2 k) from by noncomm_ring,
        hK2F2, mul_smul_comm, smul_smul,
        show uq3F1 k * (uq3F2 k * uq3K2inv k) = uq3F1 k * uq3F2 k * uq3K2inv k from by noncomm_ring]
    congr 1; rw [← T_add]; norm_num
  rw [hF2K2F1, hK2F2F1, hF1K2F2, hK2F1F2]
  have factor : ∀ (a b : Uqsl3 k),
      ((T (-1) : LaurentPolynomial k) • a + (T 1 : LaurentPolynomial k) • a +
       b + (T 2 : LaurentPolynomial k) • b) -
      ((T 1 + T (-1) : LaurentPolynomial k)) • (a + (T 1 : LaurentPolynomial k) • b) =
      ((T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k)) • a +
      ((1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k)) • b := by intros; module
  rw [factor]
  have hcoef_A : (T (-1) + T 1 - (T 1 + T (-1)) : LaurentPolynomial k) = 0 := by ring
  have hcoef_B : (1 + T 2 - (T 1 + T (-1)) * T 1 : LaurentPolynomial k) = 0 := by
    rw [add_mul, ← T_add, ← T_add]
    show 1 + T 2 - (T 2 + T 0) = (0 : LaurentPolynomial k)
    rw [T_zero]; ring
  rw [hcoef_A, hcoef_B, zero_smul, zero_smul, add_zero]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem comulFreeAlg3_SerreF21 :
    comulFreeAlg3 k
      (gen3 k F2 * gen3 k F2 * gen3 k F1 + gen3 k F1 * gen3 k F2 * gen3 k F2) =
    comulFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k F2 * gen3 k F1 * gen3 k F2) := by
  rw [← sub_eq_zero, ← map_sub]
  simp only [scal3', map_sub, map_add, map_mul, AlgHom.commutes,
             comulFreeAlg3_ι, comulOnGen3, mul_add, add_mul,
             Algebra.TensorProduct.algebraMap_apply,
             Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [← Algebra.smul_def, smul_mul_assoc, smul_add, smul_sub]
  let phi_LL : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (1 : Uqsl3 k)
  let phi_RR : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)
      (uq3K2inv k * uq3K2inv k * uq3K1inv k)
  have hSerreS := sect3_hSerreF21_smul k
  have hSect00 :
      phi_LL (uq3F2 k * uq3F2 k * uq3F1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3F1 k * uq3F2 k) +
        uq3F1 k * uq3F2 k * uq3F2 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_LL
  have hSect21 :
      phi_RR (uq3F2 k * uq3F2 k * uq3F1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3F1 k * uq3F2 k) +
        uq3F1 k * uq3F2 k * uq3F2 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_RR
  rw [map_add phi_LL, map_sub phi_LL,
      LinearMap.map_smul_of_tower phi_LL] at hSect00
  rw [map_add phi_RR, map_sub phi_RR,
      LinearMap.map_smul_of_tower phi_RR] at hSect21
  simp only [phi_LL, phi_RR, LinearMap.flip_apply, TensorProduct.mk_apply]
    at hSect00 hSect21
  have hUqId01 := sect3_hUqIdF21_20 k
  let phi_01 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F2 k * uq3F2 k)
  have hSect01 :
      phi_01 (uq3K2inv k * uq3K2inv k * uq3F1 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3K2inv k * uq3F1 k * uq3K2inv k) +
        uq3F1 k * uq3K2inv k * uq3K2inv k) = 0 := by
    rw [hUqId01]; exact map_zero phi_01
  rw [map_add phi_01, map_sub phi_01,
      LinearMap.map_smul_of_tower phi_01] at hSect01
  simp only [phi_01, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect01
  have hUqId20 := sect3_hUqIdF21_01 k
  let phi_20 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F1 k)
  have hSect20 :
      phi_20 (uq3F2 k * uq3F2 k * uq3K1inv k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k * uq3F2 k) +
        uq3K1inv k * uq3F2 k * uq3F2 k) = 0 := by
    rw [hUqId20]; exact map_zero phi_20
  rw [map_add phi_20, map_sub phi_20,
      LinearMap.map_smul_of_tower phi_20] at hSect20
  simp only [phi_20, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect20
  have hUqId10a := sect3_hUqIdF21_10_F2F1 k
  let phi_10a : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F2 k * uq3F1 k)
  have hSect10a :
      phi_10a (uq3F2 k * uq3K2inv k * uq3K1inv k + uq3K2inv k * uq3F2 k * uq3K1inv k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3K2inv k * uq3K1inv k * uq3F2 k)) = 0 := by
    rw [hUqId10a]; exact map_zero phi_10a
  rw [map_sub phi_10a, map_add phi_10a,
      LinearMap.map_smul_of_tower phi_10a] at hSect10a
  simp only [phi_10a, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect10a
  have hUqId10b := sect3_hUqIdF21_10_F1F2 k
  let phi_10b : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F1 k * uq3F2 k)
  have hSect10b :
      phi_10b (uq3K1inv k * uq3F2 k * uq3K2inv k + uq3K1inv k * uq3K2inv k * uq3F2 k -
        (T 1 + T (-1) : LaurentPolynomial k) • (uq3F2 k * uq3K1inv k * uq3K2inv k)) = 0 := by
    rw [hUqId10b]; exact map_zero phi_10b
  rw [map_sub phi_10b, map_add phi_10b,
      LinearMap.map_smul_of_tower phi_10b] at hSect10b
  simp only [phi_10b, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect10b
  have hUqId11 := sect3_hUqIdF21_11 k
  let phi_11 : Uqsl3 k →ₗ[LaurentPolynomial k]
      Uqsl3 k ⊗[LaurentPolynomial k] Uqsl3 k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl3 k) (Uqsl3 k)).flip (uq3F2 k)
  have hSect11 :
      phi_11 ((uq3F2 k * uq3K2inv k * uq3F1 k + uq3K2inv k * uq3F2 k * uq3F1 k +
                uq3F1 k * uq3F2 k * uq3K2inv k + uq3F1 k * uq3K2inv k * uq3F2 k) -
        (T 1 + T (-1) : LaurentPolynomial k) •
          (uq3F2 k * uq3F1 k * uq3K2inv k + uq3K2inv k * uq3F1 k * uq3F2 k)) = 0 := by
    rw [hUqId11]; exact map_zero phi_11
  rw [map_sub phi_11, map_add phi_11, map_add phi_11, map_add phi_11,
      LinearMap.map_smul_of_tower phi_11, map_add phi_11] at hSect11
  simp only [phi_11, LinearMap.flip_apply, TensorProduct.mk_apply,
             TensorProduct.add_tmul, smul_add] at hSect11
  have hKK : uq3K1inv k * uq3K2inv k = uq3K2inv k * uq3K1inv k :=
    uq3_K1inv_K2inv_comm k
  have hKKK1 : uq3K1inv k * uq3K2inv k * uq3K2inv k =
      uq3K2inv k * uq3K2inv k * uq3K1inv k := by
    rw [hKK, mul_assoc, hKK, ← mul_assoc]
  have hKKK2 : uq3K2inv k * uq3K1inv k * uq3K2inv k =
      uq3K2inv k * uq3K2inv k * uq3K1inv k := by
    rw [mul_assoc, hKK, ← mul_assoc]
  have hKKK3 : uq3F2 k * uq3K1inv k * uq3K2inv k =
      uq3F2 k * uq3K2inv k * uq3K1inv k := by
    rw [mul_assoc, hKK, ← mul_assoc]
  simp_rw [hKKK1, hKKK2, hKKK3]
  clear hSerreS hUqId01 hUqId20 hUqId10a hUqId10b hUqId11
  clear phi_LL phi_RR phi_01 phi_20 phi_10a phi_10b phi_11
  simp only [add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
             TensorProduct.smul_tmul'] at hSect00 hSect21 hSect01 hSect20 hSect10a hSect10b hSect11 ⊢
  linear_combination (norm := skip)
    hSect00 + hSect21 + hSect01 + hSect20 + hSect10a + hSect10b + hSect11
  simp_rw [hKKK3]
  abel!

private theorem comulFreeAlg3_respects_rel :
    ∀ a b, ChevalleyRelSl3 k a b → comulFreeAlg3 k a = comulFreeAlg3 k b := by
  intro a b hab
  cases hab with
  | K1K1inv => rw [comulFreeAlg3_K1K1inv, map_one]
  | K1invK1 => rw [comulFreeAlg3_K1invK1, map_one]
  | K2K2inv => rw [comulFreeAlg3_K2K2inv, map_one]
  | K2invK2 => rw [comulFreeAlg3_K2invK2, map_one]
  | K1K2 => exact comulFreeAlg3_K1K2 k
  | K1E1 => exact comulFreeAlg3_K1E1 k
  | K1E2 => exact comulFreeAlg3_K1E2 k
  | K2E1 => exact comulFreeAlg3_K2E1 k
  | K2E2 => exact comulFreeAlg3_K2E2 k
  | K1F1 => exact comulFreeAlg3_K1F1 k
  | K1F2 => exact comulFreeAlg3_K1F2 k
  | K2F1 => exact comulFreeAlg3_K2F1 k
  | K2F2 => exact comulFreeAlg3_K2F2 k
  | EF11 => exact comulFreeAlg3_EF11 k
  | EF22 => exact comulFreeAlg3_EF22 k
  | E1F2comm => exact comulFreeAlg3_E1F2comm k
  | E2F1comm => exact comulFreeAlg3_E2F1comm k
  | SerreE12 => exact comulFreeAlg3_SerreE12 k
  | SerreE21 => exact comulFreeAlg3_SerreE21 k
  | SerreF12 => exact comulFreeAlg3_SerreF12 k
  | SerreF21 => exact comulFreeAlg3_SerreF21 k

/-- The coproduct on U_q(sl₃), descended to the quotient. -/
noncomputable def uq3Comul :
    Uqsl3 k →ₐ[LaurentPolynomial k]
    (Uqsl3 k) ⊗[LaurentPolynomial k] (Uqsl3 k) :=
  RingQuot.liftAlgHom (LaurentPolynomial k) ⟨comulFreeAlg3 k, comulFreeAlg3_respects_rel k⟩

/-! ## 2. Counit ε -/

/-- Counit on generators: ε(E_i) = ε(F_i) = 0, ε(K_i) = ε(K_i⁻¹) = 1. -/
private def counitOnGen3 : Uqsl3Gen → LaurentPolynomial k
  | .E1 => 0  | .E2 => 0  | .F1 => 0  | .F2 => 0
  | .K1 => 1  | .K1inv => 1  | .K2 => 1  | .K2inv => 1

/-- Counit lifted to the free algebra. -/
private def counitFreeAlg3 :
    FreeAlgebra (LaurentPolynomial k) Uqsl3Gen →ₐ[LaurentPolynomial k]
    LaurentPolynomial k :=
  FreeAlgebra.lift (LaurentPolynomial k) (counitOnGen3 k)

/-- The counit respects all 21 Chevalley relations.

PROVIDED SOLUTION: All E,F map to 0, all K map to 1. EVERY relation is trivially satisfied.
Proof: intro a b hab; cases hab <;> simp [counitFreeAlg3, counitOnGen3,
  FreeAlgebra.lift_ι_apply, map_mul, map_add, AlgHom.commutes] <;> ring
The key is that after simp + ring, all 21 cases reduce to 0=0 or 1=1.
This is the same strategy that worked for Uqsl2AffineHopf.lean's counit
(which Aristotle proved with simp +decide in the previous run).
If simp+ring doesn't close all cases, try decide or norm_num for the remaining ones. -/
private theorem counitFreeAlg3_respects_rel :
    ∀ a b, ChevalleyRelSl3 k a b → counitFreeAlg3 k a = counitFreeAlg3 k b := by
  intro a b hab
  induction hab <;> simp [counitFreeAlg3, FreeAlgebra.lift_ι_apply, counitOnGen3] <;> ring

/-- The counit on U_q(sl₃). -/
noncomputable def uq3Counit :
    Uqsl3 k →ₐ[LaurentPolynomial k] LaurentPolynomial k :=
  RingQuot.liftAlgHom (LaurentPolynomial k) ⟨counitFreeAlg3 k, counitFreeAlg3_respects_rel k⟩

/-! ## 3. Antipode S -/

/-- Antipode on generators (anti-homomorphism):
  S(K_i) = K_i⁻¹, S(K_i⁻¹) = K_i
  S(E_i) = −E_i K_i⁻¹, S(F_i) = −K_i F_i -/
private def antipodeOnGen3 : Uqsl3Gen → Uqsl3 k
  | .E1    => -(uq3E1 k * uq3K1inv k)
  | .E2    => -(uq3E2 k * uq3K2inv k)
  | .F1    => -(uq3K1 k * uq3F1 k)
  | .F2    => -(uq3K2 k * uq3F2 k)
  | .K1    => uq3K1inv k
  | .K1inv => uq3K1 k
  | .K2    => uq3K2inv k
  | .K2inv => uq3K2 k

/-- Antipode lifted to the free algebra.
    Note: S is an algebra ANTI-homomorphism, so it reverses multiplication.
    We define it as an algebra hom from FreeAlgebra to (Uqsl3 k)ᵐᵒᵖ, then
    compose with MulOpposite.unop. -/
private def antipodeFreeAlg3 :
    FreeAlgebra (LaurentPolynomial k) Uqsl3Gen →ₐ[LaurentPolynomial k]
    (Uqsl3 k)ᵐᵒᵖ :=
  FreeAlgebra.lift (LaurentPolynomial k) (fun x => MulOpposite.op (antipodeOnGen3 k x))

private theorem antipodeFreeAlg3_ι (x : Uqsl3Gen) :
    antipodeFreeAlg3 k (FreeAlgebra.ι _ x) = MulOpposite.op (antipodeOnGen3 k x) := by
  unfold antipodeFreeAlg3; exact FreeAlgebra.lift_ι_apply _ _

/-! ### Per-relation antipode helpers (21 Chevalley relations) -/

/- Group I: K-invertibility (4 antipode helpers) -/

private theorem antipodeFreeAlg3_K1K1inv :
    antipodeFreeAlg3 k (gen3 k K1 * gen3 k K1inv) =
    (1 : (Uqsl3 k)ᵐᵒᵖ) := by
  rw [map_mul]
  erw [antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
  simp only [antipodeOnGen3, ← MulOpposite.op_mul, uq3_K1_mul_K1inv, MulOpposite.op_one]

private theorem antipodeFreeAlg3_K1invK1 :
    antipodeFreeAlg3 k (gen3 k K1inv * gen3 k K1) =
    (1 : (Uqsl3 k)ᵐᵒᵖ) := by
  rw [map_mul]
  erw [antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
  simp only [antipodeOnGen3, ← MulOpposite.op_mul, uq3_K1inv_mul_K1, MulOpposite.op_one]

private theorem antipodeFreeAlg3_K2K2inv :
    antipodeFreeAlg3 k (gen3 k K2 * gen3 k K2inv) =
    (1 : (Uqsl3 k)ᵐᵒᵖ) := by
  rw [map_mul]
  erw [antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
  simp only [antipodeOnGen3, ← MulOpposite.op_mul, uq3_K2_mul_K2inv, MulOpposite.op_one]

private theorem antipodeFreeAlg3_K2invK2 :
    antipodeFreeAlg3 k (gen3 k K2inv * gen3 k K2) =
    (1 : (Uqsl3 k)ᵐᵒᵖ) := by
  rw [map_mul]
  erw [antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
  simp only [antipodeOnGen3, ← MulOpposite.op_mul, uq3_K2inv_mul_K2, MulOpposite.op_one]

/- Group II: K-commutativity -/

private theorem antipodeFreeAlg3_K1K2 :
    antipodeFreeAlg3 k (gen3 k K1 * gen3 k K2) =
    antipodeFreeAlg3 k (gen3 k K2 * gen3 k K1) := by
  rw [map_mul, map_mul]
  erw [antipodeFreeAlg3_ι (k := k) K1, antipodeFreeAlg3_ι (k := k) K2]
  simp only [antipodeOnGen3, ← MulOpposite.op_mul]
  congr 1
  exact (uq3_K1inv_K2inv_comm k).symm

/- Group III: K-E conjugation (4 helpers) -/
-- The antipode inverts multiplication via MulOpposite, so
--   S(K_i·E_j) = S(E_j)·S(K_i) [in Uqsl3] = (-E_j·K_j⁻¹)·K_i⁻¹
-- and S(q^a·E_j·K_i) = q^a·S(K_i)·S(E_j) = q^a·K_i⁻¹·(-E_j·K_j⁻¹)
-- These are equal via E_j·K_i⁻¹ and K_i⁻¹ commutation.

private theorem antipodeFreeAlg3_K1E1 :
    antipodeFreeAlg3 k (gen3 k K1 * gen3 k E1) =
    antipodeFreeAlg3 k (scal3' k (T 2) * gen3 k E1 * gen3 k K1) := by
  rw [show antipodeFreeAlg3 k (gen3 k K1 * gen3 k E1) =
        MulOpposite.op (uq3K1inv k) * MulOpposite.op (-(uq3E1 k * uq3K1inv k)) by
      erw [map_mul, antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]; rfl]
  rw [show antipodeFreeAlg3 k (scal3' k (T 2) * gen3 k E1 * gen3 k K1) =
        MulOpposite.op (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) *
          uq3E1 k * uq3K1inv k)) * MulOpposite.op (uq3K1inv k) from ?_]
  · simp +decide [← mul_assoc, ← MulOpposite.op_mul, uq3_E1_mul_K1inv]
    rw [show (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3K1inv k * uq3E1 k =
        uq3K1inv k * ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E1 k) by
      simp +decide [← mul_assoc, ← Algebra.smul_def]]
    simp +decide [mul_assoc, mul_comm, mul_left_comm]
    grind +splitImp
  · simp +decide [scal3', map_mul, AlgHom.commutes]
    erw [antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
    simp +decide [antipodeOnGen3, mul_assoc]
    simp +decide [mul_assoc, mul_left_comm, mul_comm, Algebra.algebraMap_eq_smul_one]
    simp +decide [mul_assoc, mul_left_comm, mul_comm, Algebra.smul_def]
    grind +splitImp

private theorem antipodeFreeAlg3_K1E2 :
    antipodeFreeAlg3 k (gen3 k K1 * gen3 k E2) =
    antipodeFreeAlg3 k (scal3' k (T (-1)) * gen3 k E2 * gen3 k K1) := by
  simp +decide [antipodeOnGen3, antipodeFreeAlg3]
  have h_central : ∀ (x : Uqsl3 k),
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * x =
      x * (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) :=
    fun x => Algebra.commutes _ _
  have this := uq3_E2_mul_K1inv k
  replace this := congr_arg (fun x => x * uq3K2inv k) this
  simp_all +decide [mul_assoc, mul_comm, mul_left_comm]
  simp_all +decide [← mul_assoc, ← MulOpposite.op_mul, ← MulOpposite.op_neg]
  convert congr_arg Neg.neg this using 1 <;> simp +decide [mul_assoc, mul_comm, mul_left_comm]
  · simp +decide [mul_assoc, uq3_K1inv_K2inv_comm]
    grind +qlia
  · grind +locals

private theorem antipodeFreeAlg3_K2E1 :
    antipodeFreeAlg3 k (gen3 k K2 * gen3 k E1) =
    antipodeFreeAlg3 k (scal3' k (T (-1)) * gen3 k E1 * gen3 k K2) := by
  simp +decide [antipodeOnGen3, antipodeFreeAlg3]
  have h_central : ∀ (x : Uqsl3 k),
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * x =
      x * (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) :=
    fun x => Algebra.commutes _ _
  have this := uq3_E1_mul_K2inv k
  replace this := congr_arg (fun x => x * uq3K1inv k) this
  simp_all +decide [mul_assoc, mul_comm, mul_left_comm]
  simp_all +decide [← mul_assoc, ← MulOpposite.op_mul, ← MulOpposite.op_neg]
  convert congr_arg Neg.neg this using 1 <;> simp +decide [mul_assoc, mul_comm, mul_left_comm]
  · simp +decide [mul_assoc, (uq3_K1inv_K2inv_comm k).symm]
    grind +qlia
  · grind +locals

private theorem antipodeFreeAlg3_K2E2 :
    antipodeFreeAlg3 k (gen3 k K2 * gen3 k E2) =
    antipodeFreeAlg3 k (scal3' k (T 2) * gen3 k E2 * gen3 k K2) := by
  rw [show antipodeFreeAlg3 k (gen3 k K2 * gen3 k E2) =
        MulOpposite.op (uq3K2inv k) * MulOpposite.op (-(uq3E2 k * uq3K2inv k)) by
      erw [map_mul, antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]; rfl]
  rw [show antipodeFreeAlg3 k (scal3' k (T 2) * gen3 k E2 * gen3 k K2) =
        MulOpposite.op (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) *
          uq3E2 k * uq3K2inv k)) * MulOpposite.op (uq3K2inv k) from ?_]
  · simp +decide [← mul_assoc, ← MulOpposite.op_mul, uq3_E2_mul_K2inv]
    rw [show (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3K2inv k * uq3E2 k =
        uq3K2inv k * ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E2 k) by
      simp +decide [← mul_assoc, ← Algebra.smul_def]]
    simp +decide [mul_assoc, mul_comm, mul_left_comm]
    grind +splitImp
  · simp +decide [scal3', map_mul, AlgHom.commutes]
    erw [antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
    simp +decide [antipodeOnGen3, mul_assoc]
    simp +decide [mul_assoc, mul_left_comm, mul_comm, Algebra.algebraMap_eq_smul_one]
    simp +decide [mul_assoc, mul_left_comm, mul_comm, Algebra.smul_def]
    grind +splitImp

/- Group IV: K-F conjugation (4 helpers) -/

private theorem antipodeFreeAlg3_K1F1 :
    antipodeFreeAlg3 k (gen3 k K1 * gen3 k F1) =
    antipodeFreeAlg3 k (scal3' k (T (-2)) * gen3 k F1 * gen3 k K1) := by
  have key : -(uq3K1 k * uq3F1 k) * uq3K1inv k =
    -((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k) := by
    letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
    rw [neg_mul, neg_inj, uq3_K1F1]; simp +decide [mul_assoc, uq3_K1_mul_K1inv]
  have hL : antipodeFreeAlg3 k (gen3 k K1 * gen3 k F1) =
    MulOpposite.op (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k)) := by
    erw [map_mul, antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
    exact (MulOpposite.op_mul (-(uq3K1 k * uq3F1 k)) (uq3K1inv k)).symm.trans
      (congr_arg MulOpposite.op key)
  rw [hL]
  symm
  rw [show antipodeFreeAlg3 k (scal3' k (T (-2)) * gen3 k F1 * gen3 k K1) =
        MulOpposite.op (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3K1 k * uq3F1 k)) *
          MulOpposite.op (uq3K1inv k) from ?_]
  · have key2 : uq3K1inv k * (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3K1 k * uq3F1 k)) =
      -((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k) := by
      letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
      rw [mul_neg, neg_inj]
      simp +decide [mul_assoc, ← mul_assoc, uq3_K1inv_mul_K1, uq3_K1_mul_K1inv,
                    Algebra.commutes, mul_comm, mul_left_comm]
    exact (MulOpposite.op_mul (uq3K1inv k) (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) *
      uq3K1 k * uq3F1 k))).symm.trans (congr_arg MulOpposite.op key2)
  · simp +decide [antipodeFreeAlg3, scal3', AlgHom.commutes, map_mul, mul_assoc]
    simp +decide [antipodeOnGen3, mul_assoc, mul_left_comm, mul_comm,
                  Algebra.algebraMap_eq_smul_one]
    simp +decide [mul_assoc, Algebra.smul_def]
    grind

private theorem antipodeFreeAlg3_K1F2 :
    antipodeFreeAlg3 k (gen3 k K1 * gen3 k F2) =
    antipodeFreeAlg3 k (scal3' k (T 1) * gen3 k F2 * gen3 k K1) := by
  simp +decide [mul_assoc, Algebra.algebraMap_eq_smul_one]
  simp +decide [antipodeFreeAlg3_ι, antipodeOnGen3]
  have h_comm : uq3K1inv k * uq3K2 k = uq3K2 k * uq3K1inv k := (uq3_K2_K1inv_comm k).symm
  have hF2_K1inv := uq3_F2_mul_K1inv k
  simp_all +decide [mul_assoc, mul_left_comm, mul_comm]
  simp +decide [← mul_assoc, ← MulOpposite.op_mul, ← MulOpposite.op_neg, ← MulOpposite.op_smul]
  have h_comm2 : uq3K2 k * uq3F2 k * uq3K1inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3K1inv k * (uq3K2 k * uq3F2 k) := by
    simp +decide [mul_assoc, hF2_K1inv]
    simp +decide [← mul_assoc, ← h_comm]
    simp +decide [mul_assoc, mul_left_comm, Algebra.commutes]
    simp +decide [← mul_assoc, ← h_comm]
  convert congr_arg Neg.neg h_comm2 using 1 <;> simp +decide [mul_assoc, mul_comm, mul_left_comm]
  · grind
  · simp +decide [Algebra.smul_def]
    grind

private theorem antipodeFreeAlg3_K2F1 :
    antipodeFreeAlg3 k (gen3 k K2 * gen3 k F1) =
    antipodeFreeAlg3 k (scal3' k (T 1) * gen3 k F1 * gen3 k K2) := by
  simp +decide [mul_assoc, Algebra.algebraMap_eq_smul_one]
  simp +decide [antipodeFreeAlg3_ι, antipodeOnGen3]
  have h_comm : uq3K2inv k * uq3K1 k = uq3K1 k * uq3K2inv k := (uq3_K1_K2inv_comm k).symm
  have hF1_K2inv := uq3_F1_mul_K2inv k
  simp_all +decide [mul_assoc, mul_left_comm, mul_comm]
  simp +decide [← mul_assoc, ← MulOpposite.op_mul, ← MulOpposite.op_neg, ← MulOpposite.op_smul]
  have h_comm2 : uq3K1 k * uq3F1 k * uq3K2inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3K2inv k * (uq3K1 k * uq3F1 k) := by
    simp +decide [mul_assoc, hF1_K2inv]
    simp +decide [← mul_assoc, ← h_comm]
    simp +decide [mul_assoc, mul_left_comm, Algebra.commutes]
    simp +decide [← mul_assoc, ← h_comm]
  convert congr_arg Neg.neg h_comm2 using 1 <;> simp +decide [mul_assoc, mul_comm, mul_left_comm]
  · grind
  · simp +decide [Algebra.smul_def]
    grind

private theorem antipodeFreeAlg3_K2F2 :
    antipodeFreeAlg3 k (gen3 k K2 * gen3 k F2) =
    antipodeFreeAlg3 k (scal3' k (T (-2)) * gen3 k F2 * gen3 k K2) := by
  have key : -(uq3K2 k * uq3F2 k) * uq3K2inv k =
    -((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k) := by
    letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
    rw [neg_mul, neg_inj, uq3_K2F2]; simp +decide [mul_assoc, uq3_K2_mul_K2inv]
  have hL : antipodeFreeAlg3 k (gen3 k K2 * gen3 k F2) =
    MulOpposite.op (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k)) := by
    erw [map_mul, antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
    exact (MulOpposite.op_mul (-(uq3K2 k * uq3F2 k)) (uq3K2inv k)).symm.trans
      (congr_arg MulOpposite.op key)
  rw [hL]
  symm
  rw [show antipodeFreeAlg3 k (scal3' k (T (-2)) * gen3 k F2 * gen3 k K2) =
        MulOpposite.op (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3K2 k * uq3F2 k)) *
          MulOpposite.op (uq3K2inv k) from ?_]
  · have key2 : uq3K2inv k * (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3K2 k * uq3F2 k)) =
      -((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k) := by
      letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
      rw [mul_neg, neg_inj]
      simp +decide [mul_assoc, ← mul_assoc, uq3_K2inv_mul_K2, uq3_K2_mul_K2inv,
                    Algebra.commutes, mul_comm, mul_left_comm]
    exact (MulOpposite.op_mul (uq3K2inv k) (-((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) *
      uq3K2 k * uq3F2 k))).symm.trans (congr_arg MulOpposite.op key2)
  · simp +decide [antipodeFreeAlg3, scal3', AlgHom.commutes, map_mul, mul_assoc]
    simp +decide [antipodeOnGen3, mul_assoc, mul_left_comm, mul_comm,
                  Algebra.algebraMap_eq_smul_one]
    simp +decide [mul_assoc, Algebra.smul_def]
    grind

/- Group V: EF commutation (4 helpers) -/

private theorem antipodeFreeAlg3_EF11 :
    antipodeFreeAlg3 k
      (scal3' k (T 1 - T (-1)) * (gen3 k E1 * gen3 k F1 - gen3 k F1 * gen3 k E1)) =
    antipodeFreeAlg3 k (gen3 k K1 - gen3 k K1inv) := by
  simp only [scal3', map_sub, map_mul, AlgHom.commutes, antipodeFreeAlg3_ι]
  simp +decide [antipodeOnGen3]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_neg, MulOpposite.unop_op]
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  simp only [neg_mul, mul_neg, neg_neg]
  -- Goal: (K1·F1·(E1·K1inv) - E1·K1inv·(K1·F1)) * (am(T1) - am(T(-1))) = K1inv - K1
  -- Simplify K1·F1·E1·K1inv = F1·E1 and E1·K1inv·K1·F1 = E1·F1
  have h_KFEKinv : uq3K1 k * uq3F1 k * (uq3E1 k * uq3K1inv k) = uq3F1 k * uq3E1 k := by
    -- Convert to smul form: T(-2)·F1·K1·E1·K1inv = T(-2)·T(2)·F1·E1 = 1·(F1·E1)
    have step : uq3K1 k * uq3F1 k * (uq3E1 k * uq3K1inv k) =
        (T 2 * T (-2) : LaurentPolynomial k) • (uq3F1 k * uq3E1 k) := by
      rw [show uq3K1 k * uq3F1 k * (uq3E1 k * uq3K1inv k) =
          uq3K1 k * uq3F1 k * uq3E1 k * uq3K1inv k from by noncomm_ring,
          uq3_K1F1,
          show (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k * uq3K1 k *
              uq3E1 k * uq3K1inv k =
              (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k *
              (uq3K1 k * uq3E1 k) * uq3K1inv k from by noncomm_ring,
          uq3_K1E1]
      simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [show uq3F1 k * (uq3E1 k * uq3K1 k) * uq3K1inv k =
          uq3F1 k * uq3E1 k * (uq3K1 k * uq3K1inv k) from by noncomm_ring,
          uq3_K1_mul_K1inv, mul_one]
    rw [step,
        show (T 2 * T (-2) : LaurentPolynomial k) = 1 from by
          rw [← T_add]; norm_num [T_zero],
        one_smul]
  have h_EKinvKF : uq3E1 k * uq3K1inv k * (uq3K1 k * uq3F1 k) = uq3E1 k * uq3F1 k := by
    rw [show uq3E1 k * uq3K1inv k * (uq3K1 k * uq3F1 k) =
        uq3E1 k * (uq3K1inv k * uq3K1 k) * uq3F1 k from by noncomm_ring,
        uq3_K1inv_mul_K1, mul_one]
  rw [h_KFEKinv, h_EKinvKF]
  -- Goal: (F1·E1 - E1·F1) * (am(T1) - am(T(-1))) = K1inv - K1
  -- Combine scalars, move to left via Algebra.commutes, factor neg, apply uq3_EF11
  rw [show (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) -
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 - T (-1)) from
    (map_sub _ _ _).symm]
  rw [(Algebra.commutes (T 1 - T (-1)) (uq3F1 k * uq3E1 k - uq3E1 k * uq3F1 k)).symm]
  rw [show uq3F1 k * uq3E1 k - uq3E1 k * uq3F1 k =
      -(uq3E1 k * uq3F1 k - uq3F1 k * uq3E1 k) from by noncomm_ring,
      mul_neg]
  rw [uq3_EF11]
  noncomm_ring

private theorem antipodeFreeAlg3_EF22 :
    antipodeFreeAlg3 k
      (scal3' k (T 1 - T (-1)) * (gen3 k E2 * gen3 k F2 - gen3 k F2 * gen3 k E2)) =
    antipodeFreeAlg3 k (gen3 k K2 - gen3 k K2inv) := by
  simp only [scal3', map_sub, map_mul, AlgHom.commutes, antipodeFreeAlg3_ι]
  simp +decide [antipodeOnGen3]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_mul, MulOpposite.unop_neg, MulOpposite.unop_op]
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  simp only [neg_mul, mul_neg, neg_neg]
  have h_KFEKinv : uq3K2 k * uq3F2 k * (uq3E2 k * uq3K2inv k) = uq3F2 k * uq3E2 k := by
    have step : uq3K2 k * uq3F2 k * (uq3E2 k * uq3K2inv k) =
        (T 2 * T (-2) : LaurentPolynomial k) • (uq3F2 k * uq3E2 k) := by
      rw [show uq3K2 k * uq3F2 k * (uq3E2 k * uq3K2inv k) =
          uq3K2 k * uq3F2 k * uq3E2 k * uq3K2inv k from by noncomm_ring,
          uq3_K2F2,
          show (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k * uq3K2 k *
              uq3E2 k * uq3K2inv k =
              (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k *
              (uq3K2 k * uq3E2 k) * uq3K2inv k from by noncomm_ring,
          uq3_K2E2]
      simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [show uq3F2 k * (uq3E2 k * uq3K2 k) * uq3K2inv k =
          uq3F2 k * uq3E2 k * (uq3K2 k * uq3K2inv k) from by noncomm_ring,
          uq3_K2_mul_K2inv, mul_one]
    rw [step,
        show (T 2 * T (-2) : LaurentPolynomial k) = 1 from by
          rw [← T_add]; norm_num [T_zero],
        one_smul]
  have h_EKinvKF : uq3E2 k * uq3K2inv k * (uq3K2 k * uq3F2 k) = uq3E2 k * uq3F2 k := by
    rw [show uq3E2 k * uq3K2inv k * (uq3K2 k * uq3F2 k) =
        uq3E2 k * (uq3K2inv k * uq3K2 k) * uq3F2 k from by noncomm_ring,
        uq3_K2inv_mul_K2, mul_one]
  rw [h_KFEKinv, h_EKinvKF]
  rw [show (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) -
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1 - T (-1)) from
    (map_sub _ _ _).symm]
  rw [(Algebra.commutes (T 1 - T (-1)) (uq3F2 k * uq3E2 k - uq3E2 k * uq3F2 k)).symm]
  rw [show uq3F2 k * uq3E2 k - uq3E2 k * uq3F2 k =
      -(uq3E2 k * uq3F2 k - uq3F2 k * uq3E2 k) from by noncomm_ring,
      mul_neg]
  rw [uq3_EF22]
  noncomm_ring

private theorem antipodeFreeAlg3_E1F2comm :
    antipodeFreeAlg3 k (gen3 k E1 * gen3 k F2) =
    antipodeFreeAlg3 k (gen3 k F2 * gen3 k E1) := by
  erw [map_mul, map_mul, antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
  simp +decide [antipodeOnGen3]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_neg]
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  simp only [neg_mul, mul_neg, neg_neg]
  -- Goal: K2·F2·(E1·K1inv) = E1·K1inv·(K2·F2)
  -- Reduce both sides to a common normal form using scalars central + commutations.
  -- Strategy: convert all generator products to smul form via Algebra.smul_def, then
  -- use abel/noncomm_ring over the scalar ring.
  have hE1F2 : uq3F2 k * uq3E1 k = uq3E1 k * uq3F2 k := (uq3_E1F2_comm k).symm
  have hK2E1 := uq3_K2E1 k
  have hF2K1inv := uq3_F2_mul_K1inv k
  have hK2K1inv := uq3_K2_K1inv_comm k
  -- Convert both sides to the common form am(T 0) · (E1·K2·K1inv·F2)
  have key : uq3K2 k * uq3F2 k * (uq3E1 k * uq3K1inv k) =
      uq3E1 k * uq3K1inv k * (uq3K2 k * uq3F2 k) := by
    -- LHS = K2·F2·E1·K1inv = K2·E1·F2·K1inv = am(T(-1))·E1·K2·am(T 1)·K1inv·F2
    --     = am(T 0)·E1·K2·K1inv·F2 = E1·K1inv·K2·F2
    rw [show uq3K2 k * uq3F2 k * (uq3E1 k * uq3K1inv k) =
        uq3K2 k * (uq3F2 k * uq3E1 k) * uq3K1inv k from by noncomm_ring,
        hE1F2,
        show uq3K2 k * (uq3E1 k * uq3F2 k) * uq3K1inv k =
            (uq3K2 k * uq3E1 k) * (uq3F2 k * uq3K1inv k) from by noncomm_ring,
        hK2E1, hF2K1inv]
    -- Goal: (am(T(-1)) * E1 * K2) * (am(T 1) * K1inv * F2) = E1 * K1inv * (K2 * F2)
    -- Use Algebra.smul_def to convert am(T c) * x = T c • x and work at scalar level
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, ← T_add]
    -- T(-1 + 1) = T 0 = 1; one_smul cleanup
    norm_num [T_zero]
    -- Goal: E1·K2·(K1inv·F2) = E1·K1inv·(K2·F2)
    rw [show uq3E1 k * uq3K2 k * (uq3K1inv k * uq3F2 k) =
        uq3E1 k * (uq3K2 k * uq3K1inv k) * uq3F2 k from by noncomm_ring,
        hK2K1inv]
    noncomm_ring
  exact key

private theorem antipodeFreeAlg3_E2F1comm :
    antipodeFreeAlg3 k (gen3 k E2 * gen3 k F1) =
    antipodeFreeAlg3 k (gen3 k F1 * gen3 k E2) := by
  erw [map_mul, map_mul, antipodeFreeAlg3_ι, antipodeFreeAlg3_ι]
  simp +decide [antipodeOnGen3]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_neg]
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  simp only [neg_mul, mul_neg, neg_neg]
  -- Goal: K1·F1·(E2·K2inv) = E2·K2inv·(K1·F1)  (symmetric to E1F2comm with 1↔2 swap)
  have hE2F1 : uq3F1 k * uq3E2 k = uq3E2 k * uq3F1 k := (uq3_E2F1_comm k).symm
  have hK1E2 := uq3_K1E2 k
  have hF1K2inv := uq3_F1_mul_K2inv k
  have hK1K2inv := uq3_K1_K2inv_comm k
  have key : uq3K1 k * uq3F1 k * (uq3E2 k * uq3K2inv k) =
      uq3E2 k * uq3K2inv k * (uq3K1 k * uq3F1 k) := by
    rw [show uq3K1 k * uq3F1 k * (uq3E2 k * uq3K2inv k) =
        uq3K1 k * (uq3F1 k * uq3E2 k) * uq3K2inv k from by noncomm_ring,
        hE2F1,
        show uq3K1 k * (uq3E2 k * uq3F1 k) * uq3K2inv k =
            (uq3K1 k * uq3E2 k) * (uq3F1 k * uq3K2inv k) from by noncomm_ring,
        hK1E2, hF1K2inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, ← T_add]
    norm_num [T_zero]
    rw [show uq3E2 k * uq3K1 k * (uq3K2inv k * uq3F1 k) =
        uq3E2 k * (uq3K1 k * uq3K2inv k) * uq3F1 k from by noncomm_ring,
        hK1K2inv]
    noncomm_ring
  exact key

/- Groups VI/VII: q-Serre antipode (4 helpers) -/

private theorem antipodeFreeAlg3_SerreE12 :
    antipodeFreeAlg3 k
      (gen3 k E1 * gen3 k E1 * gen3 k E2 + gen3 k E2 * gen3 k E1 * gen3 k E1) =
    antipodeFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k E1 * gen3 k E2 * gen3 k E1) := by
  -- TODO next session: port `Uqsl2AffineHopf.affAntipodeFreeAlg_SerreE01` (L4946-5078).
  -- Template follows structure:
  --   1. Expand S as AlgHom (simp [map_*, AlgHom.commutes, antipodeFreeAlg3_ι, antipodeOnGen3])
  --   2. sub_eq_zero.mp; MulOpposite.unop_injective
  --   3. simp_rw [uq3_E{i}_mul_K{i}inv] to push K⁻¹ left
  --   4. Neg → (-1)•; smul_mul_assoc chain; (-1)^3 = -1
  --   5. Algebra.smul_def conversions; T_add normalizations
  --   6. 4 K⁻¹·E helpers (hK1invE1, hK2invE2, hK1invE2, hK2invE1) + positional _at variants
  --   7. simp to push K⁻¹ rightward through E's
  --   8. K⁻¹·K⁻¹ commute to canonical order
  --   9. Apply sect3_hSerreE12_smul via `congr_arg φ` where
  --      `φ := (LinearMap.mul _ _).flip (K1inv·K2inv·K1inv)`
  --  10. Convert Algebra.commutes scalar centrality; `convert h_neg using 1; module`
  -- ATTEMPT made session 4: ~110 lines of port but hit `simp` recursion loop at
  -- step 6-7 (maxRecDepth). Backed off; clean baseline preserved.
  -- The proof pattern IS known to work (sl_2 affine cubic works identically);
  -- sl_3 quadratic should be simpler (3 terms vs 4). Investigation: likely simp
  -- set ordering between `hK*invE*` and `smul_mul_assoc` — need to avoid
  -- simp cycling. Use `rw` for precise control instead of simp.
  sorry

private theorem antipodeFreeAlg3_SerreE21 :
    antipodeFreeAlg3 k
      (gen3 k E2 * gen3 k E2 * gen3 k E1 + gen3 k E1 * gen3 k E2 * gen3 k E2) =
    antipodeFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k E2 * gen3 k E1 * gen3 k E2) := by
  sorry

private theorem antipodeFreeAlg3_SerreF12 :
    antipodeFreeAlg3 k
      (gen3 k F1 * gen3 k F1 * gen3 k F2 + gen3 k F2 * gen3 k F1 * gen3 k F1) =
    antipodeFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k F1 * gen3 k F2 * gen3 k F1) := by
  sorry

private theorem antipodeFreeAlg3_SerreF21 :
    antipodeFreeAlg3 k
      (gen3 k F2 * gen3 k F2 * gen3 k F1 + gen3 k F1 * gen3 k F2 * gen3 k F2) =
    antipodeFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k F2 * gen3 k F1 * gen3 k F2) := by
  sorry

private theorem antipodeFreeAlg3_respects_rel :
    ∀ a b, ChevalleyRelSl3 k a b → antipodeFreeAlg3 k a = antipodeFreeAlg3 k b := by
  intro a b hab
  cases hab with
  | K1K1inv => rw [antipodeFreeAlg3_K1K1inv, map_one]
  | K1invK1 => rw [antipodeFreeAlg3_K1invK1, map_one]
  | K2K2inv => rw [antipodeFreeAlg3_K2K2inv, map_one]
  | K2invK2 => rw [antipodeFreeAlg3_K2invK2, map_one]
  | K1K2 => exact antipodeFreeAlg3_K1K2 k
  | K1E1 => exact antipodeFreeAlg3_K1E1 k
  | K1E2 => exact antipodeFreeAlg3_K1E2 k
  | K2E1 => exact antipodeFreeAlg3_K2E1 k
  | K2E2 => exact antipodeFreeAlg3_K2E2 k
  | K1F1 => exact antipodeFreeAlg3_K1F1 k
  | K1F2 => exact antipodeFreeAlg3_K1F2 k
  | K2F1 => exact antipodeFreeAlg3_K2F1 k
  | K2F2 => exact antipodeFreeAlg3_K2F2 k
  | EF11 => exact antipodeFreeAlg3_EF11 k
  | EF22 => exact antipodeFreeAlg3_EF22 k
  | E1F2comm => exact antipodeFreeAlg3_E1F2comm k
  | E2F1comm => exact antipodeFreeAlg3_E2F1comm k
  | SerreE12 => exact antipodeFreeAlg3_SerreE12 k
  | SerreE21 => exact antipodeFreeAlg3_SerreE21 k
  | SerreF12 => exact antipodeFreeAlg3_SerreF12 k
  | SerreF21 => exact antipodeFreeAlg3_SerreF21 k

/-- The antipode on U_q(sl₃), as a map to the opposite ring. -/
noncomputable def uq3AntipodeOp :
    Uqsl3 k →ₐ[LaurentPolynomial k] (Uqsl3 k)ᵐᵒᵖ :=
  RingQuot.liftAlgHom (LaurentPolynomial k) ⟨antipodeFreeAlg3 k, antipodeFreeAlg3_respects_rel k⟩

/-- The antipode as a function (composing with unop). -/
noncomputable def uq3Antipode (x : Uqsl3 k) : Uqsl3 k :=
  MulOpposite.unop (uq3AntipodeOp k x)

/-! ## 4. Squared Antipode

**Theorem (Drinfeld):** For U_q(𝔤) with 𝔤 simple, S² = Ad(K_{2ρ}) where 2ρ is twice the
half-sum of positive roots (= sum of positive roots). This is the Drinfeld
"ribbon-element" formula for the squared antipode.

**Primary sources:**
- Jantzen, "Lectures on Quantum Groups", AMS GSM 6 (1996), §4.9 Theorem 4.10 —
  explicit proof S²(x) = K_{2ρ} · x · K_{2ρ}⁻¹ for U_q(𝔤) on generators.
- Kassel, "Quantum Groups", Springer GTM 155 (1995), Ch. VII.2 (quasi-triangular
  structure), specialised to sl_2 in Ch. VI (Prop. VI.1.4 establishes S² = Ad(K)
  for sl_2 where 2ρ = α and K_α = K).
- Chari-Pressley, "A Guide to Quantum Groups", CUP (1994), §9.2.

**For sl_3 (type A₂):** Positive roots are {α₁, α₂, α₁+α₂}. Their sum:
  2ρ = α₁ + α₂ + (α₁+α₂) = 2α₁ + 2α₂.
In the Drinfeld-Jimbo convention, K_{α_i} = K_i (since sl_3 is simply-laced with d_i = 1),
so K_{2ρ} = K_1^{⟨2ρ,α_1^∨⟩} · K_2^{⟨2ρ,α_2^∨⟩} = K_1² · K_2².

**Verification on E_i (direct computation):**
  S²(E_i) = S(-E_i K_i⁻¹) = -S(K_i⁻¹) · S(E_i) = -K_i · (-E_i K_i⁻¹) = K_i E_i K_i⁻¹
         = q^{A_{ii}} E_i = q² E_i [since A_{ii} = 2].
And Ad(K_1²K_2²)(E_i) = q² E_i (using the Cartan matrix A_{ij}, K_{2ρ} acts on E_i
by q^{⟨2ρ, α_i∨⟩} = q^2 since ⟨2ρ, α_i∨⟩ = 2 for all simple roots in simply-laced sl_n).

**Historical note:** The original codebase statement `S² = Ad(K_1 K_2)` was
mathematically wrong. It would give q·E_i instead of q²·E_i (differing by one factor
of K_1·K_2 vs K_1²·K_2²). Caught during the Lean 4.29 upgrade refactor. -/

/-- Helper: `uq3Antipode k (uqsl3Mk k (gen3 k y)) = antipodeOnGen3 k y`. -/
private theorem uq3Antipode_gen (y : Uqsl3Gen) :
    uq3Antipode k (uqsl3Mk k (gen3 k y)) = antipodeOnGen3 k y := by
  show MulOpposite.unop ((RingQuot.liftAlgHom _ _) (uqsl3Mk k (FreeAlgebra.ι _ y))) = _
  rw [show uqsl3Mk k (FreeAlgebra.ι _ y) =
        RingQuot.mkAlgHom (LaurentPolynomial k) (ChevalleyRelSl3 k) (FreeAlgebra.ι _ y) from rfl,
      RingQuot.liftAlgHom_mkAlgHom_apply]
  erw [antipodeFreeAlg3_ι]
  exact MulOpposite.unop_op _

/-- uq3Antipode is an anti-homomorphism: S(a·b) = S(b)·S(a). -/
private theorem uq3Antipode_mul (a b : Uqsl3 k) :
    uq3Antipode k (a * b) = uq3Antipode k b * uq3Antipode k a := by
  show MulOpposite.unop (uq3AntipodeOp k (a * b)) = _
  rw [map_mul]
  rfl

/-- uq3Antipode preserves negation. -/
private theorem uq3Antipode_neg (a : Uqsl3 k) :
    uq3Antipode k (-a) = -uq3Antipode k a := by
  show MulOpposite.unop ((uq3AntipodeOp k) (-a)) = -MulOpposite.unop ((uq3AntipodeOp k) a)
  letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
  rw [map_neg]
  rfl

/-- S²(E_i) = T(2)·E_i via K-E conjugation. Helper for S² proof. -/
private theorem uq3_S2_on_E1_lhs :
    uq3K1 k * uq3E1 k * uq3K1inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E1 k := by
  have h := uq3_K1E1 k
  calc uq3K1 k * uq3E1 k * uq3K1inv k
      = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E1 k * uq3K1 k *
          uq3K1inv k := by rw [h]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E1 k *
          (uq3K1 k * uq3K1inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E1 k * 1 := by
          rw [uq3_K1_mul_K1inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E1 k := mul_one _

private theorem uq3_S2_on_E2_lhs :
    uq3K2 k * uq3E2 k * uq3K2inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E2 k := by
  have h := uq3_K2E2 k
  calc uq3K2 k * uq3E2 k * uq3K2inv k
      = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E2 k * uq3K2 k *
          uq3K2inv k := by rw [h]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E2 k *
          (uq3K2 k * uq3K2inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E2 k * 1 := by
          rw [uq3_K2_mul_K2inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E2 k := mul_one _

/-- S²(F_1) = K₁·F₁·K₁⁻¹ = T(-2)·F₁. -/
private theorem uq3_S2_on_F1_lhs :
    uq3K1 k * uq3F1 k * uq3K1inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k := by
  have h := uq3_K1F1 k
  calc uq3K1 k * uq3F1 k * uq3K1inv k
      = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k * uq3K1 k *
          uq3K1inv k := by rw [h]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k *
          (uq3K1 k * uq3K1inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k * 1 := by
          rw [uq3_K1_mul_K1inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k := mul_one _

private theorem uq3_S2_on_F2_lhs :
    uq3K2 k * uq3F2 k * uq3K2inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k := by
  have h := uq3_K2F2 k
  calc uq3K2 k * uq3F2 k * uq3K2inv k
      = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k * uq3K2 k *
          uq3K2inv k := by rw [h]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k *
          (uq3K2 k * uq3K2inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k * 1 := by
          rw [uq3_K2_mul_K2inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k := mul_one _

/-! ### Cross-index K-X conjugation helpers

These extend the same-index helpers `uq3_S2_on_{E1,E2,F1,F2}_lhs` by covering
cross-index conjugations. Each states `K_j·X·K_j⁻¹ = am(T(c))·X` for the
appropriate scaling c from the sl₃ Cartan matrix [[2,-1],[-1,2]]. -/

private theorem uq3_K2_conj_E1 :
    uq3K2 k * uq3E1 k * uq3K2inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E1 k := by
  have h := uq3_K2E1 k
  calc uq3K2 k * uq3E1 k * uq3K2inv k
      = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E1 k * uq3K2 k *
          uq3K2inv k := by rw [h]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E1 k *
          (uq3K2 k * uq3K2inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E1 k * 1 := by
          rw [uq3_K2_mul_K2inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E1 k := mul_one _

private theorem uq3_K1_conj_E2 :
    uq3K1 k * uq3E2 k * uq3K1inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E2 k := by
  have h := uq3_K1E2 k
  calc uq3K1 k * uq3E2 k * uq3K1inv k
      = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E2 k * uq3K1 k *
          uq3K1inv k := by rw [h]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E2 k *
          (uq3K1 k * uq3K1inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E2 k * 1 := by
          rw [uq3_K1_mul_K1inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-1)) * uq3E2 k := mul_one _

private theorem uq3_K2_conj_F1 :
    uq3K2 k * uq3F1 k * uq3K2inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F1 k := by
  have h := uq3_K2F1 k
  calc uq3K2 k * uq3F1 k * uq3K2inv k
      = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F1 k * uq3K2 k *
          uq3K2inv k := by rw [h]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F1 k *
          (uq3K2 k * uq3K2inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F1 k * 1 := by
          rw [uq3_K2_mul_K2inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F1 k := mul_one _

private theorem uq3_K1_conj_F2 :
    uq3K1 k * uq3F2 k * uq3K1inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F2 k := by
  have h := uq3_K1F2 k
  calc uq3K1 k * uq3F2 k * uq3K1inv k
      = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F2 k * uq3K1 k *
          uq3K1inv k := by rw [h]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F2 k *
          (uq3K1 k * uq3K1inv k) := by noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F2 k * 1 := by
          rw [uq3_K1_mul_K1inv]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 1) * uq3F2 k := mul_one _

/-! ### Iterated K-X conjugation helpers

These reduce `K₁²K₂² · X · K₂⁻²K₁⁻²` to `am(T(c))·X` for X ∈ {E₁,E₂,F₁,F₂}.
Strategy: `K²·X·Kinv² = K·(K·X·Kinv)·Kinv = K·am(c)·X·Kinv = am(c)·K·X·Kinv = am(c)·am(c)·X`,
then iterate for the outer K pair. The scaling exponent is `2·a_{ji} + 2·a_{ii'}` where
`i' = j` for same-index and `i' ≠ j` for cross-index pairs, summing to the positive-root sum. -/

/-- Double-K conjugation from a single conjugation:
    if `K·X·K⁻¹ = am(c)·X` then `K²·X·K⁻² = am(c)·am(c)·X`. -/
private theorem uq3_double_conj
    (K Kinv X : Uqsl3 k) (c : LaurentPolynomial k)
    (hconj : K * X * Kinv = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * X) :
    K * K * X * Kinv * Kinv =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c *
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * X := by
  have hcomm : K * (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * K :=
    (Algebra.commutes c K).symm
  calc K * K * X * Kinv * Kinv
      = K * (K * X * Kinv) * Kinv := by noncomm_ring
    _ = K * ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * X) * Kinv := by rw [hconj]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * (K * X * Kinv) := by
          rw [show K * ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * X) * Kinv =
              (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * (K * X * Kinv) from by
            rw [show K * ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * X) =
                (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * K * X from by
              rw [← mul_assoc, hcomm]]
            noncomm_ring]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * X) := by rw [hconj]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c *
          (algebraMap (LaurentPolynomial k) (Uqsl3 k)) c * X := by noncomm_ring

/-- K₁²K₂² · E₁ · K₂⁻²K₁⁻² = am(T(2)) · E₁. -/
private theorem uq3_S2_on_E1_rhs :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3E1 k *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E1 k := by
  have h_K2sq : uq3K2 k * uq3K2 k * uq3E1 k * uq3K2inv k * uq3K2inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3E1 k := by
    rw [uq3_double_conj k (uq3K2 k) (uq3K2inv k) (uq3E1 k) (T (-1)) (uq3_K2_conj_E1 k),
        ← map_mul, ← T_add]
    norm_num
  have h_K1sq : uq3K1 k * uq3K1 k * uq3E1 k * uq3K1inv k * uq3K1inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 4) * uq3E1 k := by
    rw [uq3_double_conj k (uq3K1 k) (uq3K1inv k) (uq3E1 k) (T 2) (uq3_S2_on_E1_lhs k),
        ← map_mul, ← T_add]
    norm_num
  calc uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3E1 k *
         uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k
      = uq3K1 k * uq3K1 k *
          (uq3K2 k * uq3K2 k * uq3E1 k * uq3K2inv k * uq3K2inv k) *
          uq3K1inv k * uq3K1inv k := by noncomm_ring
    _ = uq3K1 k * uq3K1 k *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3E1 k) *
          uq3K1inv k * uq3K1inv k := by rw [h_K2sq]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) *
          (uq3K1 k * uq3K1 k * uq3E1 k * uq3K1inv k * uq3K1inv k) := by
          rw [← mul_assoc (uq3K1 k * uq3K1 k), (Algebra.commutes (T (-2)) (uq3K1 k * uq3K1 k)).symm]
          noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 4) * uq3E1 k) := by rw [h_K1sq]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E1 k := by
          rw [← mul_assoc, ← map_mul, ← T_add]; norm_num

/-- K₁²K₂² · E₂ · K₂⁻²K₁⁻² = am(T(2)) · E₂. -/
private theorem uq3_S2_on_E2_rhs :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3E2 k *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E2 k := by
  have h_K2sq : uq3K2 k * uq3K2 k * uq3E2 k * uq3K2inv k * uq3K2inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 4) * uq3E2 k := by
    rw [uq3_double_conj k (uq3K2 k) (uq3K2inv k) (uq3E2 k) (T 2) (uq3_S2_on_E2_lhs k),
        ← map_mul, ← T_add]
    norm_num
  have h_K1sq : uq3K1 k * uq3K1 k * uq3E2 k * uq3K1inv k * uq3K1inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3E2 k := by
    rw [uq3_double_conj k (uq3K1 k) (uq3K1inv k) (uq3E2 k) (T (-1)) (uq3_K1_conj_E2 k),
        ← map_mul, ← T_add]
    norm_num
  calc uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3E2 k *
         uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k
      = uq3K1 k * uq3K1 k *
          (uq3K2 k * uq3K2 k * uq3E2 k * uq3K2inv k * uq3K2inv k) *
          uq3K1inv k * uq3K1inv k := by noncomm_ring
    _ = uq3K1 k * uq3K1 k *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 4) * uq3E2 k) *
          uq3K1inv k * uq3K1inv k := by rw [h_K2sq]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 4) *
          (uq3K1 k * uq3K1 k * uq3E2 k * uq3K1inv k * uq3K1inv k) := by
          rw [← mul_assoc (uq3K1 k * uq3K1 k), (Algebra.commutes (T 4) (uq3K1 k * uq3K1 k)).symm]
          noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 4) *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3E2 k) := by rw [h_K1sq]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3E2 k := by
          rw [← mul_assoc, ← map_mul, ← T_add]; norm_num

/-- K₁²K₂² · F₁ · K₂⁻²K₁⁻² = am(T(-2)) · F₁. -/
private theorem uq3_S2_on_F1_rhs :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3F1 k *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k := by
  have h_K2sq : uq3K2 k * uq3K2 k * uq3F1 k * uq3K2inv k * uq3K2inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3F1 k := by
    rw [uq3_double_conj k (uq3K2 k) (uq3K2inv k) (uq3F1 k) (T 1) (uq3_K2_conj_F1 k),
        ← map_mul, ← T_add]
    norm_num
  have h_K1sq : uq3K1 k * uq3K1 k * uq3F1 k * uq3K1inv k * uq3K1inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-4)) * uq3F1 k := by
    rw [uq3_double_conj k (uq3K1 k) (uq3K1inv k) (uq3F1 k) (T (-2)) (uq3_S2_on_F1_lhs k),
        ← map_mul, ← T_add]
    norm_num
  calc uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3F1 k *
         uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k
      = uq3K1 k * uq3K1 k *
          (uq3K2 k * uq3K2 k * uq3F1 k * uq3K2inv k * uq3K2inv k) *
          uq3K1inv k * uq3K1inv k := by noncomm_ring
    _ = uq3K1 k * uq3K1 k *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3F1 k) *
          uq3K1inv k * uq3K1inv k := by rw [h_K2sq]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) *
          (uq3K1 k * uq3K1 k * uq3F1 k * uq3K1inv k * uq3K1inv k) := by
          rw [← mul_assoc (uq3K1 k * uq3K1 k), (Algebra.commutes (T 2) (uq3K1 k * uq3K1 k)).symm]
          noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-4)) * uq3F1 k) := by rw [h_K1sq]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F1 k := by
          rw [← mul_assoc, ← map_mul, ← T_add]; norm_num

/-- K₁²K₂² · F₂ · K₂⁻²K₁⁻² = am(T(-2)) · F₂. -/
private theorem uq3_S2_on_F2_rhs :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3F2 k *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k := by
  have h_K2sq : uq3K2 k * uq3K2 k * uq3F2 k * uq3K2inv k * uq3K2inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-4)) * uq3F2 k := by
    rw [uq3_double_conj k (uq3K2 k) (uq3K2inv k) (uq3F2 k) (T (-2)) (uq3_S2_on_F2_lhs k),
        ← map_mul, ← T_add]
    norm_num
  have h_K1sq : uq3K1 k * uq3K1 k * uq3F2 k * uq3K1inv k * uq3K1inv k =
      (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3F2 k := by
    rw [uq3_double_conj k (uq3K1 k) (uq3K1inv k) (uq3F2 k) (T 1) (uq3_K1_conj_F2 k),
        ← map_mul, ← T_add]
    norm_num
  calc uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3F2 k *
         uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k
      = uq3K1 k * uq3K1 k *
          (uq3K2 k * uq3K2 k * uq3F2 k * uq3K2inv k * uq3K2inv k) *
          uq3K1inv k * uq3K1inv k := by noncomm_ring
    _ = uq3K1 k * uq3K1 k *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-4)) * uq3F2 k) *
          uq3K1inv k * uq3K1inv k := by rw [h_K2sq]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-4)) *
          (uq3K1 k * uq3K1 k * uq3F2 k * uq3K1inv k * uq3K1inv k) := by
          rw [← mul_assoc (uq3K1 k * uq3K1 k), (Algebra.commutes (T (-4)) (uq3K1 k * uq3K1 k)).symm]
          noncomm_ring
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-4)) *
          ((algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T 2) * uq3F2 k) := by rw [h_K1sq]
    _ = (algebraMap (LaurentPolynomial k) (Uqsl3 k)) (T (-2)) * uq3F2 k := by
          rw [← mul_assoc, ← map_mul, ← T_add]; norm_num


/-- Key cancellation: `K₁²K₂² · K₂⁻²K₁⁻² = 1`. -/
private theorem uq3_Kprod_cancel :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * (uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k) = 1 := by
  have h1 : uq3K2 k * uq3K2 k * (uq3K2inv k * uq3K2inv k) = 1 := by
    calc uq3K2 k * uq3K2 k * (uq3K2inv k * uq3K2inv k)
        = uq3K2 k * (uq3K2 k * uq3K2inv k) * uq3K2inv k := by noncomm_ring
      _ = uq3K2 k * 1 * uq3K2inv k := by rw [uq3_K2_mul_K2inv]
      _ = uq3K2 k * uq3K2inv k := by noncomm_ring
      _ = 1 := uq3_K2_mul_K2inv k
  have h2 : uq3K1 k * uq3K1 k * (uq3K1inv k * uq3K1inv k) = 1 := by
    calc uq3K1 k * uq3K1 k * (uq3K1inv k * uq3K1inv k)
        = uq3K1 k * (uq3K1 k * uq3K1inv k) * uq3K1inv k := by noncomm_ring
      _ = uq3K1 k * 1 * uq3K1inv k := by rw [uq3_K1_mul_K1inv]
      _ = uq3K1 k * uq3K1inv k := by noncomm_ring
      _ = 1 := uq3_K1_mul_K1inv k
  calc uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k *
        (uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k)
      = uq3K1 k * uq3K1 k * (uq3K2 k * uq3K2 k * (uq3K2inv k * uq3K2inv k)) *
          (uq3K1inv k * uq3K1inv k) := by noncomm_ring
    _ = uq3K1 k * uq3K1 k * 1 * (uq3K1inv k * uq3K1inv k) := by rw [h1]
    _ = uq3K1 k * uq3K1 k * (uq3K1inv k * uq3K1inv k) := by noncomm_ring
    _ = 1 := h2

/-- The K-subalgebra {K₁, K₁⁻¹, K₂, K₂⁻¹} is commutative, so any K_i commutes with K₁²K₂².
This is proved by noting K-generators mutually commute. -/
private theorem uq3_K1_comm_K1K2sq :
    uq3K1 k * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) =
    (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * uq3K1 k := by
  have h := uq3_K1K2_comm k
  have h1 : uq3K2 k * uq3K1 k = uq3K1 k * uq3K2 k := h.symm
  calc uq3K1 k * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k)
      = uq3K1 k * uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k := by noncomm_ring
    _ = uq3K1 k * uq3K1 k * (uq3K1 k * uq3K2 k) * uq3K2 k := by noncomm_ring
    _ = uq3K1 k * uq3K1 k * (uq3K2 k * uq3K1 k) * uq3K2 k := by rw [← h1]
    _ = uq3K1 k * uq3K1 k * uq3K2 k * (uq3K1 k * uq3K2 k) := by noncomm_ring
    _ = uq3K1 k * uq3K1 k * uq3K2 k * (uq3K2 k * uq3K1 k) := by rw [← h1]
    _ = (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * uq3K1 k := by noncomm_ring

private theorem uq3_K1inv_comm_K1K2sq :
    uq3K1inv k * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) =
    (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * uq3K1inv k := by
  have h := uq3_K2_K1inv_comm k
  -- K1inv commutes with K2 (derived commutation)
  have hcomm : uq3K2 k * uq3K1inv k = uq3K1inv k * uq3K2 k := h
  -- K1inv commutes with K1 (trivially — any element is commutative with itself's inverse
  -- via the fact that K1·K1inv = 1, and 1 is central). Explicitly:
  have hK1_K1inv : uq3K1 k * uq3K1inv k = uq3K1inv k * uq3K1 k := by
    rw [uq3_K1_mul_K1inv, uq3_K1inv_mul_K1]
  calc uq3K1inv k * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k)
      = uq3K1inv k * uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k := by noncomm_ring
    _ = uq3K1 k * uq3K1inv k * uq3K1 k * uq3K2 k * uq3K2 k := by rw [← hK1_K1inv]
    _ = uq3K1 k * (uq3K1inv k * uq3K1 k) * uq3K2 k * uq3K2 k := by noncomm_ring
    _ = uq3K1 k * (uq3K1 k * uq3K1inv k) * uq3K2 k * uq3K2 k := by rw [hK1_K1inv]
    _ = uq3K1 k * uq3K1 k * (uq3K1inv k * uq3K2 k) * uq3K2 k := by noncomm_ring
    _ = uq3K1 k * uq3K1 k * (uq3K2 k * uq3K1inv k) * uq3K2 k := by rw [← hcomm]
    _ = uq3K1 k * uq3K1 k * uq3K2 k * (uq3K1inv k * uq3K2 k) := by noncomm_ring
    _ = uq3K1 k * uq3K1 k * uq3K2 k * (uq3K2 k * uq3K1inv k) := by rw [← hcomm]
    _ = (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * uq3K1inv k := by noncomm_ring

private theorem uq3_K2_comm_K1K2sq :
    uq3K2 k * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) =
    (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * uq3K2 k := by
  have h := uq3_K1K2_comm k
  have h1 : uq3K2 k * uq3K1 k = uq3K1 k * uq3K2 k := h.symm
  calc uq3K2 k * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k)
      = (uq3K2 k * uq3K1 k) * uq3K1 k * uq3K2 k * uq3K2 k := by noncomm_ring
    _ = (uq3K1 k * uq3K2 k) * uq3K1 k * uq3K2 k * uq3K2 k := by rw [h1]
    _ = uq3K1 k * (uq3K2 k * uq3K1 k) * uq3K2 k * uq3K2 k := by noncomm_ring
    _ = uq3K1 k * (uq3K1 k * uq3K2 k) * uq3K2 k * uq3K2 k := by rw [h1]
    _ = (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * uq3K2 k := by noncomm_ring

private theorem uq3_K2inv_comm_K1K2sq :
    uq3K2inv k * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) =
    (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * uq3K2inv k := by
  have h := uq3_K1_K2inv_comm k
  have hcomm : uq3K2inv k * uq3K1 k = uq3K1 k * uq3K2inv k := h.symm
  have hK2_K2inv : uq3K2 k * uq3K2inv k = uq3K2inv k * uq3K2 k := by
    rw [uq3_K2_mul_K2inv, uq3_K2inv_mul_K2]
  calc uq3K2inv k * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k)
      = (uq3K2inv k * uq3K1 k) * uq3K1 k * uq3K2 k * uq3K2 k := by noncomm_ring
    _ = (uq3K1 k * uq3K2inv k) * uq3K1 k * uq3K2 k * uq3K2 k := by rw [hcomm]
    _ = uq3K1 k * (uq3K2inv k * uq3K1 k) * uq3K2 k * uq3K2 k := by noncomm_ring
    _ = uq3K1 k * (uq3K1 k * uq3K2inv k) * uq3K2 k * uq3K2 k := by rw [hcomm]
    _ = uq3K1 k * uq3K1 k * (uq3K2inv k * uq3K2 k) * uq3K2 k := by noncomm_ring
    _ = uq3K1 k * uq3K1 k * (uq3K2 k * uq3K2inv k) * uq3K2 k := by rw [hK2_K2inv]
    _ = uq3K1 k * uq3K1 k * uq3K2 k * (uq3K2inv k * uq3K2 k) := by noncomm_ring
    _ = uq3K1 k * uq3K1 k * uq3K2 k * (uq3K2 k * uq3K2inv k) := by rw [hK2_K2inv]
    _ = (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * uq3K2inv k := by noncomm_ring

/-- Conjugation: K₁²K₂² · y · K₂⁻²K₁⁻² = y when y commutes with K₁²K₂². -/
private theorem uq3_K_conj_gen (y : Uqsl3 k)
    (hcomm : y * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) =
             (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * y) :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * y *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k = y := by
  calc uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * y *
         uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k
      = (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) * y *
          (uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k) := by noncomm_ring
    _ = y * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k) *
          (uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k) := by rw [← hcomm]
    _ = y * (uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k *
          (uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k)) := by noncomm_ring
    _ = y * 1 := by rw [uq3_Kprod_cancel]
    _ = y := mul_one _

private theorem uq3_K_conj_K1 :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3K1 k *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k = uq3K1 k :=
  uq3_K_conj_gen k (uq3K1 k) (uq3_K1_comm_K1K2sq k)

private theorem uq3_K_conj_K1inv :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3K1inv k *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k = uq3K1inv k :=
  uq3_K_conj_gen k (uq3K1inv k) (uq3_K1inv_comm_K1K2sq k)

private theorem uq3_K_conj_K2 :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3K2 k *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k = uq3K2 k :=
  uq3_K_conj_gen k (uq3K2 k) (uq3_K2_comm_K1K2sq k)

private theorem uq3_K_conj_K2inv :
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uq3K2inv k *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k = uq3K2inv k :=
  uq3_K_conj_gen k (uq3K2inv k) (uq3_K2inv_comm_K1K2sq k)

theorem uq3_antipode_squared :
    ∀ x : Uqsl3Gen,
    let sx := uq3Antipode k (uqsl3Mk k (gen3 k x))
    uq3Antipode k sx =
    uq3K1 k * uq3K1 k * uq3K2 k * uq3K2 k * uqsl3Mk k (gen3 k x) *
      uq3K2inv k * uq3K2inv k * uq3K1inv k * uq3K1inv k := by
  intro x
  simp only [uq3Antipode_gen]
  cases x
  · -- E1: S²(E1) = K₁·E₁·K₁⁻¹ = am(T 2)·E₁ = K₁²K₂²·E₁·K₂⁻²K₁⁻²
    simp only [antipodeOnGen3]
    rw [uq3Antipode_neg, uq3Antipode_mul,
        show uq3K1inv k = uqsl3Mk k (gen3 k Uqsl3Gen.K1inv) from rfl,
        show uq3E1 k = uqsl3Mk k (gen3 k Uqsl3Gen.E1) from rfl,
        uq3Antipode_gen, uq3Antipode_gen]
    simp only [antipodeOnGen3]
    rw [show (uqsl3Mk k) (gen3 k Uqsl3Gen.E1) = uq3E1 k from rfl,
        show (uqsl3Mk k) (gen3 k Uqsl3Gen.K1inv) = uq3K1inv k from rfl]
    letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
    rw [mul_neg, neg_neg, ← mul_assoc, uq3_S2_on_E1_lhs, ← uq3_S2_on_E1_rhs]
  · -- E2: S²(E2) = K₂·E₂·K₂⁻¹ = am(T 2)·E₂ = K₁²K₂²·E₂·K₂⁻²K₁⁻²
    simp only [antipodeOnGen3]
    rw [uq3Antipode_neg, uq3Antipode_mul,
        show uq3K2inv k = uqsl3Mk k (gen3 k Uqsl3Gen.K2inv) from rfl,
        show uq3E2 k = uqsl3Mk k (gen3 k Uqsl3Gen.E2) from rfl,
        uq3Antipode_gen, uq3Antipode_gen]
    simp only [antipodeOnGen3]
    rw [show (uqsl3Mk k) (gen3 k Uqsl3Gen.E2) = uq3E2 k from rfl,
        show (uqsl3Mk k) (gen3 k Uqsl3Gen.K2inv) = uq3K2inv k from rfl]
    letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
    rw [mul_neg, neg_neg, ← mul_assoc, uq3_S2_on_E2_lhs, ← uq3_S2_on_E2_rhs]
  · -- F1: S²(F1) = K₁·F₁·K₁⁻¹ = am(T(-2))·F₁ = K₁²K₂²·F₁·K₂⁻²K₁⁻²
    simp only [antipodeOnGen3]
    rw [uq3Antipode_neg, uq3Antipode_mul,
        show uq3K1 k = uqsl3Mk k (gen3 k Uqsl3Gen.K1) from rfl,
        show uq3F1 k = uqsl3Mk k (gen3 k Uqsl3Gen.F1) from rfl,
        uq3Antipode_gen, uq3Antipode_gen]
    simp only [antipodeOnGen3]
    rw [show (uqsl3Mk k) (gen3 k Uqsl3Gen.F1) = uq3F1 k from rfl,
        show (uqsl3Mk k) (gen3 k Uqsl3Gen.K1) = uq3K1 k from rfl]
    letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
    rw [neg_mul, neg_neg, uq3_S2_on_F1_lhs, ← uq3_S2_on_F1_rhs]
  · -- F2: S²(F2) = K₂·F₂·K₂⁻¹ = am(T(-2))·F₂ = K₁²K₂²·F₂·K₂⁻²K₁⁻²
    simp only [antipodeOnGen3]
    rw [uq3Antipode_neg, uq3Antipode_mul,
        show uq3K2 k = uqsl3Mk k (gen3 k Uqsl3Gen.K2) from rfl,
        show uq3F2 k = uqsl3Mk k (gen3 k Uqsl3Gen.F2) from rfl,
        uq3Antipode_gen, uq3Antipode_gen]
    simp only [antipodeOnGen3]
    rw [show (uqsl3Mk k) (gen3 k Uqsl3Gen.F2) = uq3F2 k from rfl,
        show (uqsl3Mk k) (gen3 k Uqsl3Gen.K2) = uq3K2 k from rfl]
    letI : NonUnitalNonAssocRing (Uqsl3 k) := inferInstance
    rw [neg_mul, neg_neg, uq3_S2_on_F2_lhs, ← uq3_S2_on_F2_rhs]
  · -- K1: S²(K1) = S(K1⁻¹) = K1; Ad(K²ρ)(K1) = K1 via K-commutativity + inv
    simp only [antipodeOnGen3]
    rw [show uq3K1inv k = uqsl3Mk k (gen3 k Uqsl3Gen.K1inv) from rfl,
        uq3Antipode_gen, show uqsl3Mk k (gen3 k Uqsl3Gen.K1) = uq3K1 k from rfl]
    simp only [antipodeOnGen3]
    exact (uq3_K_conj_K1 k).symm
  · -- K1inv: S²(K1⁻¹) = S(K1) = K1⁻¹
    simp only [antipodeOnGen3]
    rw [show uq3K1 k = uqsl3Mk k (gen3 k Uqsl3Gen.K1) from rfl,
        uq3Antipode_gen, show uqsl3Mk k (gen3 k Uqsl3Gen.K1inv) = uq3K1inv k from rfl]
    simp only [antipodeOnGen3]
    exact (uq3_K_conj_K1inv k).symm
  · -- K2: S²(K2) = S(K2⁻¹) = K2
    simp only [antipodeOnGen3]
    rw [show uq3K2inv k = uqsl3Mk k (gen3 k Uqsl3Gen.K2inv) from rfl,
        uq3Antipode_gen, show uqsl3Mk k (gen3 k Uqsl3Gen.K2) = uq3K2 k from rfl]
    simp only [antipodeOnGen3]
    exact (uq3_K_conj_K2 k).symm
  · -- K2inv: S²(K2⁻¹) = S(K2) = K2⁻¹
    simp only [antipodeOnGen3]
    rw [show uq3K2 k = uqsl3Mk k (gen3 k Uqsl3Gen.K2) from rfl,
        uq3Antipode_gen, show uqsl3Mk k (gen3 k Uqsl3Gen.K2inv) = uq3K2inv k from rfl]
    simp only [antipodeOnGen3]
    exact (uq3_K_conj_K2inv k).symm

/-! ## 5. Module Summary -/

/--
Uqsl3Hopf module: Hopf algebra structure on U_q(sl₃).
  - Coproduct Δ defined via FreeAlgebra.lift + RingQuot.liftAlgHom (3 sorry: relation-respect)
  - Counit ε defined and descended (sorry: relation-respect)
  - Antipode S defined as anti-homomorphism via MulOpposite (sorry: relation-respect)
  - S² = Ad(K₁K₂) (sorry)
  - Bialgebra/HopfAlgebra typeclass wiring deferred until relation-respect proofs filled
-/
theorem uqsl3_hopf_summary : True := trivial

end SKEFTHawking
