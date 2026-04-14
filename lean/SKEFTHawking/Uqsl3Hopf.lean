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

private theorem comulFreeAlg3_SerreE12 :
    comulFreeAlg3 k
      (gen3 k E1 * gen3 k E1 * gen3 k E2 + gen3 k E2 * gen3 k E1 * gen3 k E1) =
    comulFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k E1 * gen3 k E2 * gen3 k E1) := by
  sorry

private theorem comulFreeAlg3_SerreE21 :
    comulFreeAlg3 k
      (gen3 k E2 * gen3 k E2 * gen3 k E1 + gen3 k E1 * gen3 k E2 * gen3 k E2) =
    comulFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k E2 * gen3 k E1 * gen3 k E2) := by
  sorry

private theorem comulFreeAlg3_SerreF12 :
    comulFreeAlg3 k
      (gen3 k F1 * gen3 k F1 * gen3 k F2 + gen3 k F2 * gen3 k F1 * gen3 k F1) =
    comulFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k F1 * gen3 k F2 * gen3 k F1) := by
  sorry

private theorem comulFreeAlg3_SerreF21 :
    comulFreeAlg3 k
      (gen3 k F2 * gen3 k F2 * gen3 k F1 + gen3 k F1 * gen3 k F2 * gen3 k F2) =
    comulFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k F2 * gen3 k F1 * gen3 k F2) := by
  sorry

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
  sorry

private theorem antipodeFreeAlg3_EF22 :
    antipodeFreeAlg3 k
      (scal3' k (T 1 - T (-1)) * (gen3 k E2 * gen3 k F2 - gen3 k F2 * gen3 k E2)) =
    antipodeFreeAlg3 k (gen3 k K2 - gen3 k K2inv) := by
  sorry

private theorem antipodeFreeAlg3_E1F2comm :
    antipodeFreeAlg3 k (gen3 k E1 * gen3 k F2) =
    antipodeFreeAlg3 k (gen3 k F2 * gen3 k E1) := by
  sorry

private theorem antipodeFreeAlg3_E2F1comm :
    antipodeFreeAlg3 k (gen3 k E2 * gen3 k F1) =
    antipodeFreeAlg3 k (gen3 k F1 * gen3 k E2) := by
  sorry

/- Groups VI/VII: q-Serre antipode (4 helpers) -/

private theorem antipodeFreeAlg3_SerreE12 :
    antipodeFreeAlg3 k
      (gen3 k E1 * gen3 k E1 * gen3 k E2 + gen3 k E2 * gen3 k E1 * gen3 k E1) =
    antipodeFreeAlg3 k
      (scal3' k (T 1 + T (-1)) * gen3 k E1 * gen3 k E2 * gen3 k E1) := by
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
  · simp only [antipodeOnGen3]
    sorry
  · simp only [antipodeOnGen3]
    sorry
  · simp only [antipodeOnGen3]
    sorry
  · simp only [antipodeOnGen3]
    sorry
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
