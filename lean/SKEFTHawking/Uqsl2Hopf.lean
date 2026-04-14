/-
Phase 5c Wave 1: U_q(sl_2) Hopf Algebra Structure

Wires the coproduct Delta, counit epsilon, and antipode S into Mathlib's
HopfAlgebra typeclass for U_q(sl_2) = RingQuot (ChevalleyRel k).

Key results:
  - Delta(E) = E tensor K + 1 tensor E, Delta(F) = F tensor 1 + Kinv tensor F, Delta(K) = K tensor K
  - epsilon(E) = epsilon(F) = 0, epsilon(K) = 1
  - S(E) = -E*Kinv, S(F) = -K*F, S(K) = Kinv
  - Bialgebra and HopfAlgebra instances on Uqsl2 k
  - S^2 = Ad(K) (squared antipode is conjugation by K)

References:
  Kassel, "Quantum Groups" (Springer, 1995), Ch. VI
  Lit-Search/Phase-5b/Mathlib4 infrastructure audit for U_q(sl_2)...
  Lit-Search/Phase-5b/From quantum groups to gauge emergence...
-/

import Mathlib
import SKEFTHawking.Uqsl2

open LaurentPolynomial TensorProduct

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k]

-- Redefined locally since the originals in Uqsl2 are private
private abbrev scal' (r : LaurentPolynomial k) :
    FreeAlgebra (LaurentPolynomial k) Uqsl2Gen :=
  algebraMap (LaurentPolynomial k) (FreeAlgebra (LaurentPolynomial k) Uqsl2Gen) r

private abbrev gen (x : Uqsl2Gen) : FreeAlgebra (LaurentPolynomial k) Uqsl2Gen :=
  FreeAlgebra.ι (LaurentPolynomial k) x

-- Fix typeclass diamond: tensor product of Rings should be a Ring
-- (Mathlib only provides Semiring by default for tensor products)
noncomputable instance uqTensorRing : Ring ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) :=
  @Algebra.TensorProduct.instRing (LaurentPolynomial k) (Uqsl2 k) (Uqsl2 k) _ _ _ _ _

-- Derived commutation: K*F*Kinv = q^{-2}*F
private theorem uq_KF_Kinv :
    uqK k * uqF k * uqKinv k = algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2)) * uqF k := by
  have h : uqK k * uqF k * uqKinv k = (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2))) * uqF k * uqK k * uqKinv k := by
    rw [← uq_KF]
  rw [h, mul_assoc, uq_K_mul_Kinv, mul_one]

-- q^2 * q^{-2} = 1
private theorem uq_T2_Tneg2 :
    algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2) *
    algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2)) = 1 := by
  rw [← map_mul, ← LaurentPolynomial.T_add]; norm_num

-- uq_KFEK_sub moved below uq_E_mul_Kinv (line ~150) due to forward dependency

/-! ## 1. Coproduct: Delta : U_q(sl_2) to U_q(sl_2) tensor U_q(sl_2)

Strategy: define on generators via FreeAlgebra.lift, prove compatibility
with ChevalleyRel, descend via RingQuot.liftAlgHom.
-/

/-- Coproduct on generators:
  Delta(E)=E tensor K + 1 tensor E,
  Delta(F)=F tensor 1 + Kinv tensor F,
  Delta(K)=K tensor K,
  Delta(Kinv)=Kinv tensor Kinv. -/
private def comulOnGen : Uqsl2Gen -> (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)
  | .E    => uqE k ⊗ₜ uqK k + 1 ⊗ₜ uqE k
  | .F    => uqF k ⊗ₜ 1 + uqKinv k ⊗ₜ uqF k
  | .K    => uqK k ⊗ₜ uqK k
  | .Kinv => uqKinv k ⊗ₜ uqKinv k

/-- Coproduct lifted to the free algebra. -/
private def comulFreeAlg :
    FreeAlgebra (LaurentPolynomial k) Uqsl2Gen →ₐ[LaurentPolynomial k]
    (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k) :=
  FreeAlgebra.lift (LaurentPolynomial k) (comulOnGen k)

/--
The coproduct respects the Chevalley relations.

PROVIDED SOLUTION
For each ChevalleyRel case, unfold the definitions and verify the algebraic
identity in the tensor product algebra. Key tools:
- KK_inv = 1 and K_inv*K = 1 (from uq_K_mul_Kinv and uq_Kinv_mul_K)
- Tensor product multiplication: (a tensor b)(c tensor d) = ac tensor bd
- The KE relation KE = q^2*EK gives
  Delta(KE) = (K tensor K)(E tensor K + 1 tensor E) = KE tensor K^2 + K tensor KE
  Delta(q^2*EK) = q^2*(E tensor K + 1 tensor E)(K tensor K) = q^2*EK tensor K^2 + q^2*K tensor EK
  These are equal by the KE relation applied in each tensor factor.
-/
-- Helper: comulFreeAlg on a generator
private theorem comulFreeAlg_ι (x : Uqsl2Gen) :
    comulFreeAlg k (FreeAlgebra.ι (LaurentPolynomial k) x) = comulOnGen k x := by
  unfold comulFreeAlg; exact FreeAlgebra.lift_ι_apply _ _

private theorem comulFreeAlg_KKinv :
    comulFreeAlg k (gen k Uqsl2Gen.K * gen k Uqsl2Gen.Kinv) = (1 : (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) := by
  simp only [map_mul, comulFreeAlg_ι]
  simp only [comulOnGen, Algebra.TensorProduct.tmul_mul_tmul]
  rw [uq_K_mul_Kinv]
  simp [Algebra.TensorProduct.one_def]

private theorem comulFreeAlg_KinvK :
    comulFreeAlg k (gen k Uqsl2Gen.Kinv * gen k Uqsl2Gen.K) = (1 : (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) := by
  simp only [map_mul, comulFreeAlg_ι]
  simp only [comulOnGen, Algebra.TensorProduct.tmul_mul_tmul]
  rw [uq_Kinv_mul_K]
  simp [Algebra.TensorProduct.one_def]

private theorem comulFreeAlg_KE :
    comulFreeAlg k (gen k Uqsl2Gen.K * gen k Uqsl2Gen.E) =
    comulFreeAlg k (scal' k (T 2) * gen k Uqsl2Gen.E * gen k Uqsl2Gen.K) := by
  simp +decide [ comulFreeAlg, gen ];
  simp +decide [ comulOnGen, mul_add ];
  rw [ uq_KE ];
  simp +decide [ mul_assoc, add_mul, mul_add, Algebra.smul_def ];
  simp +decide [ Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul' ]

private theorem comulFreeAlg_KF :
    comulFreeAlg k (gen k Uqsl2Gen.K * gen k Uqsl2Gen.F) =
    comulFreeAlg k (scal' k (T (-2)) * gen k Uqsl2Gen.F * gen k Uqsl2Gen.K) := by
  unfold comulFreeAlg;
  simp +decide [ comulOnGen, gen, scal' ];
  -- Apply the relation uq_KF to rewrite the left-hand side.
  have h_rewrite : uqK k * uqF k = (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2))) * uqF k * uqK k := by
    exact?;
  simp +decide [ mul_add, add_mul, mul_assoc, mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul ];
  simp +decide [ mul_assoc, h_rewrite, uq_K_mul_Kinv, uq_Kinv_mul_K ];
  simp +decide [ Algebra.algebraMap_eq_smul_one ];
  rw [ TensorProduct.smul_tmul' ]

/-
Derived relation: E*Kinv = q²*Kinv*E
-/
private theorem uq_E_mul_Kinv :
    uqE k * uqKinv k = algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2) * uqKinv k * uqE k := by
  convert congr_arg ( fun x => uqKinv k * x * uqKinv k ) ( uq_KE k ) using 1 <;> simp +decide [ mul_assoc, uq_K_mul_Kinv, uq_Kinv_mul_K ];
  · simp +decide [ ← mul_assoc, uq_Kinv_mul_K ];
  · simp +decide [ mul_assoc, mul_left_comm, Algebra.commutes ]

/-
K*F*E*Kinv - E*Kinv*K*F = F*E - E*F (used by antipodeFreeAlg_Serre)
-/
private theorem uq_KFEK_sub :
    uqK k * uqF k * (uqE k * uqKinv k) - uqE k * uqKinv k * (uqK k * uqF k) =
    uqF k * uqE k - uqE k * uqF k := by
  have h1 : uqK k * uqF k * (uqE k * uqKinv k) = uqF k * uqE k := by
    have h1 : uqK k * uqF k * uqE k * uqKinv k = (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2)) * (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2))) * uqF k * uqE k := by
      have h1 : uqK k * uqF k * uqE k = (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2))) * uqF k * uqK k * uqE k := by
        rw [ ← uq_KF ] ;
      have h2 : uqK k * uqE k = (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2)) * uqE k * uqK k := by
        grind +suggestions;
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      rw [ show uqK k * uqKinv k = 1 from uq_K_mul_Kinv k ] ; ring;
      nontriviality;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, Algebra.algebraMap_eq_smul_one ];
      rw [ SMulCommClass.smul_comm ];
    rw [ ← mul_assoc, h1, uq_T2_Tneg2, one_mul ];
  simp_all +decide [ mul_assoc ];
  simp_all +decide [ ← mul_assoc, uq_Kinv_mul_K ]

/-
Derived relation: F*K = q⁻²*K*F ... wait no, KF = q⁻²FK means F*K = algebraMap(T 2)*K*F
Actually from KF = q⁻²FK: uqK*uqF = algebraMap(T(-2))*uqF*uqK
So uqF*uqK = algebraMap(T 2)*uqK*uqF
-/
private theorem uq_F_mul_K :
    uqF k * uqK k = algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2) * uqK k * uqF k := by
  have := @uq_KF k;
  convert congr_arg ( fun x => ( algebraMap ( LaurentPolynomial k ) ( Uqsl2 k ) ) ( T 2 ) * x ) this using 1;
  · rw [ this ];
    simp +decide [ mul_assoc, ← map_mul ];
    rw [ ← mul_assoc, ← map_mul ];
    rw [ show T 2 * T ( -2 ) = 1 by rw [ ← LaurentPolynomial.T_add ] ; norm_num ] ; simp +decide;
  · rw [ ← this, mul_assoc ]

/-
Derived: Kinv*F = algebraMap(T 2)*F*Kinv
-/
private theorem uq_Kinv_mul_F :
    uqKinv k * uqF k = algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2) * uqF k * uqKinv k := by
  have h1 : uqF k * uqKinv k = algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2)) * uqKinv k * uqF k := by
    convert congr_arg ( fun x => uqKinv k * x * uqKinv k ) ( uq_KF k ) using 1 <;> simp +decide [ mul_assoc, uq_K_mul_Kinv, uq_Kinv_mul_K ];
    · simp +decide [ ← mul_assoc, uq_K_mul_Kinv, uq_Kinv_mul_K ];
    · simp +decide [ ← mul_assoc, ← Algebra.smul_def ];
  have h2 : algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2) * algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2)) = 1 := by
    rw [ ← map_mul, ← LaurentPolynomial.T_add ] ; norm_num;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  rw [ ← mul_assoc, h2, one_mul ]

/-
The cross terms in the Serre coproduct are equal
-/
private theorem comulFreeAlg_Serre_cross_terms :
    (uqE k * uqKinv k) ⊗ₜ[LaurentPolynomial k] (uqK k * uqF k) =
    (uqKinv k * uqE k) ⊗ₜ[LaurentPolynomial k] (uqF k * uqK k) := by
  have h_cross : (uqKinv k * uqE k) ⊗ₜ[k[T;T⁻¹]] (uqF k * uqK k) = (uqKinv k * uqE k) ⊗ₜ[k[T;T⁻¹]] (algebraMap (LaurentPolynomial k) _ (T 2) * uqK k * uqF k) := by
    rw [ uq_F_mul_K ];
  rw [ uq_E_mul_Kinv ];
  rw [ h_cross ];
  simp +decide [ Algebra.algebraMap_eq_smul_one, mul_assoc, TensorProduct.smul_tmul, TensorProduct.tmul_smul ]

-- Helper: for AlgHom from Ring to Semiring, decompose subtraction
private theorem comulFreeAlg_sub (a b : FreeAlgebra (LaurentPolynomial k) Uqsl2Gen) :
    comulFreeAlg k (a - b) = comulFreeAlg k a +
    algebraMap (LaurentPolynomial k) _ (-1) * comulFreeAlg k b := by
  rw [sub_eq_add_neg, map_add]
  congr 1
  rw [← neg_one_smul (LaurentPolynomial k) b, Algebra.smul_def, map_mul, AlgHom.commutes]

-- Helper: algebraMap(-1) * x + x = 0 in a semiring with algebra structure
private theorem algMap_neg_one_mul_add_self (x : (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) :
    algebraMap (LaurentPolynomial k) _ (-1) * x + x = 0 := by
  have h : (algebraMap (LaurentPolynomial k) ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) (-1) + 1) * x = 0 := by
    have : algebraMap (LaurentPolynomial k) ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) (-1) + 1 = 0 := by
      conv_lhs => rw [show (1 : (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) =
        algebraMap (LaurentPolynomial k) _ 1 from (map_one _).symm]
      rw [← map_add]
      simp
    rw [this, zero_mul]
  rwa [add_mul, one_mul] at h

/-
Helper: algebraMap(-1) * (a ⊗ₜ b) = (-a) ⊗ₜ b
-/
private theorem algMap_neg_one_tmul (a b : Uqsl2 k) :
    algebraMap (LaurentPolynomial k) ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) (-1) *
    (a ⊗ₜ[LaurentPolynomial k] b) = (-a) ⊗ₜ[LaurentPolynomial k] b := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [← neg_one_smul (LaurentPolynomial k) a, TensorProduct.smul_tmul']

-- Helper: algebraMap(-1) * (a ⊗ₜ b) = a ⊗ₜ (-b)
private theorem algMap_neg_one_tmul_right (a b : Uqsl2 k) :
    algebraMap (LaurentPolynomial k) ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) (-1) *
    (a ⊗ₜ[LaurentPolynomial k] b) = a ⊗ₜ[LaurentPolynomial k] (-b) := by
  rw [algMap_neg_one_tmul]
  rw [show (-a) ⊗ₜ[LaurentPolynomial k] b = a ⊗ₜ[LaurentPolynomial k] (-b) from by
    rw [← neg_one_smul (LaurentPolynomial k) a, ← neg_one_smul (LaurentPolynomial k) b]
    rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]]

-- Helper: algebraMap(r) * (a ⊗ₜ b) = (algebraMap(r)*a) ⊗ₜ b
private theorem algMap_mul_tmul (r : LaurentPolynomial k) (a b : Uqsl2 k) :
    algebraMap (LaurentPolynomial k) ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) r *
    (a ⊗ₜ[LaurentPolynomial k] b) = (algebraMap (LaurentPolynomial k) (Uqsl2 k) r * a) ⊗ₜ[LaurentPolynomial k] b := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, TensorProduct.smul_tmul']
  simp [Algebra.smul_def]

-- Helper: algebraMap(r) * (a ⊗ₜ b) = a ⊗ₜ (algebraMap(r)*b)
private theorem algMap_mul_tmul_right (r : LaurentPolynomial k) (a b : Uqsl2 k) :
    algebraMap (LaurentPolynomial k) ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) r *
    (a ⊗ₜ[LaurentPolynomial k] b) = a ⊗ₜ[LaurentPolynomial k] (algebraMap (LaurentPolynomial k) (Uqsl2 k) r * b) := by
  rw [algMap_mul_tmul]
  rw [← Algebra.smul_def, ← Algebra.smul_def]
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]

/-
Step 1: Expand EF - FE in the tensor product.
-/
private theorem comulFreeAlg_EF_sub_FE :
    comulFreeAlg k (gen k Uqsl2Gen.E * gen k Uqsl2Gen.F) -
    comulFreeAlg k (gen k Uqsl2Gen.F * gen k Uqsl2Gen.E) =
    (uqE k * uqF k - uqF k * uqE k) ⊗ₜ[LaurentPolynomial k] uqK k +
    uqKinv k ⊗ₜ[LaurentPolynomial k] (uqE k * uqF k - uqF k * uqE k) := by
  rw [ sub_eq_iff_eq_add ];
  simp +decide [ comulFreeAlg_ι, comulOnGen ];
  simp +decide [ add_mul, mul_add, mul_assoc, add_assoc, sub_eq_add_neg ];
  rw [ show ( uqE k * uqKinv k ) ⊗ₜ[k[T;T⁻¹]] ( uqK k * uqF k ) = ( uqKinv k * uqE k ) ⊗ₜ[k[T;T⁻¹]] ( uqF k * uqK k ) from ?_ ] ; abel_nf;
  · simp +decide [ add_comm, add_left_comm, add_assoc, TensorProduct.add_tmul, TensorProduct.tmul_add ];
    simp +decide [ ← add_assoc, ← TensorProduct.tmul_add, ← TensorProduct.add_tmul ];
  · convert comulFreeAlg_Serre_cross_terms k using 1

/-
Step 2: Distribute algebraMap(T1-T(-1)) and apply uq_serre.
-/
private theorem comulFreeAlg_Serre_apply_serre :
    algebraMap (LaurentPolynomial k)
      ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) (T 1 - T (-1)) *
    ((uqE k * uqF k - uqF k * uqE k) ⊗ₜ[LaurentPolynomial k] uqK k +
     uqKinv k ⊗ₜ[LaurentPolynomial k] (uqE k * uqF k - uqF k * uqE k)) =
    uqK k ⊗ₜ[LaurentPolynomial k] uqK k -
    uqKinv k ⊗ₜ[LaurentPolynomial k] uqKinv k := by
  have h_dist : algebraMap (LaurentPolynomial k) ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) (T 1 - T (-1)) * ((uqE k * uqF k - uqF k * uqE k) ⊗ₜ[LaurentPolynomial k] uqK k) = (uqK k - uqKinv k) ⊗ₜ[LaurentPolynomial k] uqK k := by
    rw [ ← uq_serre ];
    exact?;
  have h_dist2 : algebraMap (LaurentPolynomial k) ((Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k)) (T 1 - T (-1)) * (uqKinv k ⊗ₜ[LaurentPolynomial k] (uqE k * uqF k - uqF k * uqE k)) = uqKinv k ⊗ₜ[LaurentPolynomial k] (uqK k - uqKinv k) := by
    rw [ ← uq_serre ];
    exact?;
  simp_all +decide [ mul_add, add_mul, sub_eq_add_neg, TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.tmul_sub, TensorProduct.sub_tmul ];
  convert congr_arg₂ ( · + · ) ( TensorProduct.sub_tmul ( uqK k ) ( uqKinv k ) ( uqK k ) ) ( TensorProduct.tmul_sub ( uqKinv k ) ( uqK k ) ( uqKinv k ) ) using 1 ; abel_nf

private theorem comulFreeAlg_Serre :
    comulFreeAlg k (scal' k (T 1 - T (-1)) * (gen k Uqsl2Gen.E * gen k Uqsl2Gen.F - gen k Uqsl2Gen.F * gen k Uqsl2Gen.E)) =
    comulFreeAlg k (gen k Uqsl2Gen.K - gen k Uqsl2Gen.Kinv) := by
  convert comulFreeAlg_Serre_apply_serre k using 1;
  · rw [ ← comulFreeAlg_EF_sub_FE ];
    rw [ map_mul ];
    rw [ map_sub ];
    congr! 2;
    convert ( comulFreeAlg k ).commutes _;
  · erw [ map_sub ];
    exact congr_arg₂ _ ( comulFreeAlg_ι k _ ) ( comulFreeAlg_ι k _ )

private theorem comulFreeAlg_respects_rel :
    ∀ ⦃x y : FreeAlgebra (LaurentPolynomial k) Uqsl2Gen⦄,
    ChevalleyRel k x y -> comulFreeAlg k x = comulFreeAlg k y := by
  intro x y h
  cases h with
  | KKinv => rw [comulFreeAlg_KKinv, map_one]
  | KinvK => rw [comulFreeAlg_KinvK, map_one]
  | KE => exact comulFreeAlg_KE k
  | KF => exact comulFreeAlg_KF k
  | Serre => exact comulFreeAlg_Serre k

/-- **Coproduct on U_q(sl_2)** as an algebra homomorphism. -/
noncomputable def comulUq :
    Uqsl2 k →ₐ[LaurentPolynomial k]
    (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k) :=
  RingQuot.liftAlgHom (LaurentPolynomial k) ⟨comulFreeAlg k, comulFreeAlg_respects_rel k⟩

/-! ## 2. Counit: epsilon : U_q(sl_2) to k[q,q_inv] -/

/-- Counit on generators: epsilon(E)=0, epsilon(F)=0, epsilon(K)=1, epsilon(Kinv)=1. -/
private def counitOnGen : Uqsl2Gen -> LaurentPolynomial k
  | .E    => 0
  | .F    => 0
  | .K    => 1
  | .Kinv => 1

/-- Counit lifted to the free algebra. -/
private def counitFreeAlg :
    FreeAlgebra (LaurentPolynomial k) Uqsl2Gen →ₐ[LaurentPolynomial k]
    LaurentPolynomial k :=
  FreeAlgebra.lift (LaurentPolynomial k) (counitOnGen k)

/-
The counit respects the Chevalley relations.
-/
private theorem counitFreeAlg_respects_rel :
    ∀ ⦃x y : FreeAlgebra (LaurentPolynomial k) Uqsl2Gen⦄,
    ChevalleyRel k x y -> counitFreeAlg k x = counitFreeAlg k y := by
  intro x y h;
  rcases h with ( _ | _ | _ | _ | _ ) <;> simp +decide [ counitFreeAlg ];
  · exact one_mul _;
  · exact one_mul _;
  · simp +decide [ counitOnGen ];
  · simp +decide [ counitOnGen ];
  · simp +decide [ counitOnGen ]

/-- **Counit on U_q(sl_2)** as an algebra homomorphism. -/
noncomputable def counitUq :
    Uqsl2 k →ₐ[LaurentPolynomial k] LaurentPolynomial k :=
  RingQuot.liftAlgHom (LaurentPolynomial k) ⟨counitFreeAlg k, counitFreeAlg_respects_rel k⟩

/-! ## 3. Generator-level coproduct and counit theorems -/

/--
Delta(E) = E tensor K + 1 tensor E.

PROVIDED SOLUTION
Unfold comulUq to RingQuot.liftAlgHom applied to comulFreeAlg.
Then uqE k = uqsl2Mk k (FreeAlgebra.iota _ E) and
liftAlgHom_mkAlgHom_apply gives comulFreeAlg k (FreeAlgebra.iota _ E).
Then lift_iota_apply gives comulOnGen k E = uqE k tensor uqK k + 1 tensor uqE k.
-/
theorem comul_E : comulUq k (uqE k) =
    uqE k ⊗ₜ uqK k + 1 ⊗ₜ uqE k := by
  unfold comulUq uqE uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold comulFreeAlg
  rw [FreeAlgebra.lift_ι_apply]
  rfl

/-- Delta(F) = F tensor 1 + Kinv tensor F. -/
theorem comul_F : comulUq k (uqF k) =
    uqF k ⊗ₜ (1 : Uqsl2 k) + uqKinv k ⊗ₜ uqF k := by
  unfold comulUq uqF uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold comulFreeAlg
  rw [FreeAlgebra.lift_ι_apply]
  rfl

/-- Delta(K) = K tensor K. -/
theorem comul_K : comulUq k (uqK k) =
    uqK k ⊗ₜ uqK k := by
  unfold comulUq uqK uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold comulFreeAlg
  rw [FreeAlgebra.lift_ι_apply]
  rfl

/-- Delta(Kinv) = Kinv tensor Kinv. -/
theorem comul_Kinv : comulUq k (uqKinv k) =
    uqKinv k ⊗ₜ uqKinv k := by
  unfold comulUq uqKinv uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold comulFreeAlg
  rw [FreeAlgebra.lift_ι_apply]
  rfl

/-- epsilon(E) = 0. -/
theorem counit_E : counitUq k (uqE k) = 0 := by
  unfold counitUq uqE uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold counitFreeAlg
  rw [FreeAlgebra.lift_ι_apply]; rfl

/-- epsilon(F) = 0. -/
theorem counit_F : counitUq k (uqF k) = 0 := by
  unfold counitUq uqF uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold counitFreeAlg
  rw [FreeAlgebra.lift_ι_apply]; rfl

/-- epsilon(K) = 1. -/
theorem counit_K : counitUq k (uqK k) = 1 := by
  unfold counitUq uqK uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold counitFreeAlg
  rw [FreeAlgebra.lift_ι_apply]; rfl

/-- epsilon(Kinv) = 1. -/
theorem counit_Kinv : counitUq k (uqKinv k) = 1 := by
  unfold counitUq uqKinv uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold counitFreeAlg
  rw [FreeAlgebra.lift_ι_apply]; rfl

/-! ## 4. Antipode: S : U_q(sl_2) to U_q(sl_2) (anti-homomorphism)

The antipode is S(E) = -E*Kinv, S(F) = -K*F, S(K) = Kinv, S(Kinv) = K.
It is an anti-algebra homomorphism: S(ab) = S(b)S(a).
We construct it as a linear map by defining an algebra homomorphism
to the opposite ring and composing.
-/

/-- Antipode on generators (into the opposite ring). -/
private def antipodeOnGen : Uqsl2Gen -> (Uqsl2 k)ᵐᵒᵖ
  | .E    => MulOpposite.op (-(uqE k * uqKinv k))
  | .F    => MulOpposite.op (-(uqK k * uqF k))
  | .K    => MulOpposite.op (uqKinv k)
  | .Kinv => MulOpposite.op (uqK k)

/-- Antipode lifted to the free algebra (into opposite ring). -/
private def antipodeFreeAlg :
    FreeAlgebra (LaurentPolynomial k) Uqsl2Gen →ₐ[LaurentPolynomial k]
    (Uqsl2 k)ᵐᵒᵖ :=
  FreeAlgebra.lift (LaurentPolynomial k) (antipodeOnGen k)

/--
The antipode respects the Chevalley relations (in the opposite ring).

PROVIDED SOLUTION
Check each ChevalleyRel case:
- KKinv: In the opposite ring, op(S(K)) * op(S(Kinv)) = op(Kinv) * op(K).
  In the opposite ring multiplication is reversed, so this equals op(K * Kinv) = op(1). Check.
- KinvK: Similarly, op(S(Kinv)) * op(S(K)) = op(K) * op(Kinv) = op(Kinv * K) = op(1). Check.
- KE: S reverses order: antipodeFreeAlg(K*E) uses op algebra.
  The relation S(K)*S(E) = Kinv * (-E*Kinv) in opposite ring.
  Need to verify this matches S(q^2 * E * K) = q^2 * S(K) * S(E) in opposite ring.
- Serre: Most involved, but reduces to algebraic identity.
Each case uses uq_K_mul_Kinv, uq_Kinv_mul_K, uq_KE, uq_KF, uq_serre.
-/
-- Helper: antipodeFreeAlg on a generator
private theorem antipodeFreeAlg_ι (x : Uqsl2Gen) :
    antipodeFreeAlg k (FreeAlgebra.ι (LaurentPolynomial k) x) = antipodeOnGen k x := by
  unfold antipodeFreeAlg; exact FreeAlgebra.lift_ι_apply _ _

private theorem antipodeFreeAlg_KKinv :
    antipodeFreeAlg k (gen k Uqsl2Gen.K * gen k Uqsl2Gen.Kinv) =
    (1 : (Uqsl2 k)ᵐᵒᵖ) := by
  -- By definition of antipodeFreeAlg, we have antipodeFreeAlg k (gen k Uqsl2Gen.K) = antipodeOnGen k Uqsl2Gen.K and antipodeFreeAlg k (gen k Uqsl2Gen.Kinv) = antipodeOnGen k Uqsl2Gen.Kinv.
  have h_antipode_K : antipodeFreeAlg k (gen k Uqsl2Gen.K) = antipodeOnGen k Uqsl2Gen.K := by
    exact?
  have h_antipode_Kinv : antipodeFreeAlg k (gen k Uqsl2Gen.Kinv) = antipodeOnGen k Uqsl2Gen.Kinv := by
    exact?;
  rw [ map_mul, h_antipode_K, h_antipode_Kinv ];
  convert congr_arg MulOpposite.op ( uq_K_mul_Kinv k ) using 1

private theorem antipodeFreeAlg_KinvK :
    antipodeFreeAlg k (gen k Uqsl2Gen.Kinv * gen k Uqsl2Gen.K) =
    (1 : (Uqsl2 k)ᵐᵒᵖ) := by
  simp_all +decide [ mul_comm, MulOpposite.op_mul ];
  convert congr_arg MulOpposite.op ( uq_Kinv_mul_K k ) using 1;
  convert congr_arg₂ ( · * · ) ( antipodeFreeAlg_ι k Uqsl2Gen.Kinv ) ( antipodeFreeAlg_ι k Uqsl2Gen.K ) using 1

private theorem antipodeFreeAlg_KE :
    antipodeFreeAlg k (gen k Uqsl2Gen.K * gen k Uqsl2Gen.E) =
    antipodeFreeAlg k (scal' k (T 2) * gen k Uqsl2Gen.E * gen k Uqsl2Gen.K) := by
  have : antipodeFreeAlg k (gen k Uqsl2Gen.K * gen k Uqsl2Gen.E) = MulOpposite.op (uqKinv k) * MulOpposite.op (-(uqE k * uqKinv k)) := by
    convert congr_arg₂ ( · * · ) ( antipodeFreeAlg_ι k Uqsl2Gen.K ) ( antipodeFreeAlg_ι k Uqsl2Gen.E ) using 1;
    exact map_mul _ _ _;
  have : antipodeFreeAlg k (scal' k (T 2) * gen k Uqsl2Gen.E * gen k Uqsl2Gen.K) = MulOpposite.op (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2)) * MulOpposite.op (-(uqE k * uqKinv k)) * MulOpposite.op (uqKinv k) := by
    simp +decide [ antipodeFreeAlg, antipodeOnGen ];
  simp_all +decide [ mul_assoc, mul_left_comm, mul_comm ];
  have : uqK k * uqE k = algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2) * uqE k * uqK k := by
    grind +suggestions;
  have h_mul : uqKinv k * uqK k * uqE k = uqKinv k * (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2) * uqE k * uqK k) := by
    rw [ ← this, mul_assoc ];
  have h_mul : uqKinv k * uqK k = 1 := by
    grind +suggestions;
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, h_mul ] at *;
  rename_i h₁ h₂;
  convert congr_arg ( fun x => MulOpposite.op ( uqKinv k ) * - ( MulOpposite.op ( uqKinv k ) * MulOpposite.op x ) ) h₂ using 1 ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, ← MulOpposite.op_mul, ← MulOpposite.op_neg ];
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, uq_K_mul_Kinv ];
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, Algebra.algebraMap_eq_smul_one ];
  simp +decide [ mul_assoc, mul_left_comm, Algebra.smul_def ];
  grind

private theorem antipodeFreeAlg_KF :
    antipodeFreeAlg k (gen k Uqsl2Gen.K * gen k Uqsl2Gen.F) =
    antipodeFreeAlg k (scal' k (T (-2)) * gen k Uqsl2Gen.F * gen k Uqsl2Gen.K) := by
  unfold antipodeFreeAlg;
  unfold gen scal' antipodeOnGen; simp +decide [ mul_assoc ] ;
  simp +decide [ mul_assoc, ← MulOpposite.op_mul ];
  have h_simp : MulOpposite.op (uqKinv k) * MulOpposite.op (uqK k * uqF k) = MulOpposite.op ((algebraMap k[T;T⁻¹] (Uqsl2 k)) (T (-2))) * (MulOpposite.op (uqK k * uqF k) * MulOpposite.op (uqKinv k)) := by
    simp +decide [ ← mul_assoc, ← MulOpposite.op_mul ];
    rw [ show uqKinv k * uqK k = 1 from ?_, one_mul ];
    · convert congr_arg ( · * uqKinv k ) ( uq_KF k ) using 1 ; ring;
      simp +decide [ mul_assoc, uq_K_mul_Kinv ];
      grind +suggestions;
    · exact?;
  convert congr_arg Neg.neg h_simp using 1 <;> simp +decide [ mul_assoc ];
  · grind +splitImp;
  · grind

private theorem antipodeFreeAlg_Serre :
    antipodeFreeAlg k (scal' k (T 1 - T (-1)) * (gen k Uqsl2Gen.E * gen k Uqsl2Gen.F - gen k Uqsl2Gen.F * gen k Uqsl2Gen.E)) =
    antipodeFreeAlg k (gen k Uqsl2Gen.K - gen k Uqsl2Gen.Kinv) := by
  have h_lhs : antipodeFreeAlg k (scal' k (T 1 - T (-1)) * (gen k Uqsl2Gen.E * gen k Uqsl2Gen.F - gen k Uqsl2Gen.F * gen k Uqsl2Gen.E)) = MulOpposite.op ((algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 1 - T (-1))) * (uqF k * uqE k - uqE k * uqF k)) := by
    have h_antipode : antipodeFreeAlg k (gen k Uqsl2Gen.E * gen k Uqsl2Gen.F - gen k Uqsl2Gen.F * gen k Uqsl2Gen.E) = MulOpposite.op (uqF k * uqE k - uqE k * uqF k) := by
      convert congr_arg MulOpposite.op (uq_KFEK_sub k) using 1
      unfold antipodeFreeAlg antipodeOnGen; simp +decide [mul_assoc, mul_left_comm, mul_comm]
      grind
    convert congr_arg (fun x => (algebraMap (LaurentPolynomial k) (MulOpposite (Uqsl2 k)) (T 1 - T (-1))) * x) h_antipode using 1
    · simp +decide [scal']
    · simp +decide [Algebra.algebraMap_eq_smul_one]
  rw [h_lhs]
  rw [show (algebraMap (LaurentPolynomial k) (Uqsl2 k)) (T 1 - T (-1)) * (uqF k * uqE k - uqE k * uqF k) = -(uqK k - uqKinv k) by
    convert congr_arg Neg.neg (uq_serre k) using 1; ring
    grind]
  unfold antipodeFreeAlg; simp +decide [antipodeOnGen]
  grind

private theorem antipodeFreeAlg_respects_rel :
    ∀ ⦃x y : FreeAlgebra (LaurentPolynomial k) Uqsl2Gen⦄,
    ChevalleyRel k x y -> antipodeFreeAlg k x = antipodeFreeAlg k y := by
  intro x y h
  cases h with
  | KKinv => rw [antipodeFreeAlg_KKinv, map_one]
  | KinvK => rw [antipodeFreeAlg_KinvK, map_one]
  | KE => exact antipodeFreeAlg_KE k
  | KF => exact antipodeFreeAlg_KF k
  | Serre => exact antipodeFreeAlg_Serre k

/-- Antipode as algebra hom to the opposite ring. -/
private noncomputable def antipodeOpAlg :
    Uqsl2 k →ₐ[LaurentPolynomial k] (Uqsl2 k)ᵐᵒᵖ :=
  RingQuot.liftAlgHom (LaurentPolynomial k) ⟨antipodeFreeAlg k, antipodeFreeAlg_respects_rel k⟩

/-- **Antipode on U_q(sl_2)** as a linear map. -/
noncomputable def antipodeUq : Uqsl2 k →ₗ[LaurentPolynomial k] Uqsl2 k :=
  (MulOpposite.opLinearEquiv (LaurentPolynomial k)).symm.toLinearMap.comp
    (antipodeOpAlg k).toLinearMap

/-! ## 5. Generator-level antipode theorems -/

/--
S(E) = -E * Kinv.

PROVIDED SOLUTION
Unfold antipodeUq to MulOpposite.opLinearEquiv.symm composed with antipodeOpAlg.
antipodeOpAlg k (uqE k) = liftAlgHom(antipodeFreeAlg)(uqsl2Mk(iota E))
  = antipodeFreeAlg(iota E) = lift(antipodeOnGen)(iota E) = antipodeOnGen E
  = op(-(uqE k * uqKinv k)).
Then opLinearEquiv.symm sends op(x) to x.
-/
theorem antipode_E : antipodeUq k (uqE k) = -(uqE k * uqKinv k) := by
  unfold antipodeUq antipodeOpAlg
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
  unfold uqE uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold antipodeFreeAlg
  rw [FreeAlgebra.lift_ι_apply]
  unfold antipodeOnGen
  rfl

/-- S(F) = -K * F. -/
theorem antipode_F : antipodeUq k (uqF k) = -(uqK k * uqF k) := by
  unfold antipodeUq antipodeOpAlg
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
  unfold uqF uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold antipodeFreeAlg
  rw [FreeAlgebra.lift_ι_apply]
  unfold antipodeOnGen
  rfl

/-- S(K) = Kinv. -/
theorem antipode_K : antipodeUq k (uqK k) = uqKinv k := by
  unfold antipodeUq antipodeOpAlg
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
  unfold uqK uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold antipodeFreeAlg
  rw [FreeAlgebra.lift_ι_apply]
  unfold antipodeOnGen
  rfl

/-- S(Kinv) = K. -/
theorem antipode_Kinv : antipodeUq k (uqKinv k) = uqK k := by
  unfold antipodeUq antipodeOpAlg
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
  unfold uqKinv uqsl2Mk
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  unfold antipodeFreeAlg
  rw [FreeAlgebra.lift_ι_apply]
  unfold antipodeOnGen
  rfl

/-! ## 6. Coalgebra axioms -/

/-
Coassociativity: (Delta tensor id) composed with Delta = (id tensor Delta) composed with Delta.
-/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc (LaurentPolynomial k) (LaurentPolynomial k)
      (LaurentPolynomial k) (Uqsl2 k) (Uqsl2 k) (Uqsl2 k)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulUq k) (.id (LaurentPolynomial k) (Uqsl2 k))).comp
        (comulUq k)) =
    (Algebra.TensorProduct.map (.id (LaurentPolynomial k) (Uqsl2 k)) (comulUq k)).comp
      (comulUq k) := by
  ext x;
  rcases x with ( _ | _ | _ | _ );
  · simp +decide [ comul_E ];
    erw [ comul_E ];
    simp +decide [ comul_E, comul_K ];
    simp +decide [ add_mul, mul_add, TensorProduct.tmul_add, TensorProduct.add_tmul ];
    erw [ Algebra.TensorProduct.assoc_tmul ] ; simp +decide [ add_assoc ];
  · simp +decide [ Algebra.TensorProduct.assoc, Algebra.TensorProduct.map ];
    erw [ comul_F ];
    simp +decide [ AlgebraTensorModule.map_tmul, AlgebraTensorModule.assoc_tmul ];
    erw [ comul_F, comul_Kinv ];
    simp +decide [ AlgebraTensorModule.assoc_tmul, TensorProduct.tmul_add, TensorProduct.add_tmul ];
    rw [ add_assoc ];
    congr;
  · simp +decide [ comul_K ];
    erw [ comul_K ];
    simp +decide [ Algebra.TensorProduct.map_tmul, comul_K ];
  · simp +decide [ comul_Kinv ];
    erw [ show ( comulUq k ) ( RingQuot.mkAlgHom _ _ ( FreeAlgebra.ι _ _ ) ) = uqKinv k ⊗ₜ uqKinv k from ?_ ];
    · simp +decide [ Algebra.TensorProduct.map_tmul, comul_Kinv ];
    · convert comul_Kinv k using 1

/-
Right counitality: (epsilon tensor id) composed with Delta = lid isomorphism.
-/
theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counitUq k) (.id (LaurentPolynomial k) (Uqsl2 k))).comp
      (comulUq k) =
    (Algebra.TensorProduct.lid (LaurentPolynomial k) (Uqsl2 k)).symm := by
  ext x;
  cases x;
  · simp +decide [ Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid ];
    erw [ comul_E ] ; simp +decide [ Algebra.TensorProduct.map_tmul ];
    erw [ counit_E ] ; simp +decide [ Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct ];
    rfl;
  · simp +zetaDelta at *;
    erw [ comul_F ];
    simp +decide [ counit_F, counit_Kinv ];
    rfl;
  · convert congr_arg ( fun x : ( Uqsl2 k ) ⊗[LaurentPolynomial k] ( Uqsl2 k ) => ( Algebra.TensorProduct.map ( counitUq k ) ( AlgHom.id k[T;T⁻¹] ( Uqsl2 k ) ) ) x ) ( comul_K k ) using 1;
    simp +decide [ Algebra.TensorProduct.map_tmul, counit_K ];
    rfl;
  · convert congr_arg ( Algebra.TensorProduct.map ( counitUq k ) ( AlgHom.id k[T;T⁻¹] ( Uqsl2 k ) ) ) ( comul_Kinv k ) using 1;
    simp +decide [ Algebra.TensorProduct.map_tmul, counit_Kinv ];
    rfl

/-
Left counitality: (id tensor epsilon) composed with Delta = rid isomorphism.
-/
theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (.id (LaurentPolynomial k) (Uqsl2 k)) (counitUq k)).comp
      (comulUq k) =
    (Algebra.TensorProduct.rid (LaurentPolynomial k) (LaurentPolynomial k) (Uqsl2 k)).symm := by
  ext x;
  cases x <;> simp +decide [ * ];
  · erw [ comul_E ];
    simp +decide [ counit_K, counit_E ];
    rfl;
  · convert congr_arg ( Algebra.TensorProduct.map ( AlgHom.id _ _ ) ( counitUq k ) ) ( comul_F k ) using 1;
    simp +decide [ Algebra.TensorProduct.map_tmul ];
    rw [ counit_F ] ; aesop;
  · convert congr_arg ( Algebra.TensorProduct.map ( AlgHom.id _ _ ) ( counitUq k ) ) ( comul_K k ) using 1;
    simp +decide [ uqK ];
    congr! 1;
    exact Eq.symm ( counit_K k );
  · erw [ comul_Kinv ];
    erw [ Algebra.TensorProduct.map_tmul ] ; simp +decide [ * ];
    exact congr_arg₂ _ rfl ( counit_Kinv k )

/-! ## 7. Bialgebra instance -/

/-- **Bialgebra instance for U_q(sl_2).** -/
noncomputable instance : Bialgebra (LaurentPolynomial k) (Uqsl2 k) :=
  Bialgebra.ofAlgHom (comulUq k) (counitUq k)
    (comul_coassoc k) (comul_rTensor_counit k) (comul_lTensor_counit k)

/-! ## 8. HopfAlgebra instance -/

/-
Helper: the convolution mul' ∘ rTensor(S) maps scalars to scalars
-/
private theorem antipodeUq_one :
    antipodeUq k 1 = 1 := by
  simp +decide [ antipodeUq, antipodeOpAlg ]

/-
Helper: rTensor(S) applied to Comul respects scalars
-/
private theorem convR_algebraMap (r : LaurentPolynomial k) :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (algebraMap (LaurentPolynomial k) (Uqsl2 k) r))) =
    algebraMap (LaurentPolynomial k) (Uqsl2 k) r := by
  unfold antipodeUq;
  simp +decide [ antipodeOpAlg ]

/-
Helper: convolution for E
-/
private theorem convR_E :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (uqE k))) = 0 := by
  have h1 : (LinearMap.mul' k[T;T⁻¹] (Uqsl2 k)) ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k)) ((comulUq k) (uqE k))) = -(uqE k * uqKinv k * uqK k) + uqE k := by
    convert congr_arg ( fun x : ( Uqsl2 k ) ⊗[LaurentPolynomial k] ( Uqsl2 k ) => ( LinearMap.mul' k[T;T⁻¹] ( Uqsl2 k ) ) x ) ( LinearMap.map_add ( LinearMap.rTensor ( Uqsl2 k ) ( antipodeUq k ) ) ( uqE k ⊗ₜ[LaurentPolynomial k] uqK k ) ( 1 ⊗ₜ[LaurentPolynomial k] uqE k ) ) using 1;
    · rw [ comul_E ];
    · simp +decide [ LinearMap.rTensor_tmul, LinearMap.mul'_apply ];
      rw [ antipode_E, antipodeUq_one ];
      grind +revert;
  have h2 : uqKinv k * uqK k = 1 := by
    exact?;
  grind +qlia

/-
Helper: convolution for F
-/
private theorem convR_F :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (uqF k))) = 0 := by
  rw [ comul_F ];
  erw [ LinearMap.map_add ] ; simp +decide [ LinearMap.mul' ] ;
  rw [ antipode_F, antipode_Kinv ] ; abel1

/-
Helper: convolution for K
-/
private theorem convR_K :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (uqK k))) = 1 := by
  convert uq_Kinv_mul_K k;
  rw [ comul_K ];
  simp +decide [ antipode_K ]

/-
Helper: convolution for Kinv
-/
private theorem convR_Kinv :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (uqKinv k))) = 1 := by
  by_contra h_contra;
  convert SKEFTHawking.antipodeUq_one k using 1;
  constructor <;> intro h <;> simp_all +decide [ comul_Kinv, antipode_Kinv, uq_K_mul_Kinv ]

/-
Key helper: if mul'(rTensor(S)(x)) = algebraMap(r), then
mul'(rTensor(S)(x * y)) = algebraMap(r) * mul'(rTensor(S)(y))
for any y in the tensor product.
-/
private theorem convR_mul_step
    (x y : (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k))
    (r : LaurentPolynomial k)
    (hx : (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
            ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k)) x) =
          algebraMap (LaurentPolynomial k) (Uqsl2 k) r) :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k)) (x * y)) =
    algebraMap (LaurentPolynomial k) (Uqsl2 k) r *
      (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
        ((LinearMap.rTensor (Uqsl2 k) (antipodeUq k)) y) := by
  revert hx;
  induction' y using TensorProduct.induction_on with c d;
  · simp +decide;
  · intro hx
    have h_sum : ∃ (s : Finset (Uqsl2 k × Uqsl2 k)), x = ∑ p ∈ s, p.1 ⊗ₜ p.2 := by
      exact?;
    obtain ⟨ s, rfl ⟩ := h_sum; simp +decide [ hx, mul_assoc, Finset.sum_mul _ _ _ ] ;
    have h_antipode_mul : ∀ a b : Uqsl2 k, antipodeUq k (a * b) = (antipodeUq k b) * (antipodeUq k a) := by
      intro a b
      simp [antipodeUq];
    simp_all +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ];
    simp +decide only [← Finset.mul_sum _ _ _, mul_assoc];
    rw [ hx ];
    simp +decide [ mul_assoc, Algebra.commutes ];
  · simp_all +decide [ mul_add, add_mul ]

/-
Helper: convolution for lTensor(S) for generators
-/
private theorem convL_E :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (uqE k))) = 0 := by
  simp +decide [ comul_E, antipode_E, antipode_K, LinearMap.lTensor ];
  grobner

private theorem convL_F :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (uqF k))) = 0 := by
  have h_convL_F : (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
    ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k))
      ((comulUq k) (uqF k))) = uqF k * 1 - uqKinv k * uqK k * uqF k := by
        have h_convL_F : (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
          ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k))
            ((comulUq k) (uqF k))) = uqF k * 1 + uqKinv k * (-uqK k * uqF k) := by
              rw [ SKEFTHawking.comul_F ];
              simp +decide [ LinearMap.lTensor, LinearMap.mul' ];
              rw [ SKEFTHawking.antipodeUq_one, SKEFTHawking.antipode_F ] ; norm_num;
              grobner;
        grind;
  rw [ h_convL_F, uq_Kinv_mul_K ] ; norm_num;
  grind +qlia

private theorem convL_K :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (uqK k))) = 1 := by
  rw [ comul_K, LinearMap.lTensor_tmul ];
  convert uq_K_mul_Kinv k using 1;
  simp [antipode_K]

private theorem convL_Kinv :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (uqKinv k))) = 1 := by
  convert convL_K k using 1;
  simp +decide [ comul_Kinv, comul_K ];
  rw [ antipode_Kinv, antipode_K ];
  rw [ uq_Kinv_mul_K, uq_K_mul_Kinv ]

private theorem convL_algebraMap (r : LaurentPolynomial k) :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k))
        ((comulUq k) (algebraMap (LaurentPolynomial k) (Uqsl2 k) r))) =
    algebraMap (LaurentPolynomial k) (Uqsl2 k) r := by
  simp +decide [ RingQuot.liftAlgHom ];
  rw [ antipodeUq_one, mul_one ]

/-
NOTE: for lTensor, the correct factoring is on y (not x):
if ψ_L(y) = algebraMap(r), then ψ_L(x*y) = ψ_L(x) * algebraMap(r)
This is because for elementary tensors (a⊗b)*(c⊗d) = ac⊗bd,
lTensor(S)(ac⊗bd) = ac⊗S(d)S(b), mul' gives a*c*S(d)*S(b).
If c*S(d) = algebraMap(r), then a*algebraMap(r)*S(b) = algebraMap(r)*a*S(b).
-/
private theorem convL_mul_step
    (x y : (Uqsl2 k) ⊗[LaurentPolynomial k] (Uqsl2 k))
    (r : LaurentPolynomial k)
    (hy : (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
            ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k)) y) =
          algebraMap (LaurentPolynomial k) (Uqsl2 k) r) :
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k)) (x * y)) =
    (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k))
      ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k)) x) *
    algebraMap (LaurentPolynomial k) (Uqsl2 k) r := by
  induction' x using TensorProduct.induction_on with a b ihx ihy;
  · simp +decide;
  · have h_eval : ∀ (x : Uqsl2 k ⊗[LaurentPolynomial k] Uqsl2 k), (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k)) ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k)) (a ⊗ₜ[LaurentPolynomial k] b * x)) = a * (LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k)) ((LinearMap.lTensor (Uqsl2 k) (antipodeUq k)) x) * antipodeUq k b := by
      intro x; induction' x using TensorProduct.induction_on with c d ihx ihy; aesop;
      · have h_antipode : antipodeUq k (b * d) = antipodeUq k d * antipodeUq k b := by
          have h_antipode : ∀ (x y : Uqsl2 k), antipodeUq k (x * y) = antipodeUq k y * antipodeUq k x := by
            intro x y
            have h_antipode_def : antipodeUq k = (MulOpposite.opLinearEquiv (LaurentPolynomial k)).symm.toLinearMap.comp (antipodeOpAlg k).toLinearMap := by
              grind +locals
            simp +decide [ h_antipode_def, antipodeOpAlg ];
          exact h_antipode b d;
        simp +decide [ h_antipode, mul_assoc ];
      · simp_all +decide [ mul_add, add_mul ];
    rw [ h_eval, hy ];
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, Algebra.commutes ];
  · simp_all +decide [ add_mul, mul_add ]

theorem antipode_right :
    LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k) ∘ₗ
      (antipodeUq k).rTensor (Uqsl2 k) ∘ₗ
      Coalgebra.comul =
    (Algebra.linearMap (LaurentPolynomial k) (Uqsl2 k)) ∘ₗ Coalgebra.counit := by
  ext x;
  obtain ⟨ x, rfl ⟩ := RingQuot.mkAlgHom_surjective ( LaurentPolynomial k ) ( ChevalleyRel k ) x;
  induction' x using FreeAlgebra.induction with r x y hx hy;
  · convert convR_algebraMap k r using 1;
    · simp +decide [ comulUq ];
    · simp +decide [ uqsl2Mk ];
  · cases x <;> simp +decide [ * ];
    · convert convR_E k using 1;
      convert congr_arg ( algebraMap ( LaurentPolynomial k ) ( Uqsl2 k ) ) ( counit_E k ) using 1;
    · convert convR_F k using 1;
      convert congr_arg ( algebraMap ( LaurentPolynomial k ) ( Uqsl2 k ) ) ( counit_F k ) using 1;
    · convert convR_K k using 1;
      erw [ show ( RingQuot.mkAlgHom k[T;T⁻¹] ( ChevalleyRel k ) ) ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.K ) = uqK k from rfl ] ; exact congr_arg _ ( counit_K k );
    · convert convR_Kinv k using 1;
      convert congr_arg ( algebraMap ( LaurentPolynomial k ) ( Uqsl2 k ) ) ( counit_Kinv k ) using 1;
  · simp_all +decide [ mul_assoc, CoalgebraStruct.comul ];
    convert convR_mul_step k _ _ _ hy using 1;
    aesop;
  · aesop

theorem antipode_left :
    LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k) ∘ₗ
      (antipodeUq k).lTensor (Uqsl2 k) ∘ₗ
      Coalgebra.comul =
    (Algebra.linearMap (LaurentPolynomial k) (Uqsl2 k)) ∘ₗ Coalgebra.counit := by
  ext x;
  obtain ⟨ x, rfl ⟩ := RingQuot.mkAlgHom_surjective ( LaurentPolynomial k ) ( ChevalleyRel k ) x;
  induction' x using FreeAlgebra.induction with r x y hx hy;
  · convert convL_algebraMap k r using 1;
    · simp +decide [ comulUq ];
    · convert counitFreeAlg_respects_rel k _;
      rotate_left;
      exact FreeAlgebra.ι _ Uqsl2Gen.K * FreeAlgebra.ι _ Uqsl2Gen.Kinv;
      exact 1;
      · exact ChevalleyRel.KKinv;
      · simp +decide [ counitFreeAlg ];
        exact one_mul _;
  · rcases x with ( _ | _ | _ | _ ) <;> simp +decide [ * ];
    · convert convL_E k;
      convert congr_arg ( algebraMap ( LaurentPolynomial k ) ( Uqsl2 k ) ) ( counit_E k ) using 1;
    · convert convL_F k using 1;
      convert congr_arg ( algebraMap ( LaurentPolynomial k ) ( Uqsl2 k ) ) ( counit_F k ) using 1;
    · convert convL_K k using 1;
      erw [ show ( RingQuot.mkAlgHom k[T;T⁻¹] ( ChevalleyRel k ) ) ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.K ) = uqK k from rfl ] ; exact congr_arg _ ( counit_K k );
    · convert convL_Kinv k using 1;
      convert congr_arg ( algebraMap ( LaurentPolynomial k ) ( Uqsl2 k ) ) ( counit_Kinv k ) using 1;
  · -- mul case: use convL_mul_step
    simp_all +decide [ ← LinearMap.comp_assoc, ← RingHom.comp_apply ];
    convert convL_mul_step k _ _ _ _ using 1;
    rw [ hy ];
    grind
  · aesop

/-- **HopfAlgebra instance for U_q(sl_2).** -/
noncomputable instance : HopfAlgebra (LaurentPolynomial k) (Uqsl2 k) where
  antipode := antipodeUq k
  mul_antipode_rTensor_comul := antipode_right k
  mul_antipode_lTensor_comul := antipode_left k

/-! ## 9. Structural theorems -/

/-
S squared = Ad(K): the squared antipode is conjugation by K.

Verified on generators:
  S^2(E) = S(-E*Kinv) = -S(Kinv)*S(E) = -K*(-E*Kinv) = K*E*Kinv = q^2*E. Check.
  S^2(F) = S(-K*F) = -S(F)*S(K) = -(-K*F)*Kinv = K*F*Kinv = q^{-2}*F. Check.
  S^2(K) = S(Kinv) = K. Check.
-/
theorem antipode_squared_is_ad_K (x : Uqsl2 k) :
    antipodeUq k (antipodeUq k x) = uqK k * x * uqKinv k := by
  have h_sq_antipode_gen : ∀ x : Uqsl2Gen, (antipodeUq k) ((antipodeUq k) (uqsl2Mk k (FreeAlgebra.ι (LaurentPolynomial k) x))) = uqK k * uqsl2Mk k (FreeAlgebra.ι (LaurentPolynomial k) x) * uqKinv k := by
    intro x
    induction' x with x ih;
    · erw [ show ( antipodeUq k ) ( uqE k ) = - ( uqE k * uqKinv k ) from ?_ ];
      · erw [ show ( antipodeUq k ) ( - ( uqE k * uqKinv k ) ) = - ( antipodeUq k ) ( uqE k * uqKinv k ) from ?_ ];
        · have h_antipode_E : (antipodeUq k) (uqE k * uqKinv k) = (antipodeUq k) (uqKinv k) * (antipodeUq k) (uqE k) := by
            simp +decide [ antipodeUq, RingQuot.liftAlgHom ];
          rw [ h_antipode_E, antipode_E, antipode_Kinv ];
          simp +decide [ mul_assoc, uqsl2Mk ];
          simp +decide [ uqE ];
          simp +decide [ uqsl2Mk ];
          grind;
        · exact map_neg ( antipodeUq k ) _;
      · exact?;
    · convert congr_arg ( fun x => ( antipodeUq k ) x ) ( antipode_F k ) using 1;
      rw [ show uqsl2Mk k ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.F ) = uqF k from ?_ ];
      · simp +decide [ antipodeUq ];
        erw [ show ( antipodeOpAlg k ) ( - ( uqK k * uqF k ) ) = MulOpposite.op ( - ( antipodeUq k ( uqK k * uqF k ) ) ) from ?_ ];
        · simp +decide [ antipodeUq ];
          erw [ show ( antipodeOpAlg k ) ( uqF k ) = MulOpposite.op ( - ( uqK k * uqF k ) ) from ?_, show ( antipodeOpAlg k ) ( uqK k ) = MulOpposite.op ( uqKinv k ) from ?_ ] ; simp +decide [ mul_assoc ];
          · grind;
          · convert antipode_K k using 1;
            simp +decide [ antipodeUq ];
            rw [ ← MulOpposite.unop_inj ] ; simp +decide [ MulOpposite.unop_op ];
          · rw [ show uqF k = uqsl2Mk k ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.F ) from ?_, antipodeOpAlg ];
            · simp +decide [ uqsl2Mk ];
              convert antipodeFreeAlg_ι k Uqsl2Gen.F using 1;
            · rfl;
        · simp +decide [ antipodeOpAlg, antipodeUq ];
          grind;
      · rfl;
    · simp +decide [ uqsl2Mk, antipode_K, antipode_Kinv ];
      erw [ show ( RingQuot.mkAlgHom k[T;T⁻¹] ( ChevalleyRel k ) ) ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.K ) = uqK k from rfl ] ; simp +decide [ antipode_K, antipode_Kinv ];
      rw [ mul_assoc, uq_K_mul_Kinv, mul_one ];
    · erw [ show ( uqsl2Mk k ) ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.Kinv ) = uqKinv k from rfl ] ; simp +decide [ antipode_Kinv, antipode_K ] ;
      rw [ uq_K_mul_Kinv, one_mul ];
  obtain ⟨ y, rfl ⟩ := RingQuot.mkAlgHom_surjective ( LaurentPolynomial k ) ( ChevalleyRel k ) x;
  induction' y using FreeAlgebra.induction with x ihx y ihy z ihz;
  · -- Since the antipode is an algebra homomorphism, we can apply it to the algebra map.
    have h_antipode_algMap : ∀ r : LaurentPolynomial k, antipodeUq k (algebraMap (LaurentPolynomial k) (Uqsl2 k) r) = algebraMap (LaurentPolynomial k) (Uqsl2 k) r := by
      intro r
      simp [antipodeUq];
    convert h_antipode_algMap x using 1;
    · simp only [AlgHom.commutes]; exact congr_arg _ (h_antipode_algMap x);
    · convert congr_arg ( fun y => algebraMap ( LaurentPolynomial k ) ( Uqsl2 k ) x * y ) ( uq_K_mul_Kinv k ) using 1;
      · simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
        rw [ ← mul_assoc, ← mul_assoc ];
        rw [ ← Algebra.commutes ];
      · rw [ mul_one ];
  · exact h_sq_antipode_gen ihx;
  · have h_antipode_mul : ∀ x y : Uqsl2 k, (antipodeUq k) (x * y) = (antipodeUq k) y * (antipodeUq k) x := by
      simp +decide [ antipodeUq ];
    simp_all +decide [ mul_assoc ];
    simp +decide [ ← mul_assoc, uq_K_mul_Kinv ];
    simp +decide [ mul_assoc, uq_Kinv_mul_K ];
  · simp_all +decide [ mul_add, add_mul ]

/-- Delta(K) = K tensor K shows K is grouplike. -/
theorem K_grouplike : comulUq k (uqK k) = uqK k ⊗ₜ uqK k :=
  comul_K k

/-- Delta(Kinv) = Kinv tensor Kinv shows Kinv is grouplike. -/
theorem Kinv_grouplike : comulUq k (uqKinv k) = uqKinv k ⊗ₜ uqKinv k :=
  comul_Kinv k

/-- epsilon(K) * epsilon(Kinv) = 1 (counit preserves invertibility). -/
theorem counit_K_mul_Kinv : counitUq k (uqK k) * counitUq k (uqKinv k) = 1 := by
  rw [counit_K, counit_Kinv, one_mul]

/-
The antipode commutes with the counit: epsilon composed with S = epsilon.
-/
theorem counit_comp_antipode (x : Uqsl2 k) :
    counitUq k (antipodeUq k x) = counitUq k x := by
  obtain ⟨ x, rfl ⟩ := RingQuot.mkAlgHom_surjective ( LaurentPolynomial k ) ( ChevalleyRel k ) x;
  induction x using FreeAlgebra.induction;
  · unfold antipodeUq; simp +decide [ antipodeUq_one ] ;
  · rename_i x;
    rcases x with ( _ | _ | _ | _ );
    · erw [ show ( RingQuot.mkAlgHom k[T;T⁻¹] ( ChevalleyRel k ) ) ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.E ) = uqE k from rfl ];
      rw [ antipode_E ];
      grind +suggestions;
    · erw [ show ( RingQuot.mkAlgHom k[T;T⁻¹] ( ChevalleyRel k ) ) ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.F ) = uqF k from rfl ];
      rw [ antipode_F ];
      grind +suggestions;
    · convert counit_Kinv k;
      · convert antipode_K k;
      · convert counit_K k;
    · erw [ show ( RingQuot.mkAlgHom k[T;T⁻¹] ( ChevalleyRel k ) ) ( FreeAlgebra.ι k[T;T⁻¹] Uqsl2Gen.Kinv ) = uqKinv k from rfl ] ; simp +decide [ antipode_Kinv ];
      rw [ counit_K, counit_Kinv ];
  · rename_i a b ha hb;
    have h_antipode_mul : antipodeUq k (RingQuot.mkAlgHom (LaurentPolynomial k) (ChevalleyRel k) (a * b)) = antipodeUq k (RingQuot.mkAlgHom (LaurentPolynomial k) (ChevalleyRel k) b) * antipodeUq k (RingQuot.mkAlgHom (LaurentPolynomial k) (ChevalleyRel k) a) := by
      unfold antipodeUq;
      simp +decide [ antipodeOpAlg ];
    simp_all +decide [ mul_comm ];
  · aesop

/-! ## 10. Module summary -/

/--
Uqsl2Hopf module: HopfAlgebra structure on U_q(sl_2).
  - Coalgebra: Delta, epsilon defined via universal property of RingQuot
  - Bialgebra: via Bialgebra.ofAlgHom with coassociativity + counitality
  - HopfAlgebra: antipode S via opposite ring construction
  - Generator-level formulas: 4 comul + 4 counit + 4 antipode = 12 explicit
  - Coalgebra axioms: coassociativity + 2 counitality = 3
  - Antipode axioms: left + right = 2
  - Structural: S^2 = Ad(K), grouplike K/Kinv, counit_comp_S = counit = 3
  - Total: 21 theorems + Bialgebra + HopfAlgebra instances
-/
theorem uqsl2_hopf_summary : True := trivial

end SKEFTHawking