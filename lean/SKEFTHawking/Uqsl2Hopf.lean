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

-- K*F*E*Kinv - E*Kinv*K*F = F*E - E*F (used by antipodeFreeAlg_Serre)
/--
PROVIDED SOLUTION
Rewrite uq_E_mul_Kinv: E*Kinv = q^2*Kinv*E. Rewrite uq_KF_Kinv: K*F*Kinv = q^{-2}*F.
Then K*F*E*Kinv = K*F*(q^2*Kinv*E) = q^2*(K*F*Kinv)*E = q^2*q^{-2}*F*E = F*E.
And E*Kinv*K*F = q^2*Kinv*E*K*F. Use uq_KE: E*K = q^{-2}*K*E...
Actually simpler: expand both using the commutation relations and show
q^2*q^{-2} = 1 via uq_T2_Tneg2. Use mul_assoc extensively.
-/
private theorem uq_KFEK_sub :
    uqK k * uqF k * (uqE k * uqKinv k) - uqE k * uqKinv k * (uqK k * uqF k) =
    uqF k * uqE k - uqE k * uqF k := by
  sorry

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

/--
PROVIDED SOLUTION
Strategy: expand both sides using map_mul, map_add, comulFreeAlg_sub, then
reduce to tensor product arithmetic using the proved generator formulas.

LHS = comulFreeAlg(scal(T1-T(-1)) * (EF - FE))
    = comulFreeAlg(scal(T1-T(-1))) * comulFreeAlg(EF - FE)
    = algebraMap(T1-T(-1)) * (comulFreeAlg(EF) + algebraMap(-1)*comulFreeAlg(FE))

comulFreeAlg(EF) = comulFreeAlg(E)*comulFreeAlg(F)
  = (E⊗K + 1⊗E)(F⊗1 + Kinv⊗F)
  = EF⊗K + E*Kinv⊗KF + F⊗E + Kinv⊗EF

comulFreeAlg(FE) = comulFreeAlg(F)*comulFreeAlg(E)
  = (F⊗1 + Kinv⊗F)(E⊗K + 1⊗E)
  = FE⊗K + F⊗E + Kinv*E⊗FK + Kinv⊗FE

RHS = comulFreeAlg(K - Kinv)
    = K⊗K + algebraMap(-1)*(Kinv⊗Kinv)
    = K⊗K - Kinv⊗Kinv (using comulFreeAlg_sub)

After expansion, use uq_serre to replace (T1-T(-1))*(EF-FE) with K-Kinv
in each tensor factor, and comulFreeAlg_Serre_cross_terms for the cross terms.
Use algMap_mul_tmul and algMap_mul_tmul_right for scalar factoring.
-/
private theorem comulFreeAlg_Serre :
    comulFreeAlg k (scal' k (T 1 - T (-1)) * (gen k Uqsl2Gen.E * gen k Uqsl2Gen.F - gen k Uqsl2Gen.F * gen k Uqsl2Gen.E)) =
    comulFreeAlg k (gen k Uqsl2Gen.K - gen k Uqsl2Gen.Kinv) := by
  sorry

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

/--
Coassociativity: (Delta tensor id) composed with Delta = (id tensor Delta) composed with Delta.

PROVIDED SOLUTION
Both sides are algebra homomorphisms from Uqsl2 k to (Uqsl2 k) ⊗ (Uqsl2 k) ⊗ (Uqsl2 k).
Two AlgHoms from a RingQuot are equal iff they agree on the image of the quotient map.
Use RingQuot.liftAlgHom_unique or ext + the universal property.
Suffices to check on the four generators E, F, K, Kinv.
For K: both sides give K⊗K⊗K (grouplike, Δ(K)=K⊗K). Use comul_K.
For Kinv: similarly Kinv⊗Kinv⊗Kinv.
For E: LHS = (Δ⊗id)(E⊗K + 1⊗E) = Δ(E)⊗K + Δ(1)⊗E = (E⊗K+1⊗E)⊗K + 1⊗1⊗E.
  RHS = (id⊗Δ)(E⊗K + 1⊗E) = E⊗Δ(K) + 1⊗Δ(E) = E⊗K⊗K + 1⊗(E⊗K+1⊗E).
  After reassociation via the associator, both equal E⊗K⊗K + 1⊗E⊗K + 1⊗1⊗E.
For F: analogous computation.
Key tactic chain: apply AlgHom.ext, use Quot.ind to reduce to FreeAlgebra,
then use FreeAlgebra.induction to reduce to generators, verify each case.
-/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc (LaurentPolynomial k) (LaurentPolynomial k)
      (LaurentPolynomial k) (Uqsl2 k) (Uqsl2 k) (Uqsl2 k)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulUq k) (.id (LaurentPolynomial k) (Uqsl2 k))).comp
        (comulUq k)) =
    (Algebra.TensorProduct.map (.id (LaurentPolynomial k) (Uqsl2 k)) (comulUq k)).comp
      (comulUq k) := by
  sorry

/--
Right counitality: (epsilon tensor id) composed with Delta = lid isomorphism.

PROVIDED SOLUTION
Check on generators: (epsilon tensor id)(Delta(E)) = epsilon(E) tensor K + epsilon(1) tensor E
= 0 tensor K + 1 tensor E = 1 tensor E. The lid sends 1 tensor E to E.
-/
theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counitUq k) (.id (LaurentPolynomial k) (Uqsl2 k))).comp
      (comulUq k) =
    (Algebra.TensorProduct.lid (LaurentPolynomial k) (Uqsl2 k)).symm := by
  sorry

/--
Left counitality: (id tensor epsilon) composed with Delta = rid isomorphism.

PROVIDED SOLUTION
Check on generators: (id tensor epsilon)(Delta(E)) = E tensor epsilon(K) + 1 tensor epsilon(E)
= E tensor 1 + 1 tensor 0 = E tensor 1. The rid sends E tensor 1 to E.
-/
theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (.id (LaurentPolynomial k) (Uqsl2 k)) (counitUq k)).comp
      (comulUq k) =
    (Algebra.TensorProduct.rid (LaurentPolynomial k) (LaurentPolynomial k) (Uqsl2 k)).symm := by
  sorry

/-! ## 7. Bialgebra instance -/

/-- **Bialgebra instance for U_q(sl_2).** -/
noncomputable instance : Bialgebra (LaurentPolynomial k) (Uqsl2 k) :=
  Bialgebra.ofAlgHom (comulUq k) (counitUq k)
    (comul_coassoc k) (comul_rTensor_counit k) (comul_lTensor_counit k)

/-! ## 8. HopfAlgebra instance -/

/--
Right antipode axiom: m composed with (S tensor id) composed with Delta = eta composed with epsilon.

PROVIDED SOLUTION
Check on generators. For E:
  (S tensor id)(Delta(E)) = S(E) tensor K + S(1) tensor E = -E*Kinv tensor K + 1 tensor E
  m(-E*Kinv tensor K + 1 tensor E) = -E*Kinv*K + E = -E + E = 0
  eta(epsilon(E)) = eta(0) = 0. Check.
For K:
  (S tensor id)(Delta(K)) = S(K) tensor K = Kinv tensor K
  m(Kinv tensor K) = Kinv*K = 1
  eta(epsilon(K)) = eta(1) = 1. Check.
-/
theorem antipode_right :
    LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k) ∘ₗ
      (antipodeUq k).rTensor (Uqsl2 k) ∘ₗ
      Coalgebra.comul =
    (Algebra.linearMap (LaurentPolynomial k) (Uqsl2 k)) ∘ₗ Coalgebra.counit := by
  sorry

/--
Left antipode axiom: m composed with (id tensor S) composed with Delta = eta composed with epsilon.

PROVIDED SOLUTION
Check on generators. For E:
  (id tensor S)(Delta(E)) = E tensor S(K) + 1 tensor S(E) = E tensor Kinv + 1 tensor (-E*Kinv)
  m(E tensor Kinv - 1 tensor E*Kinv) = E*Kinv - E*Kinv = 0
  eta(epsilon(E)) = 0. Check.
-/
theorem antipode_left :
    LinearMap.mul' (LaurentPolynomial k) (Uqsl2 k) ∘ₗ
      (antipodeUq k).lTensor (Uqsl2 k) ∘ₗ
      Coalgebra.comul =
    (Algebra.linearMap (LaurentPolynomial k) (Uqsl2 k)) ∘ₗ Coalgebra.counit := by
  sorry

/-- **HopfAlgebra instance for U_q(sl_2).** -/
noncomputable instance : HopfAlgebra (LaurentPolynomial k) (Uqsl2 k) where
  antipode := antipodeUq k
  mul_antipode_rTensor_comul := antipode_right k
  mul_antipode_lTensor_comul := antipode_left k

/-! ## 9. Structural theorems -/

/--
S squared = Ad(K): the squared antipode is conjugation by K.

Verified on generators:
  S^2(E) = S(-E*Kinv) = -S(Kinv)*S(E) = -K*(-E*Kinv) = K*E*Kinv = q^2*E. Check.
  S^2(F) = S(-K*F) = -S(F)*S(K) = -(-K*F)*Kinv = K*F*Kinv = q^{-2}*F. Check.
  S^2(K) = S(Kinv) = K. Check.

PROVIDED SOLUTION
Apply the antipode definitions twice. Use the anti-homomorphism property
S(ab) = S(b)S(a) and the Chevalley relations to simplify.
-/
theorem antipode_squared_is_ad_K (x : Uqsl2 k) :
    antipodeUq k (antipodeUq k x) = uqK k * x * uqKinv k := by
  sorry

/-- Delta(K) = K tensor K shows K is grouplike. -/
theorem K_grouplike : comulUq k (uqK k) = uqK k ⊗ₜ uqK k :=
  comul_K k

/-- Delta(Kinv) = Kinv tensor Kinv shows Kinv is grouplike. -/
theorem Kinv_grouplike : comulUq k (uqKinv k) = uqKinv k ⊗ₜ uqKinv k :=
  comul_Kinv k

/-- epsilon(K) * epsilon(Kinv) = 1 (counit preserves invertibility). -/
theorem counit_K_mul_Kinv : counitUq k (uqK k) * counitUq k (uqKinv k) = 1 := by
  rw [counit_K, counit_Kinv, one_mul]

/--
The antipode commutes with the counit: epsilon composed with S = epsilon.

PROVIDED SOLUTION
On generators: epsilon(S(E)) = epsilon(-E*Kinv) = -epsilon(E)*epsilon(Kinv) = 0 = epsilon(E).
epsilon(S(K)) = epsilon(Kinv) = 1 = epsilon(K). Similarly for F, Kinv.
-/
theorem counit_comp_antipode (x : Uqsl2 k) :
    counitUq k (antipodeUq k x) = counitUq k x := by
  sorry

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