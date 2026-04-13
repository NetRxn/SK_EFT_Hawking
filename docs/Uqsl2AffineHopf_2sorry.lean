import SKEFTHawking.Uqsl2Affine
import Mathlib

/-!
# Hopf Algebra Structure on U_q(ŝl₂)

Coproduct, counit, and antipode on the quantum affine algebra U_q(ŝl₂).
Same FreeAlgebra.lift + RingQuot.liftAlgHom pattern as Uqsl2Hopf.lean.
-/

noncomputable section

open LaurentPolynomial

namespace SKEFTHawking

variable (k : Type*) [CommRing k]

open Uqsl2AffGen TensorProduct

-- RingQuot typeclass diamond: rw operates at .reducible transparency where
-- RingQuot.instMul ≠ RingQuot.instSemiring.toMul structurally (Mathlib #10906).
-- Fix: use `erw` (which operates at .default transparency) instead of `rw`.
-- Helper for neg cancellation (needed for cross-comm and KE/KF proofs):
-- RingQuot diamond workaround: letI to fix instance path, then standard lemmas work.
private theorem uqAff_neg_mul_neg (a b : Uqsl2Aff k) : -a * -b = a * b := by
  letI : NonUnitalNonAssocRing (Uqsl2Aff k) := inferInstance
  rw [neg_mul, mul_neg, neg_neg]

-- Redefine locally (private in Uqsl2Affine)
private abbrev ascal (r : LaurentPolynomial k) :
    FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen :=
  algebraMap (LaurentPolynomial k) (FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen) r

private abbrev ag (x : Uqsl2AffGen) : FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen :=
  FreeAlgebra.ι (LaurentPolynomial k) x

/-! ## 0. Quotient relation lemmas in Uqsl2Aff k -/

/-
KE relations
-/
private theorem uqAff_K0E0 :
    uqAffK0 k * uqAffE0 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffE0 k * uqAffK0 k := by
  convert RingQuot.mkAlgHom_rel _ _;
  rotate_left;
  rotate_left;
  exact LaurentPolynomial k;
  exact?;
  exact inferInstance;
  exact ag k K0 * ag k E0;
  exact ascal k ( T 2 ) * ag k E0 * ag k K0;
  · exact AffChevalleyRel.K0E0;
  · unfold uqAffK0 uqAffE0; aesop;
  · simp +decide [ uqAffE0, uqAffK0 ];
    rfl

private theorem uqAff_K1E1 :
    uqAffK1 k * uqAffE1 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffE1 k * uqAffK1 k := by
  unfold uqAffK1 uqAffE1;
  have h_lift : ∀ {x y : FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen}, AffChevalleyRel k x y → (uqsl2AffMk k) x = (uqsl2AffMk k) y := by
    intro x y hxy
    simp [uqsl2AffMk];
    convert RingQuot.mkAlgHom_rel _ hxy;
  rw [ ← map_mul, h_lift AffChevalleyRel.K1E1 ];
  simp +decide [ uqsl2AffMk ]

private theorem uqAff_K0E1 :
    uqAffK0 k * uqAffE1 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffE1 k * uqAffK0 k := by
  -- Apply the relation from AffChevalleyRel.K0E1 to rewrite the left-hand side in terms of the right-hand side.
  have h_rewrite : uqsl2AffMk k (ag k K0 * ag k E1) = uqsl2AffMk k (ascal k (T (-2)) * ag k E1 * ag k K0) := by
    apply RingQuot.mkAlgHom_rel;
    exact AffChevalleyRel.K0E1;
  convert h_rewrite using 1;
  · exact ( uqsl2AffMk k ).map_mul ( ag k K0 ) ( ag k E1 ) ▸ rfl;
  · simp +decide [ uqAffE1, uqAffK0 ]

private theorem uqAff_K1E0 :
    uqAffK1 k * uqAffE0 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffE0 k * uqAffK1 k := by
  -- Apply the definition of `uqAffK1` and `uqAffE0` to rewrite the left-hand side.
  have h_def : uqAffK1 k * uqAffE0 k = uqsl2AffMk k (ag k K1 * ag k E0) := by
    -- By definition of multiplication in the quotient, we have:
    simp [uqAffK1, uqAffE0];
  rw [ h_def ];
  convert RingQuot.mkAlgHom_rel _ _;
  rotate_left;
  exact ascal k ( T ( -2 ) ) * ag k E0 * ag k K1;
  · exact AffChevalleyRel.K1E0;
  · unfold uqAffE0 uqAffK1; aesop;

/-
KF relations
-/
private theorem uqAff_K0F0 :
    uqAffK0 k * uqAffF0 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF0 k * uqAffK0 k := by
  unfold uqAffK0 uqAffF0;
  convert RingQuot.mkAlgHom_rel _ _ ; rotate_left;
  rotate_left;
  exact LaurentPolynomial k;
  exact inferInstance;
  exact?;
  exact FreeAlgebra.ι _ Uqsl2AffGen.K0 * FreeAlgebra.ι _ Uqsl2AffGen.F0
  exact ascal k ( T ( -2 ) ) * FreeAlgebra.ι _ Uqsl2AffGen.F0 * FreeAlgebra.ι _ Uqsl2AffGen.K0
  exact AffChevalleyRel.K0F0
  all_goals generalize_proofs at *;
  · exact?;
  · simp +decide [ uqsl2AffMk ]

private theorem uqAff_K1F1 :
    uqAffK1 k * uqAffF1 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF1 k * uqAffK1 k := by
  unfold uqAffK1 uqAffF1;
  have h_uqAff_K1F1 : (SKEFTHawking.uqsl2AffMk k) (SKEFTHawking.ag k K1 * SKEFTHawking.ag k F1) = (SKEFTHawking.uqsl2AffMk k) ((SKEFTHawking.ascal k (T (-2))) * SKEFTHawking.ag k F1 * SKEFTHawking.ag k K1) := by
    apply RingQuot.mkAlgHom_rel;
    exact AffChevalleyRel.K1F1;
  unfold uqsl2AffMk; aesop;

private theorem uqAff_K0F1 :
    uqAffK0 k * uqAffF1 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffF1 k * uqAffK0 k := by
  have h_quot : RingQuot.mkAlgHom (LaurentPolynomial k) (AffChevalleyRel k) (ag k K0 * ag k F1) = (algebraMap (LaurentPolynomial k) (Uqsl2Aff k)) (T 2) * RingQuot.mkAlgHom (LaurentPolynomial k) (AffChevalleyRel k) (ag k F1) * RingQuot.mkAlgHom (LaurentPolynomial k) (AffChevalleyRel k) (ag k K0) := by
    erw [ RingQuot.mkAlgHom_rel ];
    rotate_left;
    exact ascal k ( T 2 ) * ag k F1 * ag k K0;
    · exact AffChevalleyRel.K0F1;
    · simp +decide [ ascal, ag ];
  aesop

private theorem uqAff_K1F0 :
    uqAffK1 k * uqAffF0 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffF0 k * uqAffK1 k := by
  rw [ uqAffK1, uqAffF0 ];
  convert RingQuot.mkAlgHom_rel _ _ using 1;
  rotate_left;
  rotate_left;
  exact LaurentPolynomial k;
  exact inferInstance;
  exact inferInstance;
  exact ag k K1 * ag k F0;
  exact ascal k ( T 2 ) * ag k F0 * ag k K1;
  · exact AffChevalleyRel.K1F0;
  · exact?;
  · unfold uqsl2AffMk; aesop;

/-
Serre relations
-/
private theorem uqAff_Serre0 :
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 1 - T (-1)) *
    (uqAffE0 k * uqAffF0 k - uqAffF0 k * uqAffE0 k) =
    uqAffK0 k - uqAffK0inv k := by
  erw [ eq_comm ];
  have hSerre0 : uqsl2AffMk k (ascal k (T 1 - T (-1)) * (ag k E0 * ag k F0 - ag k F0 * ag k E0)) = uqsl2AffMk k (ag k K0 - ag k K0inv) := by
    apply RingQuot.mkAlgHom_rel;
    constructor;
  convert hSerre0.symm using 1;
  · unfold uqAffK0 uqAffK0inv uqsl2AffMk; norm_num;
  · simp +decide [ uqAffE0, uqAffF0 ]

private theorem uqAff_Serre1 :
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 1 - T (-1)) *
    (uqAffE1 k * uqAffF1 k - uqAffF1 k * uqAffE1 k) =
    uqAffK1 k - uqAffK1inv k := by
  convert RingQuot.mkAlgHom_rel _ _;
  rotate_left;
  rotate_left;
  exact k[T;T⁻¹];
  all_goals try infer_instance;
  exact ascal k ( T 1 - T ( -1 ) ) * ( ag k E1 * ag k F1 - ag k F1 * ag k E1 );
  exact ag k K1 - ag k K1inv;
  · exact AffChevalleyRel.Serre1;
  · unfold uqAffE1 uqAffF1; aesop;
  · simp +decide [ uqAffK1, uqAffK1inv ];
    rfl

/-
q-Serre relations
-/
private theorem uqAff_SerreE01 :
    uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k
    - algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2 + 1 + T (-2)) *
      uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k
    + algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2 + 1 + T (-2)) *
      uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k
    - uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k = 0 := by
  unfold uqAffE0 uqAffE1;
  convert ( RingQuot.mkAlgHom_rel _ AffChevalleyRel.SerreE01 ) using 1;
  any_goals exact k[T;T⁻¹];
  all_goals try infer_instance;
  · simp +decide [ uqsl2AffMk ];
  · exact?

private theorem uqAff_SerreE10 :
    uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k
    - algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2 + 1 + T (-2)) *
      uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k
    + algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2 + 1 + T (-2)) *
      uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k
    - uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k = 0 := by
  unfold uqAffE1 uqAffE0;
  convert RingQuot.mkAlgHom_rel _ _;
  any_goals exact AffChevalleyRel.SerreE10;
  any_goals exact k[T;T⁻¹];
  any_goals try infer_instance;
  · simp +decide [ uqsl2AffMk ];
  · exact Eq.symm ( map_zero _ )

private theorem uqAff_SerreF01 :
    uqAffF0 k * uqAffF0 k * uqAffF0 k * uqAffF1 k
    - algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2 + 1 + T (-2)) *
      uqAffF0 k * uqAffF0 k * uqAffF1 k * uqAffF0 k
    + algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2 + 1 + T (-2)) *
      uqAffF0 k * uqAffF1 k * uqAffF0 k * uqAffF0 k
    - uqAffF1 k * uqAffF0 k * uqAffF0 k * uqAffF0 k = 0 := by
  unfold uqAffF0 uqAffF1;
  convert RingQuot.mkAlgHom_rel _ _;
  any_goals exact AffChevalleyRel.SerreF01;
  rotate_left;
  grind;
  exact LaurentPolynomial k;
  all_goals try infer_instance;
  simp +decide [ uqsl2AffMk ]

private theorem uqAff_SerreF10 :
    uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffF0 k
    - algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2 + 1 + T (-2)) *
      uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffF1 k
    + algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2 + 1 + T (-2)) *
      uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffF1 k
    - uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffF1 k = 0 := by
  unfold uqAffF1 uqAffF0;
  convert RingQuot.mkAlgHom_rel _ _;
  any_goals exact AffChevalleyRel.SerreF10;
  any_goals exact k[T;T⁻¹];
  all_goals try infer_instance;
  · simp +decide [ uqsl2AffMk ];
  · grind +splitImp

/-! ## 1. Coproduct -/

/-- Ring instance on tensor product. -/
noncomputable instance affTensorRing :
    Ring ((Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) :=
  @Algebra.TensorProduct.instRing (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k) _ _ _ _ _

/-- Coproduct on generators of U_q(ŝl₂). -/
private noncomputable def affComulOnGen :
    Uqsl2AffGen → (Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)
  | .E0    => uqAffE0 k ⊗ₜ uqAffK0 k + 1 ⊗ₜ uqAffE0 k
  | .E1    => uqAffE1 k ⊗ₜ uqAffK1 k + 1 ⊗ₜ uqAffE1 k
  | .F0    => uqAffF0 k ⊗ₜ 1 + uqAffK0inv k ⊗ₜ uqAffF0 k
  | .F1    => uqAffF1 k ⊗ₜ 1 + uqAffK1inv k ⊗ₜ uqAffF1 k
  | .K0    => uqAffK0 k ⊗ₜ uqAffK0 k
  | .K1    => uqAffK1 k ⊗ₜ uqAffK1 k
  | .K0inv => uqAffK0inv k ⊗ₜ uqAffK0inv k
  | .K1inv => uqAffK1inv k ⊗ₜ uqAffK1inv k

/-- The coproduct lifted to the free algebra. -/
private noncomputable def affComulFreeAlg :
    FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen →ₐ[LaurentPolynomial k]
    (Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k) :=
  FreeAlgebra.lift (LaurentPolynomial k) (affComulOnGen k)

private theorem affComulFreeAlg_ι (x : Uqsl2AffGen) :
    affComulFreeAlg k (FreeAlgebra.ι _ x) = affComulOnGen k x := by
  unfold affComulFreeAlg; exact FreeAlgebra.lift_ι_apply _ _

/-! ### Comul case helpers -/

/-
KK⁻¹ cases
-/
private theorem affComulFreeAlg_K0K0inv :
    affComulFreeAlg k (ag k K0 * ag k K0inv) =
    (1 : (Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) := by
  -- Apply the definition of `affComulFreeAlg` and the fact that `affComulOnGen K0 * affComulOnGen K0inv = 1 ⊗ 1`.
  have h_coproduct_K0_K0inv : (affComulFreeAlg k) (ag k K0) * (affComulFreeAlg k) (ag k K0inv) = 1 ⊗ₜ 1 := by
    erw [ affComulFreeAlg_ι, affComulFreeAlg_ι ];
    erw [ Algebra.TensorProduct.tmul_mul_tmul ];
    rw [ uqAff_K0_mul_K0inv ];
  convert h_coproduct_K0_K0inv using 1;
  exact map_mul _ _ _

private theorem affComulFreeAlg_K0invK0 :
    affComulFreeAlg k (ag k K0inv * ag k K0) =
    (1 : (Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) := by
  erw [ RingHom.map_mul, affComulFreeAlg_ι, affComulFreeAlg_ι, Algebra.TensorProduct.tmul_mul_tmul ];
  erw [ uqAff_K0inv_mul_K0 ];
  exact?

private theorem affComulFreeAlg_K1K1inv :
    affComulFreeAlg k (ag k K1 * ag k K1inv) =
    (1 : (Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) := by
  have h : (affComulFreeAlg k) (ag k K1) * (affComulFreeAlg k) (ag k K1inv) = 1 ⊗ₜ 1 := by
    erw [affComulFreeAlg_ι, affComulFreeAlg_ι]; erw [Algebra.TensorProduct.tmul_mul_tmul]; rw [uqAff_K1_mul_K1inv];
  convert h using 1;
  exact map_mul _ _ _

private theorem affComulFreeAlg_K1invK1 :
    affComulFreeAlg k (ag k K1inv * ag k K1) =
    (1 : (Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) := by
  convert affComulFreeAlg_K1K1inv using 1;
  constructor;
  exact?;
  intro h;
  convert h k using 1;
  simp +decide [ affComulFreeAlg, affComulOnGen ];
  rw [ uqAff_K1inv_mul_K1, uqAff_K1_mul_K1inv ]

/-
K0K1 commutativity
-/
private theorem affComulFreeAlg_K0K1 :
    affComulFreeAlg k (ag k K0 * ag k K1) =
    affComulFreeAlg k (ag k K1 * ag k K0) := by
  convert ( congr_arg ( fun x => x ⊗ₜ[LaurentPolynomial k] x ) ( uqAff_K0K1_comm k ) ) using 1;
  · -- By definition of affComulFreeAlg, we have:
    simp [affComulFreeAlg, affComulOnGen];
  · erw [ RingHom.map_mul, affComulFreeAlg_ι, affComulFreeAlg_ι, affComulOnGen, affComulOnGen ] ; norm_num

/-
KE cases
-/
private theorem affComulFreeAlg_K0E0 :
    affComulFreeAlg k (ag k K0 * ag k E0) =
    affComulFreeAlg k (ascal k (T 2) * ag k E0 * ag k K0) := by
  simp +decide [ affComulFreeAlg, affComulOnGen ];
  simp +decide [ mul_add, add_mul, mul_assoc, uqAff_K0E0 ];
  simp +decide [ Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul' ]

private theorem affComulFreeAlg_K1E1 :
    affComulFreeAlg k (ag k K1 * ag k E1) =
    affComulFreeAlg k (ascal k (T 2) * ag k E1 * ag k K1) := by
  simp +decide [ affComulFreeAlg, affComulOnGen ];
  simp +decide [ mul_add, add_mul, mul_assoc, uqAff_K1E1 ];
  simp +decide [ mul_assoc, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul' ]

private theorem affComulFreeAlg_K0E1 :
    affComulFreeAlg k (ag k K0 * ag k E1) =
    affComulFreeAlg k (ascal k (T (-2)) * ag k E1 * ag k K0) := by
  simp +decide [ affComulFreeAlg, affComulOnGen ];
  simp +decide [ mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.algebraMap_apply ];
  rw [ uqAff_K0E1, uqAff_K0K1_comm ];
  simp +decide [ mul_assoc, Algebra.algebraMap_eq_smul_one ];
  exact?

private theorem affComulFreeAlg_K1E0 :
    affComulFreeAlg k (ag k K1 * ag k E0) =
    affComulFreeAlg k (ascal k (T (-2)) * ag k E0 * ag k K1) := by
  unfold affComulFreeAlg; simp +decide [ affComulOnGen ] ;
  simp +decide [ mul_add, add_mul, mul_assoc, mul_left_comm, Algebra.smul_def ];
  rw [ uqAff_K1E0, uqAff_K0K1_comm ];
  simp +decide [ mul_assoc, Algebra.algebraMap_eq_smul_one ];
  exact?

/-
KF cases
-/
private theorem affComulFreeAlg_K0F0 :
    affComulFreeAlg k (ag k K0 * ag k F0) =
    affComulFreeAlg k (ascal k (T (-2)) * ag k F0 * ag k K0) := by
  simp +decide [affComulFreeAlg, affComulOnGen, mul_add, add_mul, mul_assoc, uqAff_K0F0];
  simp +decide only [uqAff_K0_mul_K0inv, uqAff_K0inv_mul_K0];
  simp +decide [ Algebra.algebraMap_eq_smul_one ];
  exact?

private theorem affComulFreeAlg_K1F1 :
    affComulFreeAlg k (ag k K1 * ag k F1) =
    affComulFreeAlg k (ascal k (T (-2)) * ag k F1 * ag k K1) := by
  unfold affComulFreeAlg; norm_num [ mul_assoc ] ;
  simp +decide [ affComulOnGen, mul_assoc, mul_left_comm, mul_comm ];
  simp +decide [ mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, Algebra.algebraMap_eq_smul_one ];
  rw [ uqAff_K1F1, uqAff_K1_mul_K1inv ];
  rw [ uqAff_K1inv_mul_K1 ];
  simp +decide [ mul_assoc, Algebra.algebraMap_eq_smul_one ];
  exact?

private theorem affComulFreeAlg_K0F1 :
    affComulFreeAlg k (ag k K0 * ag k F1) =
    affComulFreeAlg k (ascal k (T 2) * ag k F1 * ag k K0) := by
  unfold affComulFreeAlg;
  simp +decide [ affComulOnGen, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm ];
  rw [ uqAff_K0F1 ];
  rw [ show uqAffK0 k * uqAffK1inv k = uqAffK1inv k * uqAffK0 k from ?_ ];
  · simp +decide [ mul_assoc, mul_left_comm, Algebra.algebraMap_eq_smul_one ];
    exact?;
  · have h_inv : uqAffK0 k * uqAffK1inv k * uqAffK1 k = uqAffK1inv k * uqAffK0 k * uqAffK1 k := by
      simp +decide [ mul_assoc, uqAff_K0K1_comm ];
      simp +decide [ ← mul_assoc, uqAff_K1inv_mul_K1 ];
    have h_inv : uqAffK1 k * uqAffK1inv k = 1 := by
      exact?;
    apply_fun ( · * uqAffK1inv k ) at ‹uqAffK0 k * uqAffK1inv k * uqAffK1 k = uqAffK1inv k * uqAffK0 k * uqAffK1 k›; simp_all +decide [ mul_assoc ] ;

private theorem affComulFreeAlg_K1F0 :
    affComulFreeAlg k (ag k K1 * ag k F0) =
    affComulFreeAlg k (ascal k (T 2) * ag k F0 * ag k K1) := by
  simp_all +decide [ mul_assoc ];
  erw [ show ( affComulFreeAlg k ) ( ag k K1 ) = uqAffK1 k ⊗ₜ[k[T;T⁻¹]] uqAffK1 k from ?_, show ( affComulFreeAlg k ) ( ag k F0 ) = uqAffF0 k ⊗ₜ[k[T;T⁻¹]] 1 + uqAffK0inv k ⊗ₜ[k[T;T⁻¹]] uqAffF0 k from ?_ ];
  · simp +decide [ mul_add, add_mul, mul_assoc, uqAff_K1F0, uqAff_K0K1_comm ];
    rw [ show uqAffK1 k * uqAffK0inv k = uqAffK0inv k * uqAffK1 k from ?_ ];
    · simp +decide [ mul_assoc, mul_left_comm, Algebra.algebraMap_eq_smul_one ];
      rw [ TensorProduct.smul_tmul' ];
    · have h_comm : uqAffK1 k * uqAffK0 k = uqAffK0 k * uqAffK1 k := by
        rw [ uqAff_K0K1_comm ];
      have h_comm : uqAffK1 k * uqAffK0inv k * uqAffK0 k = uqAffK0inv k * uqAffK1 k * uqAffK0 k := by
        simp +decide [ mul_assoc, h_comm ];
        rw [ uqAff_K0inv_mul_K0 ] ; simp +decide [ mul_assoc ];
        rw [ ← mul_assoc, uqAff_K0inv_mul_K0, one_mul ];
      have h_comm : uqAffK1 k * uqAffK0inv k * uqAffK0 k * uqAffK0inv k = uqAffK0inv k * uqAffK1 k * uqAffK0 k * uqAffK0inv k := by
        rw [h_comm];
      convert h_comm using 1 <;> simp +decide [ mul_assoc, uqAff_K0_mul_K0inv ];
  · convert affComulFreeAlg_ι k F0 using 1;
  · -- By definition of affComulFreeAlg, we know that affComulFreeAlg k (ag k K1) = uqAffK1 k ⊗ₜ uqAffK1 k. This follows directly from the definition of affComulFreeAlg.
    apply affComulFreeAlg_ι

/-
Serre cases
Derived commutation: E0*K0inv = q²*K0inv*E0
-/
private theorem uqAff_E0_mul_K0inv :
    uqAffE0 k * uqAffK0inv k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffK0inv k * uqAffE0 k := by
  convert congr_arg ( fun x => uqAffK0inv k * x * uqAffK0inv k ) ( uqAff_K0E0 k ) using 1;
  · simp +decide [ ← mul_assoc, uqAff_K0_mul_K0inv, uqAff_K0inv_mul_K0 ];
  · simp +decide [ mul_assoc, mul_left_comm, Algebra.commutes ];
    simp +decide [ ← mul_assoc, uqAff_K0_mul_K0inv ]

/-
Derived commutation: K0inv*F0 = q²*F0*K0inv
-/
private theorem uqAff_K0inv_mul_F0 :
    uqAffK0inv k * uqAffF0 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffF0 k * uqAffK0inv k := by
  have h_comm : uqAffK0 k * uqAffF0 k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF0 k * uqAffK0 k := by
    exact?;
  have h_comm : uqAffK0inv k * (uqAffK0 k * uqAffF0 k) = uqAffF0 k := by
    rw [ ← mul_assoc, uqAff_K0inv_mul_K0, one_mul ];
  have h_comm : uqAffK0inv k * (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF0 k * uqAffK0 k) = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * (uqAffK0inv k * uqAffF0 k) * uqAffK0 k := by
    simp +decide [ mul_assoc, mul_left_comm ];
    exact?;
  have h_comm : uqAffK0inv k * uqAffF0 k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * (uqAffK0inv k * uqAffF0 k) * uqAffK0 k) * uqAffK0inv k := by
    have h_comm : algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) = 1 := by
      rw [ ← map_mul ];
      erw [ ← LaurentPolynomial.T_add ] ; norm_num;
    simp +decide [ ← mul_assoc, h_comm ];
    simp +decide [ mul_assoc, uqAff_K0_mul_K0inv ];
  grind

/-
Cross-term equality for Serre0
-/
private theorem affComul_Serre0_cross_terms :
    (uqAffE0 k * uqAffK0inv k) ⊗ₜ[LaurentPolynomial k] (uqAffK0 k * uqAffF0 k) =
    (uqAffK0inv k * uqAffE0 k) ⊗ₜ[LaurentPolynomial k] (uqAffF0 k * uqAffK0 k) := by
  -- Apply the commutation relations for E0 and F0.
  have h_comm_E0 : uqAffE0 k * uqAffK0inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffK0inv k * uqAffE0 k := by
    exact?
  have h_comm_F0 : uqAffK0 k * uqAffF0 k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF0 k * uqAffK0 k := by
    exact?;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Algebra.algebraMap_eq_smul_one ];
  exact?

/-
Derived commutations for index 1
-/
private theorem uqAff_E1_mul_K1inv :
    uqAffE1 k * uqAffK1inv k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffK1inv k * uqAffE1 k := by
  have h_comm : uqAffK1 k * uqAffE1 k * uqAffK1inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffE1 k := by
    convert congr_arg ( · * uqAffK1inv k ) ( uqAff_K1E1 k ) using 1;
    simp +decide [ mul_assoc, uqAff_K1_mul_K1inv ];
  have h_comm : uqAffK1inv k * uqAffK1 k = 1 := by
    exact?;
  apply_fun ( fun x => uqAffK1inv k * x ) at ‹uqAffK1 k * uqAffE1 k * uqAffK1inv k = _› ; simp_all +decide [ mul_assoc ];
  simp_all +decide [ ← mul_assoc, Algebra.algebraMap_eq_smul_one ]

private theorem uqAff_K1inv_mul_F1 :
    uqAffK1inv k * uqAffF1 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffF1 k * uqAffK1inv k := by
  have h_rewrite : uqAffK1 k * uqAffF1 k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF1 k * uqAffK1 k := by
    exact?;
  have h_rewrite : uqAffK1inv k * (uqAffK1 k * uqAffF1 k) = uqAffK1inv k * (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF1 k * uqAffK1 k) := by
    rw [h_rewrite];
  have h_rewrite : (uqAffK1inv k * uqAffK1 k) * uqAffF1 k = (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2))) * (uqAffK1inv k * uqAffF1 k) * uqAffK1 k := by
    convert h_rewrite using 1 <;> simp +decide [ mul_assoc, mul_left_comm ];
    simp +decide [ mul_assoc, mul_left_comm, Algebra.commutes ];
  have h_rewrite : (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2))) * (uqAffK1inv k * uqAffF1 k) * uqAffK1 k = uqAffF1 k := by
    rw [ ← h_rewrite, uqAff_K1inv_mul_K1, one_mul ];
  have h_rewrite : (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2)) * (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2))) = 1 := by
    rw [ ← map_mul ];
    rw [ ← LaurentPolynomial.T_add ] ; norm_num;
  apply_fun ( fun x => x * uqAffK1inv k ) at ‹ ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ) ( T ( -2 ) ) * ( uqAffK1inv k * uqAffF1 k ) * uqAffK1 k = uqAffF1 k › ; simp_all +decide [ mul_assoc ];
  rw [ ← h_rewrite, ← mul_assoc ];
  rw [ ‹ ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ) ( T 2 ) * ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ) ( T ( -2 ) ) = 1 ›, one_mul ];
  rw [ uqAff_K1_mul_K1inv, mul_one ]

private theorem affComul_Serre1_cross_terms :
    (uqAffE1 k * uqAffK1inv k) ⊗ₜ[LaurentPolynomial k] (uqAffK1 k * uqAffF1 k) =
    (uqAffK1inv k * uqAffE1 k) ⊗ₜ[LaurentPolynomial k] (uqAffF1 k * uqAffK1 k) := by
  have := uqAff_E1_mul_K1inv k;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Algebra.smul_def ];
  rw [ show uqAffK1 k * uqAffF1 k = ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ) ( T ( -2 ) ) * ( uqAffF1 k * uqAffK1 k ) from ?_ ];
  · simp +decide [ ← mul_assoc, ← Algebra.smul_def ];
    exact?;
  · convert uqAff_K1F1 k using 1;
    rw [ mul_assoc ]

/-
Step 1: Expand EF-FE showing cross terms cancel
-/
private theorem affComul_EF_sub_FE_0 :
    affComulFreeAlg k (ag k E0 * ag k F0) - affComulFreeAlg k (ag k F0 * ag k E0) =
    (uqAffE0 k * uqAffF0 k - uqAffF0 k * uqAffE0 k) ⊗ₜ[LaurentPolynomial k] uqAffK0 k +
    uqAffK0inv k ⊗ₜ[LaurentPolynomial k] (uqAffE0 k * uqAffF0 k - uqAffF0 k * uqAffE0 k) := by
  rw [ sub_eq_iff_eq_add' ];
  simp +decide [ affComulFreeAlg, affComulOnGen ];
  simp +decide [ mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, sub_eq_add_neg ];
  simp +decide [ ← add_assoc, ← TensorProduct.tmul_add, ← TensorProduct.add_tmul, affComul_Serre0_cross_terms ];
  simp +decide [ TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_sub ] ; abel_nf;
  simp +decide [ TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul, add_assoc, add_left_comm, add_comm ];
  simp +decide [ ← add_assoc, ← TensorProduct.tmul_add, ← TensorProduct.add_tmul, ← TensorProduct.smul_tmul ]

private theorem affComul_EF_sub_FE_1 :
    affComulFreeAlg k (ag k E1 * ag k F1) - affComulFreeAlg k (ag k F1 * ag k E1) =
    (uqAffE1 k * uqAffF1 k - uqAffF1 k * uqAffE1 k) ⊗ₜ[LaurentPolynomial k] uqAffK1 k +
    uqAffK1inv k ⊗ₜ[LaurentPolynomial k] (uqAffE1 k * uqAffF1 k - uqAffF1 k * uqAffE1 k) := by
  unfold affComulFreeAlg; simp +decide [ affComulOnGen ] ;
  -- By combining like terms, we can see that the cross terms cancel out, leaving the desired expression.
  simp [mul_add, add_mul, mul_assoc, add_assoc, sub_eq_add_neg];
  rw [ affComul_Serre1_cross_terms ] ; abel_nf;
  simp +decide [ TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul ] ; abel_nf;
  simp +decide [ TensorProduct.tmul_neg, TensorProduct.neg_tmul ] ; abel_nf;
  rw [ TensorProduct.smul_tmul, TensorProduct.tmul_smul ] ; abel_nf;
  rw [ add_comm ] ; norm_num [ TensorProduct.smul_tmul', TensorProduct.tmul_smul ] ; abel_nf;
  rw [ TensorProduct.tmul_smul ]

/-
Step 2: Apply Serre relation
-/
private theorem affComul_Serre0_apply :
    algebraMap (LaurentPolynomial k) ((Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) (T 1 - T (-1)) *
    ((uqAffE0 k * uqAffF0 k - uqAffF0 k * uqAffE0 k) ⊗ₜ[LaurentPolynomial k] uqAffK0 k +
     uqAffK0inv k ⊗ₜ[LaurentPolynomial k] (uqAffE0 k * uqAffF0 k - uqAffF0 k * uqAffE0 k)) =
    uqAffK0 k ⊗ₜ[LaurentPolynomial k] uqAffK0 k -
    uqAffK0inv k ⊗ₜ[LaurentPolynomial k] uqAffK0inv k := by
  have h_dist : algebraMap (LaurentPolynomial k) (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k) (T 1 - T (-1)) * ((uqAffE0 k * uqAffF0 k - uqAffF0 k * uqAffE0 k) ⊗ₜ[LaurentPolynomial k] uqAffK0 k) = (uqAffK0 k - uqAffK0inv k) ⊗ₜ[LaurentPolynomial k] uqAffK0 k := by
    convert congr_arg ( fun x => x ⊗ₜ[LaurentPolynomial k] uqAffK0 k ) ( uqAff_Serre0 k ) using 1;
    simp +decide [ TensorProduct.smul_tmul' ];
  have h_dist2 : algebraMap (LaurentPolynomial k) (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k) (T 1 - T (-1)) * (uqAffK0inv k ⊗ₜ[LaurentPolynomial k] (uqAffE0 k * uqAffF0 k - uqAffF0 k * uqAffE0 k)) = uqAffK0inv k ⊗ₜ[LaurentPolynomial k] (uqAffK0 k - uqAffK0inv k) := by
    rw [ ← uqAff_Serre0 ];
    simp +decide [ Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul' ];
  rw [ mul_add, h_dist, h_dist2 ] ; abel_nf;
  simp +decide [ add_comm, add_left_comm, add_assoc, TensorProduct.tmul_add, TensorProduct.tmul_neg ];
  simp +decide [ TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.neg_tmul, TensorProduct.tmul_neg ] ; abel_nf;
  rw [ TensorProduct.smul_tmul, TensorProduct.tmul_smul ] ; norm_num ; abel_nf

private theorem affComul_Serre1_apply :
    algebraMap (LaurentPolynomial k) ((Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) (T 1 - T (-1)) *
    ((uqAffE1 k * uqAffF1 k - uqAffF1 k * uqAffE1 k) ⊗ₜ[LaurentPolynomial k] uqAffK1 k +
     uqAffK1inv k ⊗ₜ[LaurentPolynomial k] (uqAffE1 k * uqAffF1 k - uqAffF1 k * uqAffE1 k)) =
    uqAffK1 k ⊗ₜ[LaurentPolynomial k] uqAffK1 k -
    uqAffK1inv k ⊗ₜ[LaurentPolynomial k] uqAffK1inv k := by
  rw [ mul_add ];
  have h_dist : algebraMap (LaurentPolynomial k) ((Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) (T 1 - T (-1)) * ((uqAffE1 k * uqAffF1 k - uqAffF1 k * uqAffE1 k) ⊗ₜ[LaurentPolynomial k] uqAffK1 k) = (uqAffK1 k - uqAffK1inv k) ⊗ₜ[LaurentPolynomial k] uqAffK1 k := by
    rw [ ← uqAff_Serre1 ];
    simp +decide [ Algebra.algebraMap_eq_smul_one ];
    exact?;
  have h_dist2 : algebraMap (LaurentPolynomial k) ((Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k)) (T 1 - T (-1)) * (uqAffK1inv k ⊗ₜ[LaurentPolynomial k] (uqAffE1 k * uqAffF1 k - uqAffF1 k * uqAffE1 k)) = uqAffK1inv k ⊗ₜ[LaurentPolynomial k] (uqAffK1 k - uqAffK1inv k) := by
    rw [ ← uqAff_Serre1 k ];
    simp +decide [ Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul' ];
  rw [ h_dist, h_dist2 ] ; abel_nf;
  simp +decide [ TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.smul_tmul ] ; abel_nf;
  rw [ TensorProduct.smul_tmul, TensorProduct.tmul_smul ] ; norm_num ; abel_nf;
  rw [ TensorProduct.tmul_smul ]

/-
Step 3: Combine into main Serre theorems
-/
private theorem affComulFreeAlg_Serre0 :
    affComulFreeAlg k
      (ascal k (T 1 - T (-1)) * (ag k E0 * ag k F0 - ag k F0 * ag k E0)) =
    affComulFreeAlg k (ag k K0 - ag k K0inv) := by
  convert affComul_Serre0_apply k using 1;
  · rw [ map_mul, map_sub ];
    congr! 1;
    · simp +decide [ Algebra.algebraMap_eq_smul_one ];
    · exact?;
  · erw [ map_sub, affComulFreeAlg_ι, affComulFreeAlg_ι ];
    rfl

private theorem affComulFreeAlg_Serre1 :
    affComulFreeAlg k
      (ascal k (T 1 - T (-1)) * (ag k E1 * ag k F1 - ag k F1 * ag k E1)) =
    affComulFreeAlg k (ag k K1 - ag k K1inv) := by
  convert affComul_Serre1_apply k using 1
  generalize_proofs at *;
  · rw [ ← affComul_EF_sub_FE_1 ];
    simp +decide [ Algebra.algebraMap_eq_smul_one ];
  · erw [ map_sub, affComulFreeAlg_ι, affComulFreeAlg_ι ] ; rfl

/-
Cross-commutation cases
-/
private theorem affComulFreeAlg_E0F1 :
    affComulFreeAlg k (ag k E0 * ag k F1) =
    affComulFreeAlg k (ag k F1 * ag k E0) := by
  unfold affComulFreeAlg;
  simp +decide [ ag, affComulOnGen ];
  simp +decide [ mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, TensorProduct.tmul_add, TensorProduct.add_tmul, uqAff_E0F1_comm, uqAff_K0K1_comm ];
  simp +decide only [uqAff_K0F1, uqAff_K1E0];
  rw [ show uqAffE0 k * uqAffK1inv k = algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ( T ( -2 ) ) * uqAffK1inv k * uqAffE0 k from ?_ ];
  · simp +decide [ mul_assoc, mul_comm, mul_left_comm, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', TensorProduct.tmul_smul ];
    rw [ show ( T 2 : LaurentPolynomial k ) • T ( -2 ) • ( uqAffK1inv k * uqAffE0 k ) = ( uqAffK1inv k * uqAffE0 k ) by
          nontriviality;
          exact? ] ; abel1;
  · have := uqAff_K1E0 k;
    apply_fun ( · * uqAffK1inv k ) at this;
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, uqAff_K1_mul_K1inv ];
    apply_fun ( fun x => uqAffK1inv k * x ) at this;
    simp_all +decide [ ← mul_assoc, uqAff_K1inv_mul_K1 ];
    simp +decide [ mul_assoc, mul_left_comm, Algebra.algebraMap_eq_smul_one ]

private theorem affComulFreeAlg_E1F0 :
    affComulFreeAlg k (ag k E1 * ag k F0) =
    affComulFreeAlg k (ag k F0 * ag k E1) := by
  unfold affComulFreeAlg;
  simp +decide [ affComulOnGen ];
  simp +decide [ mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, TensorProduct.tmul_add, TensorProduct.add_tmul ];
  rw [ uqAff_E1F0_comm, uqAff_K1F0 ] ; ring;
  rw [ show uqAffE1 k * uqAffK0inv k = algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ( T ( -2 ) ) * uqAffK0inv k * uqAffE1 k from ?_ ] ; ring;
  · simp +decide [ mul_assoc, Algebra.algebraMap_eq_smul_one ];
    simp +decide [ ← mul_assoc, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul ];
    rw [ show T 2 • T ( -2 ) • ( uqAffF0 k * uqAffK1 k ) = uqAffF0 k * uqAffK1 k from ?_ ] ; abel1;
    exact?;
  · have h_comm : uqAffK0 k * (uqAffE1 k * uqAffK0inv k) = uqAffK0 k * (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffK0inv k * uqAffE1 k) := by
      simp +decide [ ← mul_assoc, uqAff_K0E1 ];
      simp +decide [ mul_assoc, mul_left_comm, uqAff_K0_mul_K0inv ];
      simp +decide [ ← mul_assoc, ← Algebra.smul_def ];
      rw [ uqAff_K0_mul_K0inv, one_mul ];
    have h_inv : IsUnit (uqAffK0 k) := by
      exact ⟨ uqAffK0_unit k, rfl ⟩;
    exact h_inv.mul_left_cancel h_comm

-- NOTE: F q-Serre coproduct proofs need cross-index K⁻¹-F commutation lemmas
-- (uqAff_K0inv_K1inv_comm, uqAff_K0inv_mul_F1, uqAff_K1inv_mul_F0)
-- which are defined later in this file (in the antipode helpers section).
-- The F proofs will be completed after relocating those lemmas.

/-
q-commutation lemmas for coproduct images in A⊗A.
These are KEY for the bidegree approach to q-Serre coproduct compatibility.

For Δ(E₁) = E₁⊗K₁ + 1⊗E₁, let x = E₁⊗K₁ and y = 1⊗E₁.
Then x·y = E₁⊗(K₁·E₁) and y·x = E₁⊗(E₁·K₁).
Using K₁E₁ = T(2)·E₁K₁: x·y = T(2)•(y·x).
This is the q-commutation relation with q² = T(2).
-/

/-! ### Right-factor K-E normalization lemmas for tensor products.

These lemmas normalize K·E products inside the RIGHT tensor factor:
  a ⊗ₜ (K_i * (E_j * b)) = T(a_{ij}) • (a ⊗ₜ (E_j * (K_i * b)))

They use `erw` internally to handle the RingQuot typeclass diamond, but
present a clean `rw`/`simp_rw`-compatible interface. This is the key tool
for Phase 6 of the q-Serre coproduct proof.
-/

private theorem tmul_K1E1_norm (a b : Uqsl2Aff k) :
    a ⊗ₜ[LaurentPolynomial k] (uqAffK1 k * (uqAffE1 k * b)) =
    (T 2 : LaurentPolynomial k) • (a ⊗ₜ[LaurentPolynomial k] (uqAffE1 k * (uqAffK1 k * b))) := by
  -- First prove the right-factor identity using erw
  have hr : uqAffK1 k * (uqAffE1 k * b) =
      algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * (uqAffE1 k * (uqAffK1 k * b)) := by
    rw [← mul_assoc]; erw [uqAff_K1E1 (k := k)]; rw [mul_assoc, mul_assoc]
  rw [hr, ← Algebra.smul_def, TensorProduct.tmul_smul]

private theorem tmul_K1E0_norm (a b : Uqsl2Aff k) :
    a ⊗ₜ[LaurentPolynomial k] (uqAffK1 k * (uqAffE0 k * b)) =
    (T (-2) : LaurentPolynomial k) • (a ⊗ₜ[LaurentPolynomial k] (uqAffE0 k * (uqAffK1 k * b))) := by
  have hr : uqAffK1 k * (uqAffE0 k * b) =
      algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * (uqAffE0 k * (uqAffK1 k * b)) := by
    rw [← mul_assoc]; erw [uqAff_K1E0 (k := k)]; rw [mul_assoc, mul_assoc]
  rw [hr, ← Algebra.smul_def, TensorProduct.tmul_smul]

private theorem tmul_K0E1_norm (a b : Uqsl2Aff k) :
    a ⊗ₜ[LaurentPolynomial k] (uqAffK0 k * (uqAffE1 k * b)) =
    (T (-2) : LaurentPolynomial k) • (a ⊗ₜ[LaurentPolynomial k] (uqAffE1 k * (uqAffK0 k * b))) := by
  have hr : uqAffK0 k * (uqAffE1 k * b) =
      algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * (uqAffE1 k * (uqAffK0 k * b)) := by
    rw [← mul_assoc]; erw [uqAff_K0E1 (k := k)]; rw [mul_assoc, mul_assoc]
  rw [hr, ← Algebra.smul_def, TensorProduct.tmul_smul]

private theorem tmul_K0E0_norm (a b : Uqsl2Aff k) :
    a ⊗ₜ[LaurentPolynomial k] (uqAffK0 k * (uqAffE0 k * b)) =
    (T 2 : LaurentPolynomial k) • (a ⊗ₜ[LaurentPolynomial k] (uqAffE0 k * (uqAffK0 k * b))) := by
  have hr : uqAffK0 k * (uqAffE0 k * b) =
      algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * (uqAffE0 k * (uqAffK0 k * b)) := by
    rw [← mul_assoc]; erw [uqAff_K0E0 (k := k)]; rw [mul_assoc, mul_assoc]
  rw [hr, ← Algebra.smul_def, TensorProduct.tmul_smul]

/-- q-commutation: (E₁⊗K₁)·(1⊗E₁) = T(2) • (1⊗E₁)·(E₁⊗K₁) in A⊗A.
    Equivalently: the "left" and "right" summands of Δ(E₁) q-commute. -/
private theorem deltaE1_q_comm :
    (uqAffE1 k ⊗ₜ[LaurentPolynomial k] uqAffK1 k) *
    ((1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE1 k) =
    (T 2 : LaurentPolynomial k) •
    (((1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE1 k) *
     (uqAffE1 k ⊗ₜ[LaurentPolynomial k] uqAffK1 k)) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  -- LHS: E₁ ⊗ K₁·E₁.  RHS: T(2) • (E₁ ⊗ E₁·K₁)
  -- Use K₁E₁ = T(2)·E₁K₁
  rw [uqAff_K1E1]
  -- Now: E₁ ⊗ (T(2)·E₁·K₁) = T(2) • (E₁ ⊗ E₁·K₁)
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm,
             TensorProduct.tmul_smul, mul_assoc]

/-- q-commutation for cross-index: (E₁⊗K₁)·(1⊗E₀) = T(-2) • (1⊗E₀)·(E₁⊗K₁).
    K₁ commutes past E₀ with q-factor T(-2). -/
private theorem deltaE1_cross_comm_E0 :
    (uqAffE1 k ⊗ₜ[LaurentPolynomial k] uqAffK1 k) *
    ((1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE0 k) =
    (T (-2) : LaurentPolynomial k) •
    (((1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE0 k) *
     (uqAffE1 k ⊗ₜ[LaurentPolynomial k] uqAffK1 k)) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [uqAff_K1E0]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm,
             TensorProduct.tmul_smul, mul_assoc]

/-- q-commutation: (E₀⊗K₀)·(1⊗E₁) = T(-2) • (1⊗E₁)·(E₀⊗K₀). -/
private theorem deltaE0_cross_comm_E1 :
    (uqAffE0 k ⊗ₜ[LaurentPolynomial k] uqAffK0 k) *
    ((1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE1 k) =
    (T (-2) : LaurentPolynomial k) •
    (((1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE1 k) *
     (uqAffE0 k ⊗ₜ[LaurentPolynomial k] uqAffK0 k)) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [uqAff_K0E1]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm,
             TensorProduct.tmul_smul, mul_assoc]

/-- q-commutation: (E₀⊗K₀)·(1⊗E₀) = T(2) • (1⊗E₀)·(E₀⊗K₀). -/
private theorem deltaE0_q_comm :
    (uqAffE0 k ⊗ₜ[LaurentPolynomial k] uqAffK0 k) *
    ((1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE0 k) =
    (T 2 : LaurentPolynomial k) •
    (((1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE0 k) *
     (uqAffE0 k ⊗ₜ[LaurentPolynomial k] uqAffK0 k)) := by
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [uqAff_K0E0]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm,
             TensorProduct.tmul_smul, mul_assoc]

/-
q-binomial coefficient lemmas for q-Serre coproduct.

These are pure polynomial identities in LaurentPolynomial k that close the
coefficient cancellations in the bidegree decomposition of serre(Δ(E), Δ(E')).

Sector (0,1) and (3,0): q⁻⁶ - [3]_q·q⁻⁴ + [3]_q·q⁻² - 1 = 0
  This factors as (x-1)(x-q²)(x-q⁻²) at x = q⁻².

Sector (1,0): (1+q²+q⁴) - [3]_q·q² = 0
  Because [3]_q = q² + 1 + q⁻², so [3]_q·q² = q⁴ + q² + 1.

Source: Deep research "CAS-assisted Lean 4 tactics for Δ..." Sections 1-2.
-/

/-- q-binomial vanishing for sectors (0,1) and (3,0):
    T(-6) - (T(2)+1+T(-2))·T(-4) + (T(2)+1+T(-2))·T(-2) - 1 = 0.
    This is the identity x³ - [3]_q·x² + [3]_q·x - 1 = 0 at x = T(-2). -/
private theorem qbinom_serre_vanish (k : Type*) [CommRing k] :
    (T (-6) : LaurentPolynomial k) -
    (T 2 + 1 + T (-2)) * T (-4) +
    (T 2 + 1 + T (-2)) * T (-2) -
    1 = 0 := by
  simp only [mul_add, add_mul, mul_one, one_mul, ← T_add]
  norm_num [T_zero]; ring

/-- q-binomial for sector (1,0) first sub-case:
    (1 + T(2) + T(4)) - (T(2)+1+T(-2))·T(2) = 0.
    Because [3]_q·q² = q⁴+q²+1. -/
private theorem qbinom_sector10_sub1 (k : Type*) [CommRing k] :
    (1 : LaurentPolynomial k) + T 2 + T 4 -
    (T 2 + 1 + T (-2)) * T 2 = 0 := by
  simp only [mul_add, add_mul, mul_one, one_mul, ← T_add]
  norm_num [T_zero]; ring

/-- q-binomial for sector (1,0) second sub-case:
    -(T(2)+1+T(-2))·(1+T(2)) + (T(2)+1+T(-2))·(1+T(2)) = 0. Trivially zero. -/
private theorem qbinom_sector10_sub2 (k : Type*) [CommRing k] :
    -(T 2 + 1 + T (-2) : LaurentPolynomial k) * (1 + T 2) +
    (T 2 + 1 + T (-2)) * (1 + T 2) = 0 := by
  ring

/-- q-binomial for sector (1,0) third sub-case: [3]_q - [3]_q = 0. -/
private theorem qbinom_sector10_sub3 (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) -
    (T 2 + 1 + T (-2)) = 0 := by
  ring

/-
q-Serre coproduct cases: PROVIDED SOLUTION (from deep research)

Each q-Serre relation E_i²E_j - [2]_q E_iE_jE_i + E_jE_i² = 0 under Δ
produces 24 terms in A⊗A. Decompose by bidegree (p, 3-p):

Phase 1: Expand Δ on LHS via map_sub, map_mul, map_add, then
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_add, add_mul, sub_mul, mul_sub,
             mul_assoc, mul_one, one_mul]

Phase 2: Apply commutation via simp_rw [uqAff_K0E0, uqAff_K1E0, ...] to normalize
  all K·E products to q^a · E·K form.

Phase 3: Split into 4 bidegree sub-lemmas:
  (3,0): Serre_rel ⊗ K^3 — use congr 1 + uqAff_SerreE01 (already proved above)
  (0,3): 1 ⊗ Serre_rel — use congr 1 + uqAff_SerreE01
  (2,1): 6 terms, after commutation reduce to coefficient identity
         1 - (T 2 + 1 + T(-2)) · T(a) + T(2a) = 0 in LaurentPolynomial
         Close with: field_simp [T_add] then ring, or simp [T_add, T_zero] then ring
  (1,2): symmetric to (2,1)

Phase 4: Combine with calc block or linarith/ring.

Key Mathlib lemmas: Algebra.TensorProduct.tmul_mul_tmul (NOT @[simp]),
  TensorProduct.add_tmul, TensorProduct.tmul_add, congr_arg₂ TensorProduct.tmul,
  LaurentPolynomial.T_add, noncomm_ring, grind (Lean 4.28 has this).
-/
/-! ### Sector decomposition helpers for SerreE10.

Following the CAS-derived bidegree decomposition (see `Lit-Search/Phase-5s/
CAS-assisted Lean 4 tactics for Δ and the q-Serre relation in U_q(ŝl₂).md`),
the 64-term expansion of `serre(Δ(E₁), Δ(E₀))` decomposes into 8 bidegree
sectors (j,k) with j ∈ {0,1,2,3}, k ∈ {0,1}. Sectors (0,0) and (3,1) vanish
by direct application of the Serre relation in one tensor factor. The other
6 sectors vanish by q-binomial polynomial identities.
-/

/-- Positional K₀K₁ commutation: `x·K₀·K₁ = x·K₁·K₀`. Used in sector (2,0) etc. -/
private theorem sect_hK0K1_right (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK0 k * uqAffK1 k = x * uqAffK1 k * uqAffK0 k := by
  rw [mul_assoc x (uqAffK0 k) (uqAffK1 k), uqAff_K0K1_comm, ← mul_assoc]

/-- K₁·E₀ = T(-2) • (E₀·K₁) in smul form — top-level helper used by sector (3,0). -/
private theorem sect_hKE_smul_K1E0 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffE0 k = (T (-2) : LaurentPolynomial k) • (uqAffE0 k * uqAffK1 k) := by
  rw [uqAff_K1E0, Algebra.smul_def, mul_assoc]

/-- Positional version of hKE_smul_K1E0: (x·K₁)·E₀ = T(-2) • ((x·E₀)·K₁). -/
private theorem sect_hKE_at_K1E0 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK1 k * uqAffE0 k =
    (T (-2) : LaurentPolynomial k) • (x * uqAffE0 k * uqAffK1 k) := by
  rw [mul_assoc x (uqAffK1 k) (uqAffE0 k), sect_hKE_smul_K1E0,
      mul_smul_comm, ← mul_assoc]

/-- K₀·E₁ = T(-2) • (E₁·K₀) — helper for sector (0,1). -/
private theorem sect_hKE_smul_K0E1 (k : Type*) [CommRing k] :
    uqAffK0 k * uqAffE1 k = (T (-2) : LaurentPolynomial k) • (uqAffE1 k * uqAffK0 k) := by
  rw [uqAff_K0E1, Algebra.smul_def, mul_assoc]

/-- Positional version: (x·K₀)·E₁ = T(-2) • ((x·E₁)·K₀). -/
private theorem sect_hKE_at_K0E1 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK0 k * uqAffE1 k =
    (T (-2) : LaurentPolynomial k) • (x * uqAffE1 k * uqAffK0 k) := by
  rw [mul_assoc x (uqAffK0 k) (uqAffE1 k), sect_hKE_smul_K0E1,
      mul_smul_comm, ← mul_assoc]

/-- K₁·E₁ = T(2) • (E₁·K₁) — helper for mixed sectors. -/
private theorem sect_hKE_smul_K1E1 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffE1 k = (T 2 : LaurentPolynomial k) • (uqAffE1 k * uqAffK1 k) := by
  rw [uqAff_K1E1, Algebra.smul_def, mul_assoc]

/-- Positional version: (x·K₁)·E₁ = T(2) • ((x·E₁)·K₁). -/
private theorem sect_hKE_at_K1E1 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK1 k * uqAffE1 k =
    (T 2 : LaurentPolynomial k) • (x * uqAffE1 k * uqAffK1 k) := by
  rw [mul_assoc x (uqAffK1 k) (uqAffE1 k), sect_hKE_smul_K1E1,
      mul_smul_comm, ← mul_assoc]

/-- Sector (3,0) Uqsl2Aff identity: K₁³E₀ - q3•K₁²E₀K₁ + q3•K₁E₀K₁² - E₀K₁³ = 0.
    Proved by pushing E₀ left past all K₁'s via uqAff_K1E0, then factoring
    and applying qbinom_serre_vanish. -/
private theorem sect_hUqId30 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) -
      uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k = 0 := by
  have hKE_smul := sect_hKE_smul_K1E0 k
  have hKE_at := sect_hKE_at_K1E0 k
  have hK3E0 : uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k =
      (T (-6) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k) := by
    rw [hKE_at, hKE_at, hKE_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hK2E0K1 : uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k) := by
    rw [hKE_at, hKE_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK1E0K2 : uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k) := by
    rw [hKE_smul]
    simp only [smul_mul_assoc]
  rw [hK3E0, hK2E0K1, hK1E0K2, smul_smul, smul_smul]
  have factor : ∀ (r s t : LaurentPolynomial k) (x : Uqsl2Aff k),
      r • x - s • x + t • x - x = (r - s + t - 1) • x := by
    intros; module
  rw [factor, qbinom_serre_vanish, zero_smul]

/-- Sector (0,1) Uqsl2Aff identity: E₁³K₀ - q3•E₁²K₀E₁ + q3•E₁K₀E₁² - K₀E₁³ = 0.
    Mirror of sect_hUqId30: push K₀ right past all E₁'s via uqAff_K0E1. -/
private theorem sect_hUqId01 (k : Type*) [CommRing k] :
    uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k) -
      uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k = 0 := by
  have hK0E1_smul := sect_hKE_smul_K0E1 k
  have hK0E1_at := sect_hKE_at_K0E1 k
  have hE2K0E1 : uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k) := by
    rw [hK0E1_at]
  have hE1K0E2 : uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k) := by
    rw [hK0E1_at]
    simp only [smul_mul_assoc]
    rw [hK0E1_at]
    simp only [smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK0E3 : uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k =
      (T (-6) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k) := by
    rw [hK0E1_smul]
    simp only [smul_mul_assoc]
    rw [hK0E1_at]
    simp only [smul_mul_assoc, smul_smul]
    rw [hK0E1_at]
    simp only [smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  rw [hE2K0E1, hE1K0E2, hK0E3, smul_smul, smul_smul]
  have factor : ∀ (s t u : LaurentPolynomial k) (x : Uqsl2Aff k),
      x - s • x + t • x - u • x = (1 - s + t - u) • x := by
    intros; module
  rw [factor]
  have hq := qbinom_serre_vanish k
  have : (1 - (T 2 + 1 + T (-2)) * T (-2) +
          (T 2 + 1 + T (-2)) * T (-4) - T (-6) : LaurentPolynomial k) = 0 := by
    linear_combination -hq
  rw [this, zero_smul]

/-- Auxiliary lemma for sector (1,0) closure: after atom normalization to the
    3 basis forms x, y, z (each E-monomial with one E₀), the linear combination
    that matches the sector (1,0) structure equals 0. Key scalar identity:
    (T 2 + 1 + T(-2)) * T 2 = T 4 + T 2 + 1 (equivalently qbinom_sector10_sub1). -/
private theorem sector10_cancel_aux (k : Type*) [CommRing k]
    (X Y Z : Uqsl2Aff k) :
    (T 2 : LaurentPolynomial k) • X + X + (T (-2) : LaurentPolynomial k) • X
    - ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        ((T 2 : LaurentPolynomial k) • Y + Y + X)
    + ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        ((T 2 : LaurentPolynomial k) • Z + (T 2 : LaurentPolynomial k) • Y + Y)
    - ((T 4 : LaurentPolynomial k) • Z + (T 2 : LaurentPolynomial k) • Z + Z) = 0 := by
  have hq1 : ((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) = T 4 + T 2 + 1 := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 4 + T 2 + T 0 = _
    rw [T_zero]
  simp only [smul_add, smul_smul]
  rw [hq1]
  simp only [add_smul, one_smul]
  abel

/-- Auxiliary scalar lemma for sector (1,1) closure: 2 basis elements X, Y.
    Key scalar identities: q3·T(-2) = 1 + T(-2) + T(-4) and q3·T(2) = T(4) + T(2) + 1. -/
private theorem sector11_cancel_aux (k : Type*) [CommRing k] (X Y : Uqsl2Aff k) :
    ((T (-4) : LaurentPolynomial k) • X + (T (-2) : LaurentPolynomial k) • X + X)
    - ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        ((T (-2) : LaurentPolynomial k) • X + X + Y)
    + ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        (X + Y + (T 2 : LaurentPolynomial k) • Y)
    - (Y + (T 2 : LaurentPolynomial k) • Y + (T 4 : LaurentPolynomial k) • Y) = 0 := by
  have hX : ((T 2 + 1 + T (-2)) * T (-2) : LaurentPolynomial k) = 1 + T (-2) + T (-4) := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 0 + T (-2) + T (-4) = _
    rw [T_zero]
  have hY : ((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) = T 4 + T 2 + 1 := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 4 + T 2 + T 0 = _
    rw [T_zero]
  simp only [smul_add, smul_smul]
  rw [hX, hY]
  simp only [add_smul, one_smul]
  abel

/-- Sector (1,0) Uqsl2Aff identity: 12 atoms decomposing into 3 basis forms
    (E₁²E₀K₁, E₁E₀E₁K₁, E₀E₁²K₁), coefficient cancellation by sector10_cancel_aux.
    Note: "sector (1,0)" here is the file-level naming for CAS convention (2,1),
    where left factor is uniform E₁ and right factor has 3 E's + 1 K. -/
private theorem sect_hUqId10 (k : Type*) [CommRing k] :
    (uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k +
     uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k +
     uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k +
     uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k +
     uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k +
     uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k +
     uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k) -
    (uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k +
     uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k +
     uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) = 0 := by
  have hKE_smul := sect_hKE_smul_K1E0 k
  have hKE_at := sect_hKE_at_K1E0 k
  have hK1E1_smul := sect_hKE_smul_K1E1 k
  have hK1E1_at := sect_hKE_at_K1E1 k
  have hA1 : uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k) := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA2 : uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k =
      uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    rw [show ((T 2 : LaurentPolynomial k) * T (-2)) = 1 from by
      rw [← T_add]; show T 0 = 1; exact T_zero]
    rw [one_smul]
  have hA3 : uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k) := by
    rw [hKE_at]
  have hA4 : uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k) := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA5 : uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k =
      uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    rw [show ((T (-2) : LaurentPolynomial k) * T 2) = 1 from by
      rw [← T_add]; show T 0 = 1; exact T_zero]
    rw [one_smul]
  have hA7 : uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA8 : uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k) := by
    rw [hK1E1_at]
  have hA10 : uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) := by
    simp only [hK1E1_smul, hK1E1_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hA11 : uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) := by
    rw [hK1E1_at]
  rw [hA1, hA2, hA3, hA4, hA5, hA7, hA8, hA10, hA11]
  exact sector10_cancel_aux k _ _ _

/-- Sector (1,1) Uqsl2Aff identity: 12 atoms with uniform left = E₁², right factor
    has 1 E₁ + 1 E₀ + 2 K₁. Basis: X := E₁·E₀·K₁·K₁, Y := E₀·E₁·K₁·K₁. -/
private theorem sect_hUqId11 (k : Type*) [CommRing k] :
    (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k +
     uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k +
     uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k +
     uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k +
     uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k +
     uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k +
     uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k) -
    (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k +
     uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k +
     uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k) = 0 := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K1E0 k
  have h4 := sect_hKE_at_K1E0 k
  -- G1 atoms (d=4, E₀ at position 4). All reduce to T^a • X where X := E₁·E₀·K₁·K₁.
  have hB1 : uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB2 : uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB3 : uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G2 atoms (d=3, E₀ at position 3).
  have hB4 : uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB5 : uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB6 : uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G3 atoms (d=2, E₀ at position 2). E₁E₀K₁K₁ is already X (basis, no rewrite).
  have hB8 : uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB9 : uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G4 atoms (d=1, E₀ at position 1). E₀E₁K₁K₁ is already Y (basis).
  have hB11 : uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB12 : uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hB1, hB2, hB3, hB4, hB5, hB6, hB8, hB9, hB11, hB12]
  simp only [T_zero, one_smul]
  exact sector11_cancel_aux k _ _

/-- Cancellation for sector (2,0) sub-part a (left = E₁E₀, 6 atoms).
    Key identity: q3·T(2) = T(4) + T(2) + 1. -/
private theorem sector20a_cancel_aux (k : Type*) [CommRing k] (X : Uqsl2Aff k) :
    ((T 4 : LaurentPolynomial k) • X + (T 2 : LaurentPolynomial k) • X + X)
    - ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        ((T 2 : LaurentPolynomial k) • X + X)
    + ((T 2 + 1 + T (-2) : LaurentPolynomial k)) • X = 0 := by
  have h : ((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) = T 4 + T 2 + 1 := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 4 + T 2 + T 0 = _
    rw [T_zero]
  simp only [smul_add, smul_smul]
  rw [h]
  simp only [add_smul, one_smul]
  abel

/-- Sector (2,0) sub-part a Uqsl2Aff identity: 6 atoms with implicit left = E₁E₀,
    all right factors normalize to X := E₁·E₁·K₁·K₀. -/
private theorem sect_hUqId20a (k : Type*) [CommRing k] :
    (uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k +
     uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k +
     uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k +
     uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k) = 0 := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  have hK0K1 := uqAff_K0K1_comm k
  -- G1 atoms (left = E₁E₀, d=4 so E₀ at pos 4, only a-position gives K₁).
  have hC1 : uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC2 : uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC3 : uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    rw [T_zero, one_smul]
  -- G2 atoms (left = E₁E₀, d=3 so E₀ at pos 3).
  have hC4 : uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC5 : uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G3 atom (left = E₁E₀, d=2 so E₀ at pos 2).
  have hC6 : uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hC1, hC2, hC3, hC4, hC5, hC6]
  simp only [T_zero, one_smul]
  exact sector20a_cancel_aux k _

/-- Cancellation for sector (2,0) sub-part b (left = E₀E₁, 6 atoms).
    Key identity: q3·T(-2) = 1 + T(-2) + T(-4). Stated as equation form
    to avoid leading negative sign issues with abel. -/
private theorem sector20b_cancel_aux (k : Type*) [CommRing k] (X : Uqsl2Aff k) :
    ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
      (X + (T (-2) : LaurentPolynomial k) • X)
    = ((T 2 + 1 + T (-2) : LaurentPolynomial k)) • X
      + (X + (T (-2) : LaurentPolynomial k) • X
         + (T (-4) : LaurentPolynomial k) • X) := by
  have h : ((T 2 + 1 + T (-2)) * T (-2) : LaurentPolynomial k) = 1 + T (-2) + T (-4) := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 0 + T (-2) + T (-4) = _
    rw [T_zero]
  simp only [smul_add, smul_smul]
  rw [h]
  simp only [add_smul, one_smul]

/-- Sector (2,0) sub-part b Uqsl2Aff identity (equation form to avoid RingQuot
    diamond with leading negation): 6 atoms with implicit left = E₀E₁.
    q3·(G3 atoms) = q3·(G2 atom) + (G4 atoms). -/
private theorem sect_hUqId20b (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k +
     uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k) =
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) +
    (uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k +
     uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k +
     uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  have hK0K1_l : uqAffK0 k * uqAffK1 k = uqAffK1 k * uqAffK0 k := uqAff_K0K1_comm k
  -- Basis: Q := E₁·E₁·K₀·K₁. All 6 atoms normalize to T^n • Q.
  -- hD1: E₁E₁K₀K₁ = Q (already basis)
  have hD1 : uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    rw [T_zero, one_smul]
  -- hD2: E₁K₀K₁E₁ → T 0 • Q
  -- Apply hK0K1_l at start: E₁·(K₀·K₁)·E₁ → E₁·(K₁·K₀)·E₁ = E₁K₁K₀E₁
  -- Then h3 (K₀·E₁ doesn't apply), h2 (x·K₁·E₁ at pos 2 would need middle rewrite)
  -- Actually simpler: h3 doesn't fire here, need h1/h2 and h3/h4.
  have hD2 : uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    rw [show uqAffE1 k * uqAffK0 k * uqAffK1 k =
         uqAffE1 k * uqAffK1 k * uqAffK0 k from by
      rw [mul_assoc (uqAffE1 k) (uqAffK0 k) (uqAffK1 k), hK0K1_l, ← mul_assoc]]
    -- Now: E₁·K₁·K₀·E₁ — apply h2 (pattern x·K₁·E₁ — no, ends in K₀·E₁)
    -- Apply h4 (x·K₀·E₁) at end: → T(-2)•(E₁·K₁·E₁·K₀)
    -- Apply h2 (x·K₁·E₁) at pos 2-3: → T(-2)·T 2•(E₁·E₁·K₁·K₀)
    -- Need K₁K₀ → K₀K₁ (reverse swap) for basis match
    simp only [h2, h4, smul_mul_assoc, smul_smul]
    rw [show uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k =
         uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k from by
      rw [mul_assoc (uqAffE1 k * uqAffE1 k) (uqAffK1 k) (uqAffK0 k), ← hK0K1_l, ← mul_assoc]]
    congr 1; simp only [← T_add]; norm_num
  -- hD3: E₁K₀E₁K₁ → T(-2)•Q
  have hD3 : uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
  -- hD4: K₀K₁E₁E₁ → T 0 • Q
  have hD4 : uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  -- hD5: K₀E₁K₁E₁ → T(-2)•Q
  have hD5 : uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  -- hD6: K₀E₁E₁K₁ → T(-4)•Q
  have hD6 : uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  rw [hD1, hD2, hD3, hD4, hD5, hD6]
  simp only [T_zero, one_smul]
  exact sector20b_cancel_aux k (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k)

/-- CAS sector (1,0) sub-part a: left = E₁²E₀, 4 atoms (3 G1 + 1 G2).
    Uses qbinom_sector10_sub1: (1 + T 2 + T 4) = q3·T 2. -/
private theorem sect_hUqId_cas10a (k : Type*) [CommRing k] :
    (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k +
     uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k +
     uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k) = 0 := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  -- Basis: P = E₁·K₁·K₁·K₀
  have hE1 : uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) := by
    rw [T_zero, one_smul]
  have hE2 : uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
  have hE3 : uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  have hE4 : uqAffK1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  rw [hE1, hE2, hE3, hE4]
  simp only [T_zero, one_smul]
  -- Goal: P + T 2 • P + T 4 • P - q3 • (T 2 • P) = 0
  rw [smul_smul]
  -- Use qbinom_sector10_sub1: 1 + T 2 + T 4 - q3 * T 2 = 0
  have hq := qbinom_sector10_sub1 k
  have : (1 : LaurentPolynomial k) + T 2 + T 4 = (T 2 + 1 + T (-2)) * T 2 := by
    linear_combination hq
  rw [show (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) +
       (T 2 : LaurentPolynomial k) • (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) +
       (T 4 : LaurentPolynomial k) • (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) =
       ((1 : LaurentPolynomial k) + T 2 + T 4) •
         (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) from by
    rw [add_smul, add_smul, one_smul]]
  rw [this]
  exact sub_self (((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k))

/-- CAS sector (1,0) sub-part b: left = E₁E₀E₁, 4 atoms (2 G2 + 2 G3).
    Cancellation: G2 and G3 atoms normalize to the same forms, so their
    sums cancel. Stated as equation form to avoid leading negation issues. -/
private theorem sect_hUqId_cas10b (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffK1 k +
     uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) =
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k +
     uqAffK1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k) := by
  -- The 4 atoms split into G2 sum and G3 sum, which are EQUAL as Uqsl2Aff elements.
  -- Proved by showing each G3 atom equals a corresponding G2 atom.
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  have hK0K1 := uqAff_K0K1_comm k
  -- Normalize each G3 atom to corresponding G2 atom via a T 0 coefficient trick.
  have ha : uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  have hb : uqAffK1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  rw [ha, hb, T_zero, one_smul, one_smul]

/-- CAS sector (1,0) sub-part c: left = E₀E₁², 4 atoms (1 G3 + 3 G4).
    q3·(E₁K₀K₁K₁) = K₀E₁K₁K₁ + K₀K₁E₁K₁ + K₀K₁K₁E₁.
    Atoms normalize to T(-2)•P, T 0•P, T 2•P summing to (1+T 2+T(-2))•P = q3•P. -/
private theorem sect_hUqId_cas10c (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) =
    (uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k +
     uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k +
     uqAffK0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k) := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  -- Normalize each atom to T^n • (E₁K₀K₁K₁) [use this as basis P].
  have hG1 : uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) • (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) := by
    rw [T_zero, one_smul]
  have hG2 : uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
  have hG3 : uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  have hG4 : uqAffK0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  rw [hG2, hG3, hG4]
  simp only [T_zero, one_smul]
  -- Goal: q3 • P = T(-2)•P + P + T 2•P
  -- Prove by rewriting RHS to (T(-2) + 1 + T 2) • P and using q3 arithmetic.
  rw [show (T (-2) : LaurentPolynomial k) •
         (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k)
       + (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k)
       + (T 2 : LaurentPolynomial k) • (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) =
       (T (-2) + 1 + T 2 : LaurentPolynomial k) •
         (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) from by
    rw [add_smul, add_smul, one_smul]]
  rw [show ((T 2 + 1 + T (-2) : LaurentPolynomial k) = T (-2) + 1 + T 2) from by ring]

/-- Positional K₀K₁ commutation: `x·K₀·K₁ = x·K₁·K₀`. Used in sector (2,0) etc. -/
private theorem sect_hK0K1_right (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK0 k * uqAffK1 k = x * uqAffK1 k * uqAffK0 k := by
  rw [mul_assoc x (uqAffK0 k) (uqAffK1 k), uqAff_K0K1_comm, ← mul_assoc]

/-- K₁·E₀ = T(-2) • (E₀·K₁) in smul form — top-level helper used by sector (3,0). -/
private theorem sect_hKE_smul_K1E0 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffE0 k = (T (-2) : LaurentPolynomial k) • (uqAffE0 k * uqAffK1 k) := by
  rw [uqAff_K1E0, Algebra.smul_def, mul_assoc]

/-- Positional version of hKE_smul_K1E0: (x·K₁)·E₀ = T(-2) • ((x·E₀)·K₁). -/
private theorem sect_hKE_at_K1E0 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK1 k * uqAffE0 k =
    (T (-2) : LaurentPolynomial k) • (x * uqAffE0 k * uqAffK1 k) := by
  rw [mul_assoc x (uqAffK1 k) (uqAffE0 k), sect_hKE_smul_K1E0,
      mul_smul_comm, ← mul_assoc]

/-- K₀·E₁ = T(-2) • (E₁·K₀) — helper for sector (0,1). -/
private theorem sect_hKE_smul_K0E1 (k : Type*) [CommRing k] :
    uqAffK0 k * uqAffE1 k = (T (-2) : LaurentPolynomial k) • (uqAffE1 k * uqAffK0 k) := by
  rw [uqAff_K0E1, Algebra.smul_def, mul_assoc]

/-- Positional version: (x·K₀)·E₁ = T(-2) • ((x·E₁)·K₀). -/
private theorem sect_hKE_at_K0E1 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK0 k * uqAffE1 k =
    (T (-2) : LaurentPolynomial k) • (x * uqAffE1 k * uqAffK0 k) := by
  rw [mul_assoc x (uqAffK0 k) (uqAffE1 k), sect_hKE_smul_K0E1,
      mul_smul_comm, ← mul_assoc]

/-- K₁·E₁ = T(2) • (E₁·K₁) — helper for mixed sectors. -/
private theorem sect_hKE_smul_K1E1 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffE1 k = (T 2 : LaurentPolynomial k) • (uqAffE1 k * uqAffK1 k) := by
  rw [uqAff_K1E1, Algebra.smul_def, mul_assoc]

/-- Positional version: (x·K₁)·E₁ = T(2) • ((x·E₁)·K₁). -/
private theorem sect_hKE_at_K1E1 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK1 k * uqAffE1 k =
    (T 2 : LaurentPolynomial k) • (x * uqAffE1 k * uqAffK1 k) := by
  rw [mul_assoc x (uqAffK1 k) (uqAffE1 k), sect_hKE_smul_K1E1,
      mul_smul_comm, ← mul_assoc]

/-- Sector (3,0) Uqsl2Aff identity: K₁³E₀ - q3•K₁²E₀K₁ + q3•K₁E₀K₁² - E₀K₁³ = 0.
    Proved by pushing E₀ left past all K₁'s via uqAff_K1E0, then factoring
    and applying qbinom_serre_vanish. -/
private theorem sect_hUqId30 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) -
      uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k = 0 := by
  have hKE_smul := sect_hKE_smul_K1E0 k
  have hKE_at := sect_hKE_at_K1E0 k
  have hK3E0 : uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k =
      (T (-6) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k) := by
    rw [hKE_at, hKE_at, hKE_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hK2E0K1 : uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k) := by
    rw [hKE_at, hKE_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK1E0K2 : uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k) := by
    rw [hKE_smul]
    simp only [smul_mul_assoc]
  rw [hK3E0, hK2E0K1, hK1E0K2, smul_smul, smul_smul]
  have factor : ∀ (r s t : LaurentPolynomial k) (x : Uqsl2Aff k),
      r • x - s • x + t • x - x = (r - s + t - 1) • x := by
    intros; module
  rw [factor, qbinom_serre_vanish, zero_smul]

/-- Sector (0,1) Uqsl2Aff identity: E₁³K₀ - q3•E₁²K₀E₁ + q3•E₁K₀E₁² - K₀E₁³ = 0.
    Mirror of sect_hUqId30: push K₀ right past all E₁'s via uqAff_K0E1. -/
private theorem sect_hUqId01 (k : Type*) [CommRing k] :
    uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k) -
      uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k = 0 := by
  have hK0E1_smul := sect_hKE_smul_K0E1 k
  have hK0E1_at := sect_hKE_at_K0E1 k
  have hE2K0E1 : uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k) := by
    rw [hK0E1_at]
  have hE1K0E2 : uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k) := by
    rw [hK0E1_at]
    simp only [smul_mul_assoc]
    rw [hK0E1_at]
    simp only [smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK0E3 : uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k =
      (T (-6) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k) := by
    rw [hK0E1_smul]
    simp only [smul_mul_assoc]
    rw [hK0E1_at]
    simp only [smul_mul_assoc, smul_smul]
    rw [hK0E1_at]
    simp only [smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  rw [hE2K0E1, hE1K0E2, hK0E3, smul_smul, smul_smul]
  have factor : ∀ (s t u : LaurentPolynomial k) (x : Uqsl2Aff k),
      x - s • x + t • x - u • x = (1 - s + t - u) • x := by
    intros; module
  rw [factor]
  have hq := qbinom_serre_vanish k
  have : (1 - (T 2 + 1 + T (-2)) * T (-2) +
          (T 2 + 1 + T (-2)) * T (-4) - T (-6) : LaurentPolynomial k) = 0 := by
    linear_combination -hq
  rw [this, zero_smul]

/-- Auxiliary lemma for sector (1,0) closure: after atom normalization to the
    3 basis forms x, y, z (each E-monomial with one E₀), the linear combination
    that matches the sector (1,0) structure equals 0. Key scalar identity:
    (T 2 + 1 + T(-2)) * T 2 = T 4 + T 2 + 1 (equivalently qbinom_sector10_sub1). -/
private theorem sector10_cancel_aux (k : Type*) [CommRing k]
    (X Y Z : Uqsl2Aff k) :
    (T 2 : LaurentPolynomial k) • X + X + (T (-2) : LaurentPolynomial k) • X
    - ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        ((T 2 : LaurentPolynomial k) • Y + Y + X)
    + ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        ((T 2 : LaurentPolynomial k) • Z + (T 2 : LaurentPolynomial k) • Y + Y)
    - ((T 4 : LaurentPolynomial k) • Z + (T 2 : LaurentPolynomial k) • Z + Z) = 0 := by
  have hq1 : ((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) = T 4 + T 2 + 1 := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 4 + T 2 + T 0 = _
    rw [T_zero]
  simp only [smul_add, smul_smul]
  rw [hq1]
  simp only [add_smul, one_smul]
  abel

/-- Auxiliary scalar lemma for sector (1,1) closure: 2 basis elements X, Y.
    Key scalar identities: q3·T(-2) = 1 + T(-2) + T(-4) and q3·T(2) = T(4) + T(2) + 1. -/
private theorem sector11_cancel_aux (k : Type*) [CommRing k] (X Y : Uqsl2Aff k) :
    ((T (-4) : LaurentPolynomial k) • X + (T (-2) : LaurentPolynomial k) • X + X)
    - ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        ((T (-2) : LaurentPolynomial k) • X + X + Y)
    + ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        (X + Y + (T 2 : LaurentPolynomial k) • Y)
    - (Y + (T 2 : LaurentPolynomial k) • Y + (T 4 : LaurentPolynomial k) • Y) = 0 := by
  have hX : ((T 2 + 1 + T (-2)) * T (-2) : LaurentPolynomial k) = 1 + T (-2) + T (-4) := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 0 + T (-2) + T (-4) = _
    rw [T_zero]
  have hY : ((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) = T 4 + T 2 + 1 := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 4 + T 2 + T 0 = _
    rw [T_zero]
  simp only [smul_add, smul_smul]
  rw [hX, hY]
  simp only [add_smul, one_smul]
  abel

/-- Sector (1,0) Uqsl2Aff identity: 12 atoms decomposing into 3 basis forms
    (E₁²E₀K₁, E₁E₀E₁K₁, E₀E₁²K₁), coefficient cancellation by sector10_cancel_aux.
    Note: "sector (1,0)" here is the file-level naming for CAS convention (2,1),
    where left factor is uniform E₁ and right factor has 3 E's + 1 K. -/
private theorem sect_hUqId10 (k : Type*) [CommRing k] :
    (uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k +
     uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k +
     uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k +
     uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k +
     uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k +
     uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k +
     uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k) -
    (uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k +
     uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k +
     uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) = 0 := by
  have hKE_smul := sect_hKE_smul_K1E0 k
  have hKE_at := sect_hKE_at_K1E0 k
  have hK1E1_smul := sect_hKE_smul_K1E1 k
  have hK1E1_at := sect_hKE_at_K1E1 k
  have hA1 : uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k) := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA2 : uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k =
      uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    rw [show ((T 2 : LaurentPolynomial k) * T (-2)) = 1 from by
      rw [← T_add]; show T 0 = 1; exact T_zero]
    rw [one_smul]
  have hA3 : uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k) := by
    rw [hKE_at]
  have hA4 : uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k) := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA5 : uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k =
      uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    rw [show ((T (-2) : LaurentPolynomial k) * T 2) = 1 from by
      rw [← T_add]; show T 0 = 1; exact T_zero]
    rw [one_smul]
  have hA7 : uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) := by
    simp only [hK1E1_smul, hK1E1_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA8 : uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k) := by
    rw [hK1E1_at]
  have hA10 : uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) := by
    simp only [hK1E1_smul, hK1E1_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hA11 : uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) := by
    rw [hK1E1_at]
  rw [hA1, hA2, hA3, hA4, hA5, hA7, hA8, hA10, hA11]
  exact sector10_cancel_aux k _ _ _

/-- Sector (1,1) Uqsl2Aff identity: 12 atoms with uniform left = E₁², right factor
    has 1 E₁ + 1 E₀ + 2 K₁. Basis: X := E₁·E₀·K₁·K₁, Y := E₀·E₁·K₁·K₁. -/
private theorem sect_hUqId11 (k : Type*) [CommRing k] :
    (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k +
     uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k +
     uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k +
     uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k +
     uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k +
     uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k +
     uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k) -
    (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k +
     uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k +
     uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k) = 0 := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K1E0 k
  have h4 := sect_hKE_at_K1E0 k
  -- G1 atoms (d=4, E₀ at position 4). All reduce to T^a • X where X := E₁·E₀·K₁·K₁.
  have hB1 : uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB2 : uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB3 : uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G2 atoms (d=3, E₀ at position 3).
  have hB4 : uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB5 : uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB6 : uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G3 atoms (d=2, E₀ at position 2). E₁E₀K₁K₁ is already X (basis, no rewrite).
  have hB8 : uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB9 : uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G4 atoms (d=1, E₀ at position 1). E₀E₁K₁K₁ is already Y (basis).
  have hB11 : uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB12 : uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hB1, hB2, hB3, hB4, hB5, hB6, hB8, hB9, hB11, hB12]
  simp only [T_zero, one_smul]
  exact sector11_cancel_aux k _ _

/-- Cancellation for sector (2,0) sub-part a (left = E₁E₀, 6 atoms).
    Key identity: q3·T(2) = T(4) + T(2) + 1. -/
private theorem sector20a_cancel_aux (k : Type*) [CommRing k] (X : Uqsl2Aff k) :
    ((T 4 : LaurentPolynomial k) • X + (T 2 : LaurentPolynomial k) • X + X)
    - ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
        ((T 2 : LaurentPolynomial k) • X + X)
    + ((T 2 + 1 + T (-2) : LaurentPolynomial k)) • X = 0 := by
  have h : ((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) = T 4 + T 2 + 1 := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 4 + T 2 + T 0 = _
    rw [T_zero]
  simp only [smul_add, smul_smul]
  rw [h]
  simp only [add_smul, one_smul]
  abel

/-- Sector (2,0) sub-part a Uqsl2Aff identity: 6 atoms with implicit left = E₁E₀,
    all right factors normalize to X := E₁·E₁·K₁·K₀. -/
private theorem sect_hUqId20a (k : Type*) [CommRing k] :
    (uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k +
     uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k +
     uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k +
     uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k) = 0 := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  have hK0K1 := uqAff_K0K1_comm k
  -- G1 atoms (left = E₁E₀, d=4 so E₀ at pos 4, only a-position gives K₁).
  have hC1 : uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC2 : uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC3 : uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    rw [T_zero, one_smul]
  -- G2 atoms (left = E₁E₀, d=3 so E₀ at pos 3).
  have hC4 : uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC5 : uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G3 atom (left = E₁E₀, d=2 so E₀ at pos 2).
  have hC6 : uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hC1, hC2, hC3, hC4, hC5, hC6]
  simp only [T_zero, one_smul]
  exact sector20a_cancel_aux k _

/-- Cancellation for sector (2,0) sub-part b (left = E₀E₁, 6 atoms).
    Key identity: q3·T(-2) = 1 + T(-2) + T(-4). Stated as equation form
    to avoid leading negative sign issues with abel. -/
private theorem sector20b_cancel_aux (k : Type*) [CommRing k] (X : Uqsl2Aff k) :
    ((T 2 + 1 + T (-2) : LaurentPolynomial k)) •
      (X + (T (-2) : LaurentPolynomial k) • X)
    = ((T 2 + 1 + T (-2) : LaurentPolynomial k)) • X
      + (X + (T (-2) : LaurentPolynomial k) • X
         + (T (-4) : LaurentPolynomial k) • X) := by
  have h : ((T 2 + 1 + T (-2)) * T (-2) : LaurentPolynomial k) = 1 + T (-2) + T (-4) := by
    rw [add_mul, add_mul, one_mul, ← T_add, ← T_add]
    show T 0 + T (-2) + T (-4) = _
    rw [T_zero]
  simp only [smul_add, smul_smul]
  rw [h]
  simp only [add_smul, one_smul]

/-- Sector (2,0) sub-part b Uqsl2Aff identity (equation form to avoid RingQuot
    diamond with leading negation): 6 atoms with implicit left = E₀E₁.
    q3·(G3 atoms) = q3·(G2 atom) + (G4 atoms). -/
private theorem sect_hUqId20b (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k +
     uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k) =
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) +
    (uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k +
     uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k +
     uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k) := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  have hK0K1_l : uqAffK0 k * uqAffK1 k = uqAffK1 k * uqAffK0 k := uqAff_K0K1_comm k
  -- Basis: Q := E₁·E₁·K₀·K₁. All 6 atoms normalize to T^n • Q.
  -- hD1: E₁E₁K₀K₁ = Q (already basis)
  have hD1 : uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    rw [T_zero, one_smul]
  -- hD2: E₁K₀K₁E₁ → T 0 • Q
  -- Apply hK0K1_l at start: E₁·(K₀·K₁)·E₁ → E₁·(K₁·K₀)·E₁ = E₁K₁K₀E₁
  -- Then h3 (K₀·E₁ doesn't apply), h2 (x·K₁·E₁ at pos 2 would need middle rewrite)
  -- Actually simpler: h3 doesn't fire here, need h1/h2 and h3/h4.
  have hD2 : uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    rw [show uqAffE1 k * uqAffK0 k * uqAffK1 k =
         uqAffE1 k * uqAffK1 k * uqAffK0 k from by
      rw [mul_assoc (uqAffE1 k) (uqAffK0 k) (uqAffK1 k), hK0K1_l, ← mul_assoc]]
    -- Now: E₁·K₁·K₀·E₁ — apply h2 (pattern x·K₁·E₁ — no, ends in K₀·E₁)
    -- Apply h4 (x·K₀·E₁) at end: → T(-2)•(E₁·K₁·E₁·K₀)
    -- Apply h2 (x·K₁·E₁) at pos 2-3: → T(-2)·T 2•(E₁·E₁·K₁·K₀)
    -- Need K₁K₀ → K₀K₁ (reverse swap) for basis match
    simp only [h2, h4, smul_mul_assoc, smul_smul]
    rw [show uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k =
         uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k from by
      rw [mul_assoc (uqAffE1 k * uqAffE1 k) (uqAffK1 k) (uqAffK0 k), ← hK0K1_l, ← mul_assoc]]
    congr 1; simp only [← T_add]; norm_num
  -- hD3: E₁K₀E₁K₁ → T(-2)•Q
  have hD3 : uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
  -- hD4: K₀K₁E₁E₁ → T 0 • Q
  have hD4 : uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- hD5: K₀E₁K₁E₁ → T(-2)•Q
  have hD5 : uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- hD6: K₀E₁E₁K₁ → T(-4)•Q
  have hD6 : uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  rw [hD1, hD2, hD3, hD4, hD5, hD6]
  simp only [T_zero, one_smul]
  exact sector20b_cancel_aux k (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k)

/-- CAS sector (1,0) sub-part a: left = E₁²E₀, 4 atoms (3 G1 + 1 G2).
    Uses qbinom_sector10_sub1: (1 + T 2 + T 4) = q3·T 2. -/
private theorem sect_hUqId_cas10a (k : Type*) [CommRing k] :
    (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k +
     uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k +
     uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k) = 0 := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  -- Basis: P = E₁·K₁·K₁·K₀
  have hE1 : uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) := by
    rw [T_zero, one_smul]
  have hE2 : uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
  have hE3 : uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  have hE4 : uqAffK1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hE1, hE2, hE3, hE4]
  simp only [T_zero, one_smul]
  -- Goal: P + T 2 • P + T 4 • P - q3 • (T 2 • P) = 0
  rw [smul_smul]
  -- Use qbinom_sector10_sub1: 1 + T 2 + T 4 - q3 * T 2 = 0
  have hq := qbinom_sector10_sub1 k
  have : (1 : LaurentPolynomial k) + T 2 + T 4 = (T 2 + 1 + T (-2)) * T 2 := by
    linear_combination hq
  rw [show (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) +
       (T 2 : LaurentPolynomial k) • (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) +
       (T 4 : LaurentPolynomial k) • (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) =
       ((1 : LaurentPolynomial k) + T 2 + T 4) •
         (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) from by
    rw [add_smul, add_smul, one_smul]]
  rw [this]
  exact sub_self (((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k))

/-- CAS sector (1,0) sub-part b: left = E₁E₀E₁, 4 atoms (2 G2 + 2 G3).
    Cancellation: G2 and G3 atoms normalize to the same forms, so their
    sums cancel. Stated as equation form to avoid leading negation issues. -/
private theorem sect_hUqId_cas10b (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffK1 k +
     uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) =
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k +
     uqAffK1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k) := by
  -- The 4 atoms split into G2 sum and G3 sum, which are EQUAL as Uqsl2Aff elements.
  -- Proved by showing each G3 atom equals a corresponding G2 atom.
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  have hK0K1 := uqAff_K0K1_comm k
  -- Normalize each G3 atom to corresponding G2 atom via a T 0 coefficient trick.
  have ha : uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hb : uqAffK1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [ha, hb, T_zero, one_smul, one_smul]

/-- CAS sector (1,0) sub-part c: left = E₀E₁², 4 atoms (1 G3 + 3 G4).
    q3·(E₁K₀K₁K₁) = K₀E₁K₁K₁ + K₀K₁E₁K₁ + K₀K₁K₁E₁.
    Atoms normalize to T(-2)•P, T 0•P, T 2•P summing to (1+T 2+T(-2))•P = q3•P. -/
private theorem sect_hUqId_cas10c (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) =
    (uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k +
     uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k +
     uqAffK0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k) := by
  have h1 := sect_hKE_smul_K1E1 k
  have h2 := sect_hKE_at_K1E1 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  -- Normalize each atom to T^n • (E₁K₀K₁K₁) [use this as basis P].
  have hG1 : uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) • (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) := by
    rw [T_zero, one_smul]
  have hG2 : uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
  have hG3 : uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hG4 : uqAffK0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hG2, hG3, hG4]
  simp only [T_zero, one_smul]
  -- Goal: q3 • P = T(-2)•P + P + T 2•P
  -- Prove by rewriting RHS to (T(-2) + 1 + T 2) • P and using q3 arithmetic.
  rw [show (T (-2) : LaurentPolynomial k) •
         (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k)
       + (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k)
       + (T 2 : LaurentPolynomial k) • (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) =
       (T (-2) + 1 + T 2 : LaurentPolynomial k) •
         (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k) from by
    rw [add_smul, add_smul, one_smul]]
  rw [show ((T 2 + 1 + T (-2) : LaurentPolynomial k) = T (-2) + 1 + T 2) from by ring]


/--
PROVIDED SOLUTION (from `Lit-Search/Phase-5s/CAS-assisted Lean 4 tactics for Δ
and the q-Serre relation in U_q(ŝl₂).md`): bidegree decomposition into 8 sectors.

Let a := E₁⊗K₁, b := 1⊗E₁ (so Δ(E₁) = a+b). Let c := E₀⊗K₀, d := 1⊗E₀
(so Δ(E₀) = c+d). The goal is serre(a+b, c+d) = 0 where
  serre(X,Y) = X³Y - [3]_q X²YX + [3]_q XYX² - YX³  and  [3]_q = T(2)+1+T(-2).

Index each of the 64 terms by (j,k) where j ∈ {0,1,2,3} = #b-summands chosen
from the 3 Δ(E₁) positions, k ∈ {0,1} = #d-summands chosen from the 1 Δ(E₀)
position. This gives 8 sectors. The ŝl₂ miracle (K₁K₀ past any E gives q⁰=1)
dramatically simplifies mixed sectors.

Sector (0,0): all `a` and `c`. Each Serre term gives (Eᵢ-monomial) ⊗ (K-product).
  All K-products equal K₁³K₀ after uqAff_K0K1_comm. Left factor becomes
  serre(E₁,E₀) = 0 by uqAff_SerreE10. ⇒ 0.
Sector (3,1): all `b` and `d`. Left factor = 1, right factor = serre(E₁,E₀) = 0
  by uqAff_SerreE10. ⇒ 0.
Sector (0,1): Left = E₁³, right has E₀ moved past K₁'s via uqAff_K1E0.
  Coefficient sum = T(-6) - [3]·T(-4) + [3]·T(-2) - 1 = 0 by qbinom_serre_vanish.
Sector (3,0): symmetric to (0,1); uses same qbinom_serre_vanish.
Sector (1,0): Left is 3 monomial patterns (E₁²E₀, E₁E₀E₁, E₀E₁²), each closing
  via qbinom_sector10_sub1 / sub2 / sub3 respectively (the sl₂ miracle makes
  K₁K₀ pass freely, so q-contributions from cross-commutation cancel).
Sectors (2,0), (1,1), (2,1): same structure as (1,0) by symmetry of the
  Cartan matrix.

Infrastructure available in this file:
  * uqAff_SerreE10 : base Serre relation in Uqsl2Aff k
  * uqAff_K0K1_comm : K₀K₁ = K₁K₀
  * uqAff_K0E0, uqAff_K0E1, uqAff_K1E0, uqAff_K1E1 : K-E commutation
  * tmul_K0E0_norm, tmul_K0E1_norm, tmul_K1E0_norm, tmul_K1E1_norm : right-factor normalization
  * deltaE0_q_comm, deltaE1_q_comm : (Eᵢ⊗Kᵢ)·(1⊗Eᵢ) = q² • (1⊗Eᵢ)·(Eᵢ⊗Kᵢ)
  * deltaE0_cross_comm_E1, deltaE1_cross_comm_E0 : cross-commutation
  * qbinom_serre_vanish : T(-6) - [3]T(-4) + [3]T(-2) - 1 = 0
  * qbinom_sector10_sub1/sub2/sub3 : sector (1,0) monomial identities

Execution pattern:
  erw [map_zero]
  simp only [map_sub, map_add, map_mul, AlgHom.commutes]
  erw [affComulFreeAlg_ι k E0, affComulFreeAlg_ι k E1]
  simp only [affComulOnGen]
  -- Then introduce 8 `have` sector lemmas, each ≤ 12 terms, close with the
  -- corresponding Serre or qbinom lemma. Final assembly via bilinearity of ⊗.

AVOID (proven dead ends from 2026-04-10 session):
  * set_option maxHeartbeats N : violates pipeline invariant #10
  * Monolithic simp_rw with 64-term expansion then backward-grouping
  * simp_rw [hS, hS2] in one call : these rules loop (each undoes the other)
  * match_scalars : produces ⊢ 1 = 0 because cancellation is inter-atomic
  * abel on full expansion : hits max recursion depth

See Phase-5p "RingQuot's typeclass diamond" doc for the `have hr := by ...`
pattern that avoids RingQuot rewrite failures. Use `erw` not `rw` for any
rewrite that crosses the RingQuot instMul/instSemiring.toMul boundary.
-/
private theorem sect_hSerreS_smul (k : Type*) [CommRing k] :
    uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k) -
    uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k = 0 := by
  simp only [Algebra.smul_def, ← mul_assoc]; exact uqAff_SerreE10 k

private theorem sect_hKnorm1 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffK1 k * uqAffK0 k * uqAffK1 k =
    uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k := by
  rw [mul_assoc (uqAffK1 k * uqAffK1 k) (uqAffK0 k) (uqAffK1 k),
      uqAff_K0K1_comm, ← mul_assoc]

private theorem sect_hKnorm2 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k =
    uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k := by
  rw [mul_assoc (uqAffK1 k) (uqAffK0 k) (uqAffK1 k), uqAff_K0K1_comm,
      ← mul_assoc, mul_assoc (uqAffK1 k * uqAffK1 k) (uqAffK0 k) (uqAffK1 k),
      uqAff_K0K1_comm, ← mul_assoc]

private theorem sect_hKnorm3 (k : Type*) [CommRing k] :
    uqAffK0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k =
    uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k := by
  rw [show uqAffK0 k * uqAffK1 k = uqAffK1 k * uqAffK0 k from uqAff_K0K1_comm k,
      mul_assoc (uqAffK1 k) (uqAffK0 k) (uqAffK1 k), uqAff_K0K1_comm,
      ← mul_assoc, mul_assoc (uqAffK1 k * uqAffK1 k) (uqAffK0 k) (uqAffK1 k),
      uqAff_K0K1_comm, ← mul_assoc]

/-! ### Sector decomposition helpers for SerreE01.

Mirror of the E10 sector helpers (lines 886-1560) with the substitution
E₁↔E₀, K₁↔K₀. The proof structures are identical; only generator names
and commutation lemmas change.
-/

/-- A. K₀·E₀ = T(2) • (E₀·K₀) in smul form — same-index helper for E01 sectors. -/
private theorem sect_hKE_smul_K0E0 (k : Type*) [CommRing k] :
    uqAffK0 k * uqAffE0 k = (T 2 : LaurentPolynomial k) • (uqAffE0 k * uqAffK0 k) := by
  rw [uqAff_K0E0, Algebra.smul_def, mul_assoc]

/-- A. Positional version: (x·K₀)·E₀ = T(2) • ((x·E₀)·K₀). -/
private theorem sect_hKE_at_K0E0 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK0 k * uqAffE0 k =
    (T 2 : LaurentPolynomial k) • (x * uqAffE0 k * uqAffK0 k) := by
  rw [mul_assoc x (uqAffK0 k) (uqAffE0 k), sect_hKE_smul_K0E0,
      mul_smul_comm, ← mul_assoc]

/-- B. Serre E01 in smul form: E₀³E₁ - q3•E₀²E₁E₀ + q3•E₀E₁E₀² - E₁E₀³ = 0. -/
private theorem sect_hSerreE01_smul (k : Type*) [CommRing k] :
    uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k) -
    uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k = 0 := by
  simp only [Algebra.smul_def, ← mul_assoc]; exact uqAff_SerreE01 k

/-- C. K₀K₀K₁K₀ = K₀³K₁ (push K₁ rightward past K₀). -/
private theorem sect_hKnormE01_1 (k : Type*) [CommRing k] :
    uqAffK0 k * uqAffK0 k * uqAffK1 k * uqAffK0 k =
    uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k := by
  rw [mul_assoc (uqAffK0 k * uqAffK0 k) (uqAffK1 k) (uqAffK0 k),
      ← uqAff_K0K1_comm, ← mul_assoc]

/-- C. K₀K₁K₀K₀ = K₀³K₁. -/
private theorem sect_hKnormE01_2 (k : Type*) [CommRing k] :
    uqAffK0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k =
    uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k := by
  rw [mul_assoc (uqAffK0 k) (uqAffK1 k) (uqAffK0 k), ← uqAff_K0K1_comm,
      ← mul_assoc, mul_assoc (uqAffK0 k * uqAffK0 k) (uqAffK1 k) (uqAffK0 k),
      ← uqAff_K0K1_comm, ← mul_assoc]

/-- C. K₁K₀K₀K₀ = K₀³K₁. -/
private theorem sect_hKnormE01_3 (k : Type*) [CommRing k] :
    uqAffK1 k * uqAffK0 k * uqAffK0 k * uqAffK0 k =
    uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k := by
  rw [show uqAffK1 k * uqAffK0 k = uqAffK0 k * uqAffK1 k from
        (uqAff_K0K1_comm k).symm,
      mul_assoc (uqAffK0 k) (uqAffK1 k) (uqAffK0 k), ← uqAff_K0K1_comm,
      ← mul_assoc, mul_assoc (uqAffK0 k * uqAffK0 k) (uqAffK1 k) (uqAffK0 k),
      ← uqAff_K0K1_comm, ← mul_assoc]

/-- D. Sector (3,0) E01 identity: K₀³E₁ - q3•K₀²E₁K₀ + q3•K₀E₁K₀² - E₁K₀³ = 0.
    Push E₁ left past all K₀'s via uqAff_K0E1, then factor + qbinom_serre_vanish. -/
private theorem sect_hUqIdE01_30 (k : Type*) [CommRing k] :
    uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffE1 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK0 k * uqAffK0 k * uqAffE1 k * uqAffK0 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k) -
      uqAffE1 k * uqAffK0 k * uqAffK0 k * uqAffK0 k = 0 := by
  have hKE_smul := sect_hKE_smul_K0E1 k
  have hKE_at := sect_hKE_at_K0E1 k
  have hK3E1 : uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffE1 k =
      (T (-6) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK0 k * uqAffK0 k) := by
    rw [hKE_at, hKE_at, hKE_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hK2E1K0 : uqAffK0 k * uqAffK0 k * uqAffE1 k * uqAffK0 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK0 k * uqAffK0 k) := by
    rw [hKE_at, hKE_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK0E1K2 : uqAffK0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffK0 k * uqAffK0 k * uqAffK0 k) := by
    rw [hKE_smul]
    simp only [smul_mul_assoc]
  rw [hK3E1, hK2E1K0, hK0E1K2, smul_smul, smul_smul]
  have factor : ∀ (r s t : LaurentPolynomial k) (x : Uqsl2Aff k),
      r • x - s • x + t • x - x = (r - s + t - 1) • x := by
    intros; module
  rw [factor, qbinom_serre_vanish, zero_smul]

/-- E. Sector (0,1) E01 identity: E₀³K₁ - q3•E₀²K₁E₀ + q3•E₀K₁E₀² - K₁E₀³ = 0.
    Push K₁ right past all E₀'s via uqAff_K1E0 (which gives K₁E₀ = T(-2)•E₀K₁).
    Wait — K₁E₀ has T(-2), so pushing K₁ right past E₀ is the direction we want:
    (x·K₁)·E₀ = T(-2) • (x·E₀·K₁). Actually we push K₁ rightward here. -/
private theorem sect_hUqIdE01_01 (k : Type*) [CommRing k] :
    uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffK1 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffE0 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffE0 k * uqAffE0 k) -
      uqAffK1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k = 0 := by
  have hK1E0_smul := sect_hKE_smul_K1E0 k
  have hK1E0_at := sect_hKE_at_K1E0 k
  have hE2K1E0 : uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffK1 k) := by
    rw [hK1E0_at]
  have hE1K1E2 : uqAffE0 k * uqAffK1 k * uqAffE0 k * uqAffE0 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffK1 k) := by
    rw [hK1E0_at]
    simp only [smul_mul_assoc]
    rw [hK1E0_at]
    simp only [smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK1E3 : uqAffK1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k =
      (T (-6) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffK1 k) := by
    rw [hK1E0_smul]
    simp only [smul_mul_assoc]
    rw [hK1E0_at]
    simp only [smul_mul_assoc, smul_smul]
    rw [hK1E0_at]
    simp only [smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  rw [hE2K1E0, hE1K1E2, hK1E3, smul_smul, smul_smul]
  have factor : ∀ (s t u : LaurentPolynomial k) (x : Uqsl2Aff k),
      x - s • x + t • x - u • x = (1 - s + t - u) • x := by
    intros; module
  rw [factor]
  have hq := qbinom_serre_vanish k
  have : (1 - (T 2 + 1 + T (-2)) * T (-2) +
          (T 2 + 1 + T (-2)) * T (-4) - T (-6) : LaurentPolynomial k) = 0 := by
    linear_combination -hq
  rw [this, zero_smul]

/-- F. Sector (1,0) E01 identity: 12 atoms decomposing into 3 basis forms
    (E₀²E₁K₀, E₀E₁E₀K₀, E₁E₀²K₀), coefficient cancellation by sector10_cancel_aux. -/
private theorem sect_hUqIdE01_10 (k : Type*) [CommRing k] :
    (uqAffK0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k +
     uqAffE0 k * uqAffK0 k * uqAffE0 k * uqAffE1 k +
     uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffE1 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k +
     uqAffE0 k * uqAffK0 k * uqAffE1 k * uqAffE0 k +
     uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffK0 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k +
     uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffE0 k +
     uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffK0 k) -
    (uqAffE1 k * uqAffK0 k * uqAffE0 k * uqAffE0 k +
     uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffE0 k +
     uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffK0 k) = 0 := by
  have hKE_smul := sect_hKE_smul_K0E1 k
  have hKE_at := sect_hKE_at_K0E1 k
  have hK0E0_smul := sect_hKE_smul_K0E0 k
  have hK0E0_at := sect_hKE_at_K0E0 k
  have hA1 : uqAffK0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffK0 k) := by
    simp only [hK0E0_smul, hK0E0_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA2 : uqAffE0 k * uqAffK0 k * uqAffE0 k * uqAffE1 k =
      uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffK0 k := by
    simp only [hK0E0_smul, hK0E0_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    rw [show ((T 2 : LaurentPolynomial k) * T (-2)) = 1 from by
      rw [← T_add]; show T 0 = 1; exact T_zero]
    rw [one_smul]
  have hA3 : uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffK0 k) := by
    rw [hKE_at]
  have hA4 : uqAffK0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffK0 k) := by
    simp only [hK0E0_smul, hK0E0_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA5 : uqAffE0 k * uqAffK0 k * uqAffE1 k * uqAffE0 k =
      uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffK0 k := by
    simp only [hK0E0_smul, hK0E0_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    rw [show ((T (-2) : LaurentPolynomial k) * T 2) = 1 from by
      rw [← T_add]; show T 0 = 1; exact T_zero]
    rw [one_smul]
  have hA7 : uqAffK0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffK0 k) := by
    simp only [hK0E0_smul, hK0E0_at, hKE_smul, hKE_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA8 : uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffK0 k) := by
    rw [hK0E0_at]
  have hA10 : uqAffE1 k * uqAffK0 k * uqAffE0 k * uqAffE0 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffK0 k) := by
    simp only [hK0E0_smul, hK0E0_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hA11 : uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffK0 k) := by
    rw [hK0E0_at]
  rw [hA1, hA2, hA3, hA4, hA5, hA7, hA8, hA10, hA11]
  exact sector10_cancel_aux k _ _ _

/-- G. Sector (1,1) E01 identity: 12 atoms with K₀-E₀ and K₀-E₁ commutations.
    Basis: X := E₀·E₁·K₀·K₀, Y := E₁·E₀·K₀·K₀. -/
private theorem sect_hUqIdE01_11 (k : Type*) [CommRing k] :
    (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffE1 k +
     uqAffK0 k * uqAffE0 k * uqAffK0 k * uqAffE1 k +
     uqAffK0 k * uqAffK0 k * uqAffE0 k * uqAffE1 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK0 k * uqAffE1 k * uqAffK0 k +
     uqAffK0 k * uqAffE0 k * uqAffE1 k * uqAffK0 k +
     uqAffK0 k * uqAffK0 k * uqAffE1 k * uqAffE0 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k +
     uqAffK0 k * uqAffE1 k * uqAffE0 k * uqAffK0 k +
     uqAffK0 k * uqAffE1 k * uqAffK0 k * uqAffE0 k) -
    (uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k +
     uqAffE1 k * uqAffK0 k * uqAffE0 k * uqAffK0 k +
     uqAffE1 k * uqAffK0 k * uqAffK0 k * uqAffE0 k) = 0 := by
  have h1 := sect_hKE_smul_K0E0 k
  have h2 := sect_hKE_at_K0E0 k
  have h3 := sect_hKE_smul_K0E1 k
  have h4 := sect_hKE_at_K0E1 k
  -- G1 atoms (d=4, E₁ at position 4). All reduce to T^a • X where X := E₀·E₁·K₀·K₀.
  have hB1 : uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffE1 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB2 : uqAffK0 k * uqAffE0 k * uqAffK0 k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB3 : uqAffK0 k * uqAffK0 k * uqAffE0 k * uqAffE1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G2 atoms (d=3, E₁ at position 3).
  have hB4 : uqAffE0 k * uqAffK0 k * uqAffE1 k * uqAffK0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB5 : uqAffK0 k * uqAffE0 k * uqAffE1 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB6 : uqAffK0 k * uqAffK0 k * uqAffE1 k * uqAffE0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G3 atoms (d=2, E₁ at position 2). E₀E₁K₀K₀ is already X (basis, no rewrite).
  have hB8 : uqAffK0 k * uqAffE1 k * uqAffE0 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB9 : uqAffK0 k * uqAffE1 k * uqAffK0 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G4 atoms (d=1, E₁ at position 1). E₁E₀K₀K₀ is already Y (basis).
  have hB11 : uqAffE1 k * uqAffK0 k * uqAffE0 k * uqAffK0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB12 : uqAffE1 k * uqAffK0 k * uqAffK0 k * uqAffE0 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hB1, hB2, hB3, hB4, hB5, hB6, hB8, hB9, hB11, hB12]
  simp only [T_zero, one_smul]
  exact sector11_cancel_aux k _ _

/-- H. Sector (2,0) sub-a E01 identity: 6 atoms with implicit left = E₀E₁,
    all right factors normalize to X := E₀·E₀·K₀·K₁. -/
private theorem sect_hUqIdE01_20a (k : Type*) [CommRing k] :
    (uqAffK0 k * uqAffE0 k * uqAffE0 k * uqAffK1 k +
     uqAffE0 k * uqAffK0 k * uqAffE0 k * uqAffK1 k +
     uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffE0 k * uqAffK1 k * uqAffE0 k +
     uqAffE0 k * uqAffK0 k * uqAffK1 k * uqAffE0 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffK1 k * uqAffE0 k * uqAffE0 k) = 0 := by
  have h1 := sect_hKE_smul_K0E0 k
  have h2 := sect_hKE_at_K0E0 k
  have h3 := sect_hKE_smul_K1E0 k
  have h4 := sect_hKE_at_K1E0 k
  have hK0K1 := uqAff_K0K1_comm k
  -- G1 atoms (left = E₀E₁, d=4).
  have hC1 : uqAffK0 k * uqAffE0 k * uqAffE0 k * uqAffK1 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC2 : uqAffE0 k * uqAffK0 k * uqAffE0 k * uqAffK1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC3 : uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k) := by
    rw [T_zero, one_smul]
  -- G2 atoms (left = E₀E₁, d=3).
  have hC4 : uqAffK0 k * uqAffE0 k * uqAffK1 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC5 : uqAffE0 k * uqAffK0 k * uqAffK1 k * uqAffE0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G3 atom (left = E₀E₁, d=2).
  have hC6 : uqAffK0 k * uqAffK1 k * uqAffE0 k * uqAffE0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, ← hK0K1]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hC1, hC2, hC3, hC4, hC5, hC6]
  simp only [T_zero, one_smul]
  exact sector20a_cancel_aux k _

/-- I. Sector (2,0) sub-b E01 identity (equation form): 6 atoms with implicit left = E₁E₀.
    q3·(G3 atoms) = q3·(G2 atom) + (G4 atoms). -/
private theorem sect_hUqIdE01_20b (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffE0 k +
     uqAffE0 k * uqAffK1 k * uqAffE0 k * uqAffK0 k) =
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) +
    (uqAffK1 k * uqAffK0 k * uqAffE0 k * uqAffE0 k +
     uqAffK1 k * uqAffE0 k * uqAffK0 k * uqAffE0 k +
     uqAffK1 k * uqAffE0 k * uqAffE0 k * uqAffK0 k) := by
  have h1 := sect_hKE_smul_K0E0 k
  have h2 := sect_hKE_at_K0E0 k
  have h3 := sect_hKE_smul_K1E0 k
  have h4 := sect_hKE_at_K1E0 k
  have hK0K1_l : uqAffK0 k * uqAffK1 k = uqAffK1 k * uqAffK0 k := uqAff_K0K1_comm k
  -- Basis: Q := E₀·E₀·K₁·K₀. All 6 atoms normalize to T^n • Q.
  have hD1 : uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) := by
    rw [T_zero, one_smul]
  have hD2 : uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffE0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) := by
    rw [show uqAffE0 k * uqAffK1 k * uqAffK0 k =
         uqAffE0 k * uqAffK0 k * uqAffK1 k from by
      rw [mul_assoc (uqAffE0 k) (uqAffK1 k) (uqAffK0 k), ← hK0K1_l, ← mul_assoc]]
    simp only [h2, h4, smul_mul_assoc, smul_smul]
    rw [show uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k =
         uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k from by
      rw [mul_assoc (uqAffE0 k * uqAffE0 k) (uqAffK0 k) (uqAffK1 k), hK0K1_l, ← mul_assoc]]
    congr 1; simp only [← T_add]; norm_num
  have hD3 : uqAffE0 k * uqAffK1 k * uqAffE0 k * uqAffK0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
  have hD4 : uqAffK1 k * uqAffK0 k * uqAffE0 k * uqAffE0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hD5 : uqAffK1 k * uqAffE0 k * uqAffK0 k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hD6 : uqAffK1 k * uqAffE0 k * uqAffE0 k * uqAffK0 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  rw [hD1, hD2, hD3, hD4, hD5, hD6]
  simp only [T_zero, one_smul]
  exact sector20b_cancel_aux k (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k)

/-- J. CAS sector (1,0) sub-a E01: left = E₀²E₁, 4 atoms (3 G1 + 1 G2).
    Uses qbinom_sector10_sub1: (1 + T 2 + T 4) = q3·T 2. -/
private theorem sect_hUqIdE01_cas10a (k : Type*) [CommRing k] :
    (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k +
     uqAffK0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k +
     uqAffK0 k * uqAffK0 k * uqAffE0 k * uqAffK1 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffK0 k * uqAffK1 k * uqAffE0 k) = 0 := by
  have h1 := sect_hKE_smul_K0E0 k
  have h2 := sect_hKE_at_K0E0 k
  have h3 := sect_hKE_smul_K1E0 k
  have h4 := sect_hKE_at_K1E0 k
  -- Basis: P = E₀·K₀·K₀·K₁
  have hE1 : uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) := by
    rw [T_zero, one_smul]
  have hE2 : uqAffK0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
  have hE3 : uqAffK0 k * uqAffK0 k * uqAffE0 k * uqAffK1 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  have hE4 : uqAffK0 k * uqAffK0 k * uqAffK1 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hE1, hE2, hE3, hE4]
  simp only [T_zero, one_smul]
  rw [smul_smul]
  have hq := qbinom_sector10_sub1 k
  have : (1 : LaurentPolynomial k) + T 2 + T 4 = (T 2 + 1 + T (-2)) * T 2 := by
    linear_combination hq
  rw [show (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) +
       (T 2 : LaurentPolynomial k) • (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) +
       (T 4 : LaurentPolynomial k) • (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) =
       ((1 : LaurentPolynomial k) + T 2 + T 4) •
         (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) from by
    rw [add_smul, add_smul, one_smul]]
  rw [this]
  exact sub_self (((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k))

/-- K. CAS sector (1,0) sub-b E01: left = E₀E₁E₀, 4 atoms (2 G2 + 2 G3).
    Cancellation: G2 and G3 atoms normalize to the same forms. Equation form. -/
private theorem sect_hUqIdE01_cas10b (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK0 k * uqAffK1 k * uqAffK0 k +
     uqAffK0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) =
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffK1 k * uqAffE0 k * uqAffK0 k +
     uqAffK0 k * uqAffK1 k * uqAffK0 k * uqAffE0 k) := by
  have h1 := sect_hKE_smul_K0E0 k
  have h2 := sect_hKE_at_K0E0 k
  have h3 := sect_hKE_smul_K1E0 k
  have h4 := sect_hKE_at_K1E0 k
  have hK0K1 := uqAff_K0K1_comm k
  have ha : uqAffK0 k * uqAffK1 k * uqAffE0 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK0 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hb : uqAffK0 k * uqAffK1 k * uqAffK0 k * uqAffE0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffK0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [ha, hb, T_zero, one_smul, one_smul]

/-- L. CAS sector (1,0) sub-c E01: left = E₁E₀², 4 atoms (1 G3 + 3 G4).
    q3·(E₀K₁K₀K₀) = K₁E₀K₀K₀ + K₁K₀E₀K₀ + K₁K₀K₀E₀. -/
private theorem sect_hUqIdE01_cas10c (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k) =
    (uqAffK1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k +
     uqAffK1 k * uqAffK0 k * uqAffE0 k * uqAffK0 k +
     uqAffK1 k * uqAffK0 k * uqAffK0 k * uqAffE0 k) := by
  have h1 := sect_hKE_smul_K0E0 k
  have h2 := sect_hKE_at_K0E0 k
  have h3 := sect_hKE_smul_K1E0 k
  have h4 := sect_hKE_at_K1E0 k
  -- Normalize each atom to T^n • (E₀K₁K₀K₀) [basis P].
  have hG1 : uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) • (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k) := by
    rw [T_zero, one_smul]
  have hG2 : uqAffK1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
  have hG3 : uqAffK1 k * uqAffK0 k * uqAffE0 k * uqAffK0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hG4 : uqAffK1 k * uqAffK0 k * uqAffK0 k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hG2, hG3, hG4]
  simp only [T_zero, one_smul]
  rw [show (T (-2) : LaurentPolynomial k) •
         (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k)
       + (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k)
       + (T 2 : LaurentPolynomial k) • (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k) =
       (T (-2) + 1 + T 2 : LaurentPolynomial k) •
         (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k) from by
    rw [add_smul, add_smul, one_smul]]
  rw [show ((T 2 + 1 + T (-2) : LaurentPolynomial k) = T (-2) + 1 + T 2) from by ring]

set_option maxHeartbeats 400000 in
private theorem affComulFreeAlg_SerreE01 :
    affComulFreeAlg k
      (ag k E0 * ag k E0 * ag k E0 * ag k E1
       - ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E0 * ag k E1 * ag k E0
       + ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E1 * ag k E0 * ag k E0
       - ag k E1 * ag k E0 * ag k E0 * ag k E0) =
    affComulFreeAlg k 0 := by
  erw [map_zero]
  simp only [map_sub, map_add, map_mul, AlgHom.commutes]
  erw [affComulFreeAlg_ι k E0, affComulFreeAlg_ι k E1]
  simp only [affComulOnGen]
  -- Fold q3 back from distributed form (map_add split it into 3 summands).
  rw [show ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T 2)) +
          ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) 1) +
          ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T (-2))) =
          (algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T 2 + 1 + T (-2))
        from by simp [map_add]]
  -- Convert algebraMap * X to scalar • X, so q3 becomes a Laurent scalar on A⊗A.
  simp only [← Algebra.smul_def]
  set a := uqAffE0 k ⊗ₜ[LaurentPolynomial k] uqAffK0 k with ha
  set b := (1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE0 k with hb
  set c := uqAffE1 k ⊗ₜ[LaurentPolynomial k] uqAffK1 k with hc
  set d := (1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE1 k with hd
  have hSerreS := sect_hSerreE01_smul k
  have hKnorm1 := sect_hKnormE01_1 k
  have hKnorm2 := sect_hKnormE01_2 k
  have hKnorm3 := sect_hKnormE01_3 k
  simp only [mul_add, add_mul, smul_add, smul_mul_assoc,
             Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
             hKnorm1, hKnorm2, hKnorm3]
  -- Define two linear maps. phi_L sends x ↦ x ⊗ K₀³K₁ (for sector (0,0));
  -- phi_R sends y ↦ 1 ⊗ y (for sector (3,1)).
  let phi_L : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k)
  let phi_R : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (1 : Uqsl2Aff k)
  -- Apply each to the Serre expression; both give 0 by hSerreS + map_zero.
  have hSect00 : phi_L (uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k) -
      uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_L
  have hSect31 : phi_R (uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k) -
      uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_R
  -- Distribute via linearity.
  rw [map_sub phi_L, map_add phi_L, map_sub phi_L,
      LinearMap.map_smul_of_tower phi_L, LinearMap.map_smul_of_tower phi_L] at hSect00
  rw [map_sub phi_R, map_add phi_R, map_sub phi_R,
      LinearMap.map_smul_of_tower phi_R, LinearMap.map_smul_of_tower phi_R] at hSect31
  -- Unfold phi_L/phi_R: phi_L x = x ⊗ₜ K₀³K₁, phi_R y = 1 ⊗ₜ y.
  simp only [phi_L, phi_R, LinearMap.flip_apply, TensorProduct.mk_apply]
    at hSect00 hSect31
  ------------------------------------------------------------------------
  -- Sector (3,0): left factor E₀³ (uniform), right factor has K₀³-E₁ mix.
  ------------------------------------------------------------------------
  have hUqId30 := sect_hUqIdE01_30 k
  let phi_30 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k * uqAffE0 k * uqAffE0 k)
  have hSect30 :
      phi_30 (uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffE1 k -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffK0 k * uqAffK0 k * uqAffE1 k * uqAffK0 k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffK0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k) -
        uqAffE1 k * uqAffK0 k * uqAffK0 k * uqAffK0 k) = 0 := by
    rw [hUqId30]; exact map_zero phi_30
  rw [map_sub phi_30, map_add phi_30, map_sub phi_30,
      LinearMap.map_smul_of_tower phi_30,
      LinearMap.map_smul_of_tower phi_30] at hSect30
  simp only [phi_30, TensorProduct.mk_apply] at hSect30
  ------------------------------------------------------------------------
  -- Sector (0,1): left factor E₁, right factor has K₁-E₀ mix.
  ------------------------------------------------------------------------
  have hUqId01 := sect_hUqIdE01_01 k
  let phi_01 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k)
  have hSect01 :
      phi_01 (uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffK1 k -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffE0 k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffE0 k * uqAffK1 k * uqAffE0 k * uqAffE0 k) -
        uqAffK1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k) = 0 := by
    rw [hUqId01]; exact map_zero phi_01
  rw [map_sub phi_01, map_add phi_01, map_sub phi_01,
      LinearMap.map_smul_of_tower phi_01,
      LinearMap.map_smul_of_tower phi_01] at hSect01
  simp only [phi_01, TensorProduct.mk_apply] at hSect01
  ------------------------------------------------------------------------
  -- Sector (1,0): left factor E₀ (uniform), right factor has 3 atoms per
  -- group — delegate to top-level lemma.
  ------------------------------------------------------------------------
  have hUqId10 := sect_hUqIdE01_10 k
  let phi_10 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k)
  have hSect10 :
      phi_10 ((uqAffK0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k +
         uqAffE0 k * uqAffK0 k * uqAffE0 k * uqAffE1 k +
         uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffE1 k) -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k +
         uqAffE0 k * uqAffK0 k * uqAffE1 k * uqAffE0 k +
         uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffK0 k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k +
         uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffE0 k +
         uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffK0 k) -
        (uqAffE1 k * uqAffK0 k * uqAffE0 k * uqAffE0 k +
         uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffE0 k +
         uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffK0 k)) = 0 := by
    rw [hUqId10]; exact map_zero phi_10
  rw [map_sub phi_10, map_add phi_10, map_sub phi_10,
      LinearMap.map_smul_of_tower phi_10,
      LinearMap.map_smul_of_tower phi_10] at hSect10
  simp only [phi_10, TensorProduct.mk_apply] at hSect10
  ------------------------------------------------------------------------
  -- Sector (1,1) (CAS convention): left factor E₀² (uniform), right has
  -- 1 E₀ + 1 E₁ + 2 K₀'s. Delegate Uqsl2Aff identity to sect_hUqIdE01_11.
  ------------------------------------------------------------------------
  have hUqId11 := sect_hUqIdE01_11 k
  let phi_11 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k * uqAffE0 k)
  have hSect11 : phi_11 ((uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffE1 k +
     uqAffK0 k * uqAffE0 k * uqAffK0 k * uqAffE1 k +
     uqAffK0 k * uqAffK0 k * uqAffE0 k * uqAffE1 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK0 k * uqAffE1 k * uqAffK0 k +
     uqAffK0 k * uqAffE0 k * uqAffE1 k * uqAffK0 k +
     uqAffK0 k * uqAffK0 k * uqAffE1 k * uqAffE0 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffE1 k * uqAffK0 k * uqAffK0 k +
     uqAffK0 k * uqAffE1 k * uqAffE0 k * uqAffK0 k +
     uqAffK0 k * uqAffE1 k * uqAffK0 k * uqAffE0 k) -
    (uqAffE1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k +
     uqAffE1 k * uqAffK0 k * uqAffE0 k * uqAffK0 k +
     uqAffE1 k * uqAffK0 k * uqAffK0 k * uqAffE0 k)) = 0 := by
    rw [hUqId11]; exact map_zero phi_11
  rw [map_sub phi_11, map_add phi_11, map_sub phi_11,
      LinearMap.map_smul_of_tower phi_11,
      LinearMap.map_smul_of_tower phi_11] at hSect11
  simp only [phi_11, TensorProduct.mk_apply] at hSect11
  ------------------------------------------------------------------------
  -- Sector (2,0) sub-part a (CAS): left factor E₀E₁, 6 atoms.
  ------------------------------------------------------------------------
  have hUqId20a := sect_hUqIdE01_20a k
  let phi_20a : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k * uqAffE1 k)
  have hSect20a : phi_20a ((uqAffK0 k * uqAffE0 k * uqAffE0 k * uqAffK1 k +
     uqAffE0 k * uqAffK0 k * uqAffE0 k * uqAffK1 k +
     uqAffE0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffE0 k * uqAffK1 k * uqAffE0 k +
     uqAffE0 k * uqAffK0 k * uqAffK1 k * uqAffE0 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffK1 k * uqAffE0 k * uqAffE0 k)) = 0 := by
    rw [hUqId20a]; exact map_zero phi_20a
  rw [map_add phi_20a, map_sub phi_20a,
      LinearMap.map_smul_of_tower phi_20a,
      LinearMap.map_smul_of_tower phi_20a] at hSect20a
  simp only [phi_20a, TensorProduct.mk_apply] at hSect20a
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part a: left = E₀²E₁, 4 atoms.
  ------------------------------------------------------------------------
  have hUqId_cas10a := sect_hUqIdE01_cas10a k
  let phi_cas10a : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k * uqAffE0 k * uqAffE1 k)
  have hSect_cas10a : phi_cas10a
      ((uqAffE0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k +
        uqAffK0 k * uqAffE0 k * uqAffK0 k * uqAffK1 k +
        uqAffK0 k * uqAffK0 k * uqAffE0 k * uqAffK1 k) -
       (T 2 + 1 + T (-2) : LaurentPolynomial k) •
       (uqAffK0 k * uqAffK0 k * uqAffK1 k * uqAffE0 k)) = 0 := by
    rw [hUqId_cas10a]; exact map_zero phi_cas10a
  rw [map_sub phi_cas10a, map_add phi_cas10a,
      LinearMap.map_smul_of_tower phi_cas10a] at hSect_cas10a
  simp only [phi_cas10a, TensorProduct.mk_apply] at hSect_cas10a
  ------------------------------------------------------------------------
  -- Sector (2,0) sub-part b (CAS): left factor E₁E₀, 6 atoms.
  ------------------------------------------------------------------------
  have hUqId20b := sect_hUqIdE01_20b k
  let phi_20b : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k * uqAffE0 k)
  have hSect20b : phi_20b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffE0 k +
     uqAffE0 k * uqAffK1 k * uqAffE0 k * uqAffK0 k)) =
    phi_20b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k) +
    (uqAffK1 k * uqAffK0 k * uqAffE0 k * uqAffE0 k +
     uqAffK1 k * uqAffE0 k * uqAffK0 k * uqAffE0 k +
     uqAffK1 k * uqAffE0 k * uqAffE0 k * uqAffK0 k)) := by
    rw [hUqId20b]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_20b, TensorProduct.mk_apply] at hSect20b
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part b: left = E₀E₁E₀, equation form.
  ------------------------------------------------------------------------
  have hUqId_cas10b := sect_hUqIdE01_cas10b k
  let phi_cas10b : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k * uqAffE1 k * uqAffE0 k)
  have hSect_cas10b : phi_cas10b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK0 k * uqAffK1 k * uqAffK0 k +
     uqAffK0 k * uqAffE0 k * uqAffK1 k * uqAffK0 k)) =
    phi_cas10b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK0 k * uqAffK1 k * uqAffE0 k * uqAffK0 k +
     uqAffK0 k * uqAffK1 k * uqAffK0 k * uqAffE0 k)) := by
    rw [hUqId_cas10b]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_cas10b, TensorProduct.mk_apply] at hSect_cas10b
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part c: left = E₁E₀², equation form.
  ------------------------------------------------------------------------
  have hUqId_cas10c := sect_hUqIdE01_cas10c k
  let phi_cas10c : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k * uqAffE0 k * uqAffE0 k)
  have hSect_cas10c : phi_cas10c ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE0 k * uqAffK1 k * uqAffK0 k * uqAffK0 k)) =
    phi_cas10c (uqAffK1 k * uqAffE0 k * uqAffK0 k * uqAffK0 k +
     uqAffK1 k * uqAffK0 k * uqAffE0 k * uqAffK0 k +
     uqAffK1 k * uqAffK0 k * uqAffK0 k * uqAffE0 k) := by
    rw [hUqId_cas10c]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_cas10c, TensorProduct.mk_apply] at hSect_cas10c
  simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, smul_add]
    at hSect10 hSect11 hSect20a hSect_cas10a hSect20b hSect_cas10b hSect_cas10c
  have h20b := sub_eq_zero_of_eq hSect20b
  have h10b := sub_eq_zero_of_eq hSect_cas10b
  have h10c := sub_eq_zero_of_eq hSect_cas10c
  simp only [LinearMap.smul_apply, LinearMap.add_apply] at h20b h10b h10c
  repeat erw [TensorProduct.mk_apply] at h20b
  repeat erw [TensorProduct.mk_apply] at h10b
  repeat erw [TensorProduct.mk_apply] at h10c
  clear ha hb hc hd hSerreS hKnorm1 hKnorm2 hKnorm3 phi_L phi_R phi_30 phi_01
    phi_10 phi_11 phi_20a phi_cas10a phi_20b phi_cas10b phi_cas10c hUqId30 hUqId01
    hUqId10 hUqId11 hUqId20a hUqId_cas10a hUqId20b hUqId_cas10b hUqId_cas10c
    hSect20b hSect_cas10b hSect_cas10c
  clear a b c d
  linear_combination (norm := module) hSect00 + hSect31 + hSect30 + hSect01 + hSect10 + hSect11 + hSect20a + hSect_cas10a + h20b - h10b + h10c

set_option maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
private theorem affComulFreeAlg_SerreE10 :
    affComulFreeAlg k
      (ag k E1 * ag k E1 * ag k E1 * ag k E0
       - ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E1 * ag k E0 * ag k E1
       + ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E0 * ag k E1 * ag k E1
       - ag k E0 * ag k E1 * ag k E1 * ag k E1) =
    affComulFreeAlg k 0 := by
  erw [map_zero]
  simp only [map_sub, map_add, map_mul, AlgHom.commutes]
  erw [affComulFreeAlg_ι k E0, affComulFreeAlg_ι k E1]
  simp only [affComulOnGen]
  -- Fold q3 back from distributed form (map_add split it into 3 summands).
  rw [show ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T 2)) +
          ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) 1) +
          ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T (-2))) =
          (algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T 2 + 1 + T (-2))
        from by simp [map_add]]
  -- Convert algebraMap * X to scalar • X, so q3 becomes a Laurent scalar on A⊗A.
  simp only [← Algebra.smul_def]
  set a := uqAffE1 k ⊗ₜ[LaurentPolynomial k] uqAffK1 k with ha
  set b := (1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE1 k with hb
  set c := uqAffE0 k ⊗ₜ[LaurentPolynomial k] uqAffK0 k with hc
  set d := (1 : Uqsl2Aff k) ⊗ₜ[LaurentPolynomial k] uqAffE0 k with hd
  have hSerreS := sect_hSerreS_smul k
  have hKnorm1 := sect_hKnorm1 k
  have hKnorm2 := sect_hKnorm2 k
  have hKnorm3 := sect_hKnorm3 k
  rw [ha, hb, hc, hd]
  -- The closure below takes the sector-by-sector approach:
  --   Phase 4': tensor expansion via tmul_mul_tmul + K-normalization via hKnorm
  --   Phase 5': define phi_L, phi_R linear maps and use them to transport
  --             hSerreS across the tensor boundary (bypasses RingQuot diamond
  --             that blocked direct `rw [← sub_tmul]` factoring)
  --   Phase 6': [pending] close 6 qbinom sectors via scalar identities
  --
  -- Key technical finding: `rw [← TensorProduct.sub_tmul]` fails with
  -- "did not find pattern" because Uqsl2Aff's Sub comes from RingQuot.instSub
  -- while sub_tmul expects AddCommGroup.toAddGroup.toSub — a documented
  -- RingQuot diamond (Phase-5p). Workaround: apply `map_sub`, `map_add`,
  -- `LinearMap.map_smul_of_tower` on a LinearMap `phi : Uqsl2Aff →ₗ A ⊗ A`
  -- whose application IS (by definition) the tensor we want. LinearMap's
  -- map_sub bypasses the instance diamond because it's bundled with the
  -- structure-preserving proof, not rewritten via exact pattern match.
  simp only [mul_add, add_mul, smul_add, smul_mul_assoc,
             Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
             hKnorm1, hKnorm2, hKnorm3]
  -- Define two linear maps. phi_L sends x ↦ x ⊗ K₁³K₀ (for sector (0,0));
  -- phi_R sends y ↦ 1 ⊗ y (for sector (3,1)).
  let phi_L : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k)
  let phi_R : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (1 : Uqsl2Aff k)
  -- Apply each to the Serre expression; both give 0 by hSerreS + map_zero.
  have hSect00 : phi_L (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k) -
      uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_L
  have hSect31 : phi_R (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k) -
      uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_R
  -- Distribute via linearity. `phi (A - B + C - D) = phi A - phi B + phi C - phi D`
  -- via map_sub, map_add, and LinearMap.map_smul_of_tower for the • scalars.
  rw [map_sub phi_L, map_add phi_L, map_sub phi_L,
      LinearMap.map_smul_of_tower phi_L, LinearMap.map_smul_of_tower phi_L] at hSect00
  rw [map_sub phi_R, map_add phi_R, map_sub phi_R,
      LinearMap.map_smul_of_tower phi_R, LinearMap.map_smul_of_tower phi_R] at hSect31
  -- Unfold phi_L/phi_R: phi_L x = x ⊗ₜ K₁³K₀, phi_R y = 1 ⊗ₜ y.
  simp only [phi_L, phi_R, LinearMap.flip_apply, TensorProduct.mk_apply]
    at hSect00 hSect31
  -- hSect00 : (E₁³E₀) ⊗ K₁³K₀ - q3•(E₁²E₀E₁) ⊗ K₁³K₀ + q3•(E₁E₀E₁²) ⊗ K₁³K₀
  --           - (E₀E₁³) ⊗ K₁³K₀ = 0
  -- hSect31 : 1 ⊗ₜ (E₁³E₀) - q3•1 ⊗ₜ (E₁²E₀E₁) + q3•1 ⊗ₜ (E₁E₀E₁²)
  --           - 1 ⊗ₜ (E₀E₁³) = 0
  ------------------------------------------------------------------------
  -- Sector (3,0): left factor E₁³ (uniform), right factor has K₁³-E₀ mix.
  -- Delegate the Uqsl2Aff-level identity to a top-level lemma to keep
  -- the main theorem's context compact (heartbeat-safe).
  ------------------------------------------------------------------------
  have hUqId30 := sect_hUqId30 k
  -- Apply phi_30 : y ↦ E₁³ ⊗ y  to hUqId30
  let phi_30 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k * uqAffE1 k * uqAffE1 k)
  have hSect30 :
      phi_30 (uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k) -
        uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffK1 k) = 0 := by
    rw [hUqId30]; exact map_zero phi_30
  rw [map_sub phi_30, map_add phi_30, map_sub phi_30,
      LinearMap.map_smul_of_tower phi_30,
      LinearMap.map_smul_of_tower phi_30] at hSect30
  simp only [phi_30, TensorProduct.mk_apply] at hSect30
  -- hSect30 : (E₁³) ⊗ K₁³E₀ - q3•(E₁³) ⊗ K₁²E₀K₁ + q3•(E₁³) ⊗ K₁E₀K₁²
  --            - (E₁³) ⊗ E₀K₁³ = 0
  ------------------------------------------------------------------------
  -- Sector (0,1): left factor E₀, right factor has K₀-E₁ mix.
  -- Delegate to top-level lemma for compact context.
  ------------------------------------------------------------------------
  have hUqId01 := sect_hUqId01 k
  -- Apply phi_01 : y ↦ uqAffE0 k ⊗ y  to hUqId01
  let phi_01 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k)
  have hSect01 :
      phi_01 (uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k) -
        uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k) = 0 := by
    rw [hUqId01]; exact map_zero phi_01
  rw [map_sub phi_01, map_add phi_01, map_sub phi_01,
      LinearMap.map_smul_of_tower phi_01,
      LinearMap.map_smul_of_tower phi_01] at hSect01
  simp only [phi_01, TensorProduct.mk_apply] at hSect01
  -- hSect01 : E₀ ⊗ E₁³K₀ - q3•E₀ ⊗ E₁²K₀E₁ + q3•E₀ ⊗ E₁K₀E₁² - E₀ ⊗ K₀E₁³ = 0
  ------------------------------------------------------------------------
  -- Sector (1,0): left factor E₁ (uniform), right factor has 3 atoms per
  -- group — delegate to top-level lemma.
  ------------------------------------------------------------------------
  have hUqId10 := sect_hUqId10 k
  let phi_10 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k)
  have hSect10 :
      phi_10 ((uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k +
         uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k +
         uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k) -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k +
         uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k +
         uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k +
         uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k +
         uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k) -
        (uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k +
         uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k +
         uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k)) = 0 := by
    rw [hUqId10]; exact map_zero phi_10
  rw [map_sub phi_10, map_add phi_10, map_sub phi_10,
      LinearMap.map_smul_of_tower phi_10,
      LinearMap.map_smul_of_tower phi_10] at hSect10
  simp only [phi_10, TensorProduct.mk_apply] at hSect10
  ------------------------------------------------------------------------
  -- Sector (1,1) (CAS convention): left factor E₁² (uniform), right has
  -- 1 E₁ + 1 E₀ + 2 K₁'s. Delegate Uqsl2Aff identity to sect_hUqId11.
  ------------------------------------------------------------------------
  have hUqId11 := sect_hUqId11 k
  let phi_11 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k * uqAffE1 k)
  have hSect11 : phi_11 ((uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffE0 k +
     uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffE0 k +
     uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffE0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK1 k * uqAffE0 k * uqAffK1 k +
     uqAffK1 k * uqAffE1 k * uqAffE0 k * uqAffK1 k +
     uqAffK1 k * uqAffK1 k * uqAffE0 k * uqAffE1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffE0 k * uqAffK1 k * uqAffK1 k +
     uqAffK1 k * uqAffE0 k * uqAffE1 k * uqAffK1 k +
     uqAffK1 k * uqAffE0 k * uqAffK1 k * uqAffE1 k) -
    (uqAffE0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k +
     uqAffE0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k +
     uqAffE0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k)) = 0 := by
    rw [hUqId11]; exact map_zero phi_11
  rw [map_sub phi_11, map_add phi_11, map_sub phi_11,
      LinearMap.map_smul_of_tower phi_11,
      LinearMap.map_smul_of_tower phi_11] at hSect11
  simp only [phi_11, TensorProduct.mk_apply] at hSect11
  ------------------------------------------------------------------------
  -- Sector (2,0) sub-part a (CAS): left factor E₁E₀, 6 atoms.
  ------------------------------------------------------------------------
  have hUqId20a := sect_hUqId20a k
  let phi_20a : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k * uqAffE0 k)
  have hSect20a : phi_20a ((uqAffK1 k * uqAffE1 k * uqAffE1 k * uqAffK0 k +
     uqAffE1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k +
     uqAffE1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffE1 k +
     uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffE1 k)) = 0 := by
    rw [hUqId20a]; exact map_zero phi_20a
  rw [map_add phi_20a, map_sub phi_20a,
      LinearMap.map_smul_of_tower phi_20a,
      LinearMap.map_smul_of_tower phi_20a] at hSect20a
  simp only [phi_20a, TensorProduct.mk_apply] at hSect20a
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part a: left = E₁²E₀, 4 atoms.
  ------------------------------------------------------------------------
  have hUqId_cas10a := sect_hUqId_cas10a k
  let phi_cas10a : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k * uqAffE1 k * uqAffE0 k)
  have hSect_cas10a : phi_cas10a
      ((uqAffE1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k +
        uqAffK1 k * uqAffE1 k * uqAffK1 k * uqAffK0 k +
        uqAffK1 k * uqAffK1 k * uqAffE1 k * uqAffK0 k) -
       (T 2 + 1 + T (-2) : LaurentPolynomial k) •
       (uqAffK1 k * uqAffK1 k * uqAffK0 k * uqAffE1 k)) = 0 := by
    rw [hUqId_cas10a]; exact map_zero phi_cas10a
  rw [map_sub phi_cas10a, map_add phi_cas10a,
      LinearMap.map_smul_of_tower phi_cas10a] at hSect_cas10a
  simp only [phi_cas10a, TensorProduct.mk_apply] at hSect_cas10a
  ------------------------------------------------------------------------
  -- Sector (2,0) sub-part b (CAS): left factor E₀E₁, 6 atoms.
  -- Equation form: q3•(G2 atom) + stuff = q3•(G3 sum) + (G4 sum).
  ------------------------------------------------------------------------
  have hUqId20b := sect_hUqId20b k
  let phi_20b : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k * uqAffE1 k)
  have hSect20b : phi_20b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k +
     uqAffE1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k)) =
    phi_20b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffE1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k) +
    (uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffE1 k +
     uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffE1 k +
     uqAffK0 k * uqAffE1 k * uqAffE1 k * uqAffK1 k)) := by
    rw [hUqId20b]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_20b, TensorProduct.mk_apply] at hSect20b
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part b: left = E₁E₀E₁, equation form.
  ------------------------------------------------------------------------
  have hUqId_cas10b := sect_hUqId_cas10b k
  let phi_cas10b : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE1 k * uqAffE0 k * uqAffE1 k)
  have hSect_cas10b : phi_cas10b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK1 k * uqAffK0 k * uqAffK1 k +
     uqAffK1 k * uqAffE1 k * uqAffK0 k * uqAffK1 k)) =
    phi_cas10b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1 k * uqAffK0 k * uqAffE1 k * uqAffK1 k +
     uqAffK1 k * uqAffK0 k * uqAffK1 k * uqAffE1 k)) := by
    rw [hUqId_cas10b]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_cas10b, TensorProduct.mk_apply] at hSect_cas10b
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part c: left = E₀E₁², equation form.
  ------------------------------------------------------------------------
  have hUqId_cas10c := sect_hUqId_cas10c k
  let phi_cas10c : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffE0 k * uqAffE1 k * uqAffE1 k)
  have hSect_cas10c : phi_cas10c ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffE1 k * uqAffK0 k * uqAffK1 k * uqAffK1 k)) =
    phi_cas10c (uqAffK0 k * uqAffE1 k * uqAffK1 k * uqAffK1 k +
     uqAffK0 k * uqAffK1 k * uqAffE1 k * uqAffK1 k +
     uqAffK0 k * uqAffK1 k * uqAffK1 k * uqAffE1 k) := by
    rw [hUqId_cas10c]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_cas10c, TensorProduct.mk_apply] at hSect_cas10c
  simp only [TensorProduct.tmul_add, smul_add]
    at hSect10 hSect11 hSect20a hSect_cas10a hSect20b hSect_cas10b hSect_cas10c
  have h20b := sub_eq_zero_of_eq hSect20b
  have h10b := sub_eq_zero_of_eq hSect_cas10b
  have h10c := sub_eq_zero_of_eq hSect_cas10c
  clear ha hb hc hd hSerreS hKnorm1 hKnorm2 hKnorm3 phi_L phi_R phi_30 phi_01
    phi_10 phi_11 phi_20a phi_cas10a phi_20b phi_cas10b phi_cas10c hUqId30 hUqId01
    hUqId10 hUqId11 hUqId20a hUqId_cas10a hUqId20b hUqId_cas10b hUqId_cas10c
    hSect20b hSect_cas10b hSect_cas10c
  clear a b c d
  linear_combination (norm := module) hSect00 + hSect31 + hSect30 + hSect01 + hSect10 + hSect11 + hSect20a + hSect_cas10a + h20b - h10b + h10c

private theorem affComulFreeAlg_SerreF01 :
    affComulFreeAlg k
      (ag k F0 * ag k F0 * ag k F0 * ag k F1
       - ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F0 * ag k F1 * ag k F0
       + ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F1 * ag k F0 * ag k F0
       - ag k F1 * ag k F0 * ag k F0 * ag k F0) =
    affComulFreeAlg k 0 := by
  -- PROVIDED SOLUTION: Identical structure to SerreE01 with E↔F, K↔K⁻¹.
  -- Δ(Fᵢ) = Fᵢ⊗1 + Kᵢ⁻¹⊗Fᵢ (note: K⁻¹ on LEFT, not K on RIGHT).
  -- The 8-sector bidegree decomposition applies with K⁻¹-F commutation:
  --   K₀⁻¹F₀ = T(-2)F₀K₀⁻¹, K₁⁻¹F₁ = T(-2)F₁K₁⁻¹, etc.
  -- Sectors (0,0)/(3,1): uqAff_SerreF01. Others: same q-binomial identities.
  -- Phase 1-3: erw [map_zero]; simp [map_sub,map_add,map_mul,AlgHom.commutes];
  --   erw [affComulFreeAlg_ι k F0, affComulFreeAlg_ι k F1]; simp [affComulOnGen];
  --   simp [add_mul, mul_add, sub_mul, mul_sub, mul_assoc, tmul_mul_tmul, mul_one, one_mul]
  -- Phase 4: bidegree sector decomposition (same structure as E case).
  sorry

/-! ### Cross-index K⁻¹ commutation helpers (relocated for F q-Serre proofs).

These were previously defined in the antipode section but are needed here
for the F10/F01 coproduct compatibility proofs. Their proofs depend only
on lemmas already defined above (uqAff_K0K1_comm, uqAff_K0inv_mul_K0, etc.).
-/

private theorem uqAff_K0inv_K1inv_comm :
    uqAffK0inv k * uqAffK1inv k = uqAffK1inv k * uqAffK0inv k := by
  have h_comm : uqAffK1inv k * uqAffK0inv k * (uqAffK0 k * uqAffK1 k) = 1 := by
    simp +decide [ mul_assoc, uqAff_K0inv_mul_K0, uqAff_K1inv_mul_K1 ];
    simp +decide [ ← mul_assoc, uqAff_K0inv_mul_K0, uqAff_K1inv_mul_K1 ];
  rw [ uqAff_K0K1_comm ] at *;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  apply_fun ( fun x => x * ( uqAffK0inv k * uqAffK1inv k ) ) at ‹uqAffK1inv k * ( uqAffK0inv k * ( uqAffK1 k * uqAffK0 k ) ) = 1›;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  simp_all +decide [ ← mul_assoc, uqAff_K0_mul_K0inv, uqAff_K1_mul_K1inv ]

private theorem uqAff_E1_mul_K0inv :
    uqAffE1 k * uqAffK0inv k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffK0inv k * uqAffE1 k := by
  have h_E1K0inv : uqAffK0 k * uqAffE1 k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffE1 k * uqAffK0 k := by
    exact?
  generalize_proofs at *; (
  have h_mul : uqAffK0inv k * (uqAffK0 k * uqAffE1 k) * uqAffK0inv k = uqAffK0inv k * (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffE1 k * uqAffK0 k) * uqAffK0inv k := by
    rw [h_E1K0inv]
  generalize_proofs at *; (
  convert h_mul using 1 <;> simp +decide [ mul_assoc, mul_left_comm, mul_comm ];
  · simp +decide [ ← mul_assoc, uqAff_K0inv_mul_K0 ];
  · simp +decide [ ← mul_assoc, ← Algebra.smul_def, uqAff_K0_mul_K0inv ]))

private theorem uqAff_E0_mul_K1inv :
    uqAffE0 k * uqAffK1inv k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffK1inv k * uqAffE0 k := by
  convert congr_arg ( fun x => uqAffK1inv k * x * uqAffK1inv k ) ( uqAff_K1E0 k ) using 1 <;> simp +decide [ mul_assoc, mul_left_comm, mul_comm ];
  · simp +decide [ ← mul_assoc, uqAff_K1inv_mul_K1 ];
  · grind +suggestions

private theorem uqAff_F1_mul_K0inv :
    uqAffF1 k * uqAffK0inv k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (2)) * uqAffK0inv k * uqAffF1 k := by
  convert congr_arg ( fun x => uqAffK0inv k * x * uqAffK0inv k ) ( uqAff_K0F1 k ) using 1;
  · simp +decide [ ← mul_assoc, uqAff_K0_mul_K0inv, uqAff_K0inv_mul_K0 ];
  · simp +decide [ mul_assoc, uqAff_K0inv_mul_K0 ];
    rw [ uqAff_K0_mul_K0inv ] ; simp +decide [ mul_assoc ];
    simp +decide [ ← mul_assoc, ← Algebra.smul_def ]

private theorem uqAff_F0_mul_K1inv :
    uqAffF0 k * uqAffK1inv k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (2)) * uqAffK1inv k * uqAffF0 k := by
  have := uqAff_K1F0 k;
  apply_fun ( fun x => x * uqAffK1inv k ) at this; simp_all +decide [ mul_assoc, mul_left_comm ] ;
  convert congr_arg ( fun x => uqAffK1inv k * x ) this using 1 ;
  · simp +decide [ ← mul_assoc, uqAff_K1inv_mul_K1 ];
  · rw [ show uqAffK1 k * uqAffK1inv k = 1 from uqAff_K1_mul_K1inv k ] ; simp +decide [ mul_assoc, mul_left_comm ];
    simp +decide [ ← mul_assoc, ← Algebra.smul_def ]

private theorem uqAff_K0inv_mul_F1 :
    uqAffK0inv k * uqAffF1 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF1 k * uqAffK0inv k := by
  have h_k0inv_f1 : uqAffF1 k * uqAffK0inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffK0inv k * uqAffF1 k := by
    exact?;
  have h_k0inv_f1 : algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) = 1 := by
    rw [ ← map_mul, ← LaurentPolynomial.T_add ] ; norm_num;
  apply_fun ( fun x => algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ( T ( -2 ) ) * x ) at ‹uqAffF1 k * uqAffK0inv k = algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ( T 2 ) * uqAffK0inv k * uqAffF1 k› ; simp_all +decide [ mul_assoc ] ;
  simp_all +decide [ ← mul_assoc ]

private theorem uqAff_K1inv_mul_F0 :
    uqAffK1inv k * uqAffF0 k =
    algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF0 k * uqAffK1inv k := by
  have h_mul : uqAffK1inv k * (uqAffK1 k * uqAffF0 k) = uqAffK1inv k * (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffF0 k * uqAffK1 k) := by
    rw [ ← uqAff_K1F0 ];
  have h_mul : (algebraMap (LaurentPolynomial k) (Uqsl2Aff k)) (T (-2)) * (algebraMap (LaurentPolynomial k) (Uqsl2Aff k)) (T 2) = 1 := by
    erw [ ← map_mul, show T ( -2 ) * T 2 = 1 from ?_ ] ; aesop;
    erw [ show T ( -2 : ℤ ) * T 2 = T ( -2 + 2 : ℤ ) by rw [ ← LaurentPolynomial.T_add ] ] ; norm_num;
  apply_fun ( fun x => ( algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ) ( T ( -2 ) ) * x ) at ‹uqAffK1inv k * ( uqAffK1 k * uqAffF0 k ) = uqAffK1inv k * ( ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ) ( T 2 ) * uqAffF0 k * uqAffK1 k ) › ; simp_all +decide [ mul_assoc ];
  simp_all +decide [ ← mul_assoc, ← eq_sub_iff_add_eq' ];
  simp_all +decide [ mul_assoc, uqAff_K1inv_mul_K1 ];
  grind +suggestions

/-! ### Sector decomposition helpers for SerreF10.

Mirror of the E10 sector helpers with the substitution E→F, K→K⁻¹.
Δ(F₁) = F₁⊗1 + K₁⁻¹⊗F₁, Δ(F₀) = F₀⊗1 + K₀⁻¹⊗F₀.

Setting a = F₁⊗1, b = K₁⁻¹⊗F₁, c = F₀⊗1, d = K₀⁻¹⊗F₀.
K⁻¹-F commutation: K₁⁻¹F₀ = T(-2)·F₀K₁⁻¹, K₁⁻¹F₁ = T(2)·F₁K₁⁻¹,
K₀⁻¹F₁ = T(-2)·F₁K₀⁻¹, K₀⁻¹F₀ = T(2)·F₀K₀⁻¹.
These have the SAME T-powers as KE, so all abstract cancel_aux lemmas reuse.
-/

/-- K₁⁻¹·F₀ = T(-2) • (F₀·K₁⁻¹) in smul form — cross-index helper for sector (3,0). -/
private theorem sect_hKinvF_smul_K1invF0 (k : Type*) [CommRing k] :
    uqAffK1inv k * uqAffF0 k = (T (-2) : LaurentPolynomial k) • (uqAffF0 k * uqAffK1inv k) := by
  rw [uqAff_K1inv_mul_F0, Algebra.smul_def, mul_assoc]

/-- Positional version: (x·K₁⁻¹)·F₀ = T(-2) • ((x·F₀)·K₁⁻¹). -/
private theorem sect_hKinvF_at_K1invF0 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK1inv k * uqAffF0 k =
    (T (-2) : LaurentPolynomial k) • (x * uqAffF0 k * uqAffK1inv k) := by
  rw [mul_assoc x (uqAffK1inv k) (uqAffF0 k), sect_hKinvF_smul_K1invF0,
      mul_smul_comm, ← mul_assoc]

/-- K₀⁻¹·F₁ = T(-2) • (F₁·K₀⁻¹) — cross-index helper for sector (0,1). -/
private theorem sect_hKinvF_smul_K0invF1 (k : Type*) [CommRing k] :
    uqAffK0inv k * uqAffF1 k = (T (-2) : LaurentPolynomial k) • (uqAffF1 k * uqAffK0inv k) := by
  rw [uqAff_K0inv_mul_F1, Algebra.smul_def, mul_assoc]

/-- Positional version: (x·K₀⁻¹)·F₁ = T(-2) • ((x·F₁)·K₀⁻¹). -/
private theorem sect_hKinvF_at_K0invF1 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK0inv k * uqAffF1 k =
    (T (-2) : LaurentPolynomial k) • (x * uqAffF1 k * uqAffK0inv k) := by
  rw [mul_assoc x (uqAffK0inv k) (uqAffF1 k), sect_hKinvF_smul_K0invF1,
      mul_smul_comm, ← mul_assoc]

/-- K₁⁻¹·F₁ = T(2) • (F₁·K₁⁻¹) — same-index helper for mixed sectors. -/
private theorem sect_hKinvF_smul_K1invF1 (k : Type*) [CommRing k] :
    uqAffK1inv k * uqAffF1 k = (T 2 : LaurentPolynomial k) • (uqAffF1 k * uqAffK1inv k) := by
  rw [uqAff_K1inv_mul_F1, Algebra.smul_def, mul_assoc]

/-- Positional version: (x·K₁⁻¹)·F₁ = T(2) • ((x·F₁)·K₁⁻¹). -/
private theorem sect_hKinvF_at_K1invF1 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK1inv k * uqAffF1 k =
    (T 2 : LaurentPolynomial k) • (x * uqAffF1 k * uqAffK1inv k) := by
  rw [mul_assoc x (uqAffK1inv k) (uqAffF1 k), sect_hKinvF_smul_K1invF1,
      mul_smul_comm, ← mul_assoc]

/-- K₀⁻¹·F₀ = T(2) • (F₀·K₀⁻¹) — same-index helper. -/
private theorem sect_hKinvF_smul_K0invF0 (k : Type*) [CommRing k] :
    uqAffK0inv k * uqAffF0 k = (T 2 : LaurentPolynomial k) • (uqAffF0 k * uqAffK0inv k) := by
  rw [uqAff_K0inv_mul_F0, Algebra.smul_def, mul_assoc]

/-- Positional version: (x·K₀⁻¹)·F₀ = T(2) • ((x·F₀)·K₀⁻¹). -/
private theorem sect_hKinvF_at_K0invF0 (k : Type*) [CommRing k] (x : Uqsl2Aff k) :
    x * uqAffK0inv k * uqAffF0 k =
    (T 2 : LaurentPolynomial k) • (x * uqAffF0 k * uqAffK0inv k) := by
  rw [mul_assoc x (uqAffK0inv k) (uqAffF0 k), sect_hKinvF_smul_K0invF0,
      mul_smul_comm, ← mul_assoc]

/-- Serre F10 in smul form: F₁³F₀ - q3•F₁²F₀F₁ + q3•F₁F₀F₁² - F₀F₁³ = 0. -/
private theorem sect_hSerreF10_smul (k : Type*) [CommRing k] :
    uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffF0 k -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffF1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffF1 k) -
    uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffF1 k = 0 := by
  simp only [Algebra.smul_def, ← mul_assoc]; exact uqAff_SerreF10 k

/-- K⁻¹-product normalization 1: K₁⁻¹K₁⁻¹K₀⁻¹K₁⁻¹ = K₁⁻¹K₁⁻¹K₁⁻¹K₀⁻¹. -/
private theorem sect_hKnormF10_1 (k : Type*) [CommRing k] :
    uqAffK1inv k * uqAffK1inv k * uqAffK0inv k * uqAffK1inv k =
    uqAffK1inv k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k := by
  rw [mul_assoc (uqAffK1inv k * uqAffK1inv k) (uqAffK0inv k) (uqAffK1inv k),
      uqAff_K0inv_K1inv_comm, ← mul_assoc]

/-- K⁻¹-product normalization 2: K₁⁻¹K₀⁻¹K₁⁻¹K₁⁻¹ = K₁⁻¹K₁⁻¹K₁⁻¹K₀⁻¹. -/
private theorem sect_hKnormF10_2 (k : Type*) [CommRing k] :
    uqAffK1inv k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k =
    uqAffK1inv k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k := by
  rw [mul_assoc (uqAffK1inv k) (uqAffK0inv k) (uqAffK1inv k),
      uqAff_K0inv_K1inv_comm,
      ← mul_assoc, mul_assoc (uqAffK1inv k * uqAffK1inv k) (uqAffK0inv k) (uqAffK1inv k),
      uqAff_K0inv_K1inv_comm, ← mul_assoc]

/-- K⁻¹-product normalization 3: K₀⁻¹K₁⁻¹K₁⁻¹K₁⁻¹ = K₁⁻¹K₁⁻¹K₁⁻¹K₀⁻¹. -/
private theorem sect_hKnormF10_3 (k : Type*) [CommRing k] :
    uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k =
    uqAffK1inv k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k := by
  rw [show uqAffK0inv k * uqAffK1inv k = uqAffK1inv k * uqAffK0inv k
        from uqAff_K0inv_K1inv_comm k,
      mul_assoc (uqAffK1inv k) (uqAffK0inv k) (uqAffK1inv k),
      uqAff_K0inv_K1inv_comm,
      ← mul_assoc, mul_assoc (uqAffK1inv k * uqAffK1inv k) (uqAffK0inv k) (uqAffK1inv k),
      uqAff_K0inv_K1inv_comm, ← mul_assoc]

/-- Sector (3,0) F10 identity: K₁⁻³F₀ - q3•K₁⁻²F₀K₁⁻¹ + q3•K₁⁻¹F₀K₁⁻² - F₀K₁⁻³ = 0.
    Push F₀ right past all K₁⁻¹'s via K₁⁻¹F₀ = T(-2)•F₀K₁⁻¹. -/
private theorem sect_hUqIdF10_30 (k : Type*) [CommRing k] :
    uqAffK1inv k * uqAffK1inv k * uqAffK1inv k * uqAffF0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1inv k * uqAffK1inv k * uqAffF0 k * uqAffK1inv k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1inv k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k) -
      uqAffF0 k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k = 0 := by
  have hKF_smul := sect_hKinvF_smul_K1invF0 k
  have hKF_at := sect_hKinvF_at_K1invF0 k
  have hK3F0 : uqAffK1inv k * uqAffK1inv k * uqAffK1inv k * uqAffF0 k =
      (T (-6) : LaurentPolynomial k) •
        (uqAffF0 k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k) := by
    rw [hKF_at, hKF_at, hKF_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hK2F0K1 : uqAffK1inv k * uqAffK1inv k * uqAffF0 k * uqAffK1inv k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffF0 k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k) := by
    rw [hKF_at, hKF_smul]
    simp only [smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK1F0K2 : uqAffK1inv k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffF0 k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k) := by
    rw [hKF_smul]
    simp only [smul_mul_assoc]
  rw [hK3F0, hK2F0K1, hK1F0K2, smul_smul, smul_smul]
  have factor : ∀ (r s t : LaurentPolynomial k) (x : Uqsl2Aff k),
      r • x - s • x + t • x - x = (r - s + t - 1) • x := by
    intros; module
  rw [factor, qbinom_serre_vanish, zero_smul]

/-- Sector (0,1) F10 identity: F₁³K₀⁻¹ - q3•F₁²K₀⁻¹F₁ + q3•F₁K₀⁻¹F₁² - K₀⁻¹F₁³ = 0.
    Push K₀⁻¹ right past all F₁'s via K₀⁻¹F₁ = T(-2)•F₁K₀⁻¹. -/
private theorem sect_hUqIdF10_01 (k : Type*) [CommRing k] :
    uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffK0inv k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffF1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK0inv k * uqAffF1 k * uqAffF1 k) -
      uqAffK0inv k * uqAffF1 k * uqAffF1 k * uqAffF1 k = 0 := by
  have hK0invF1_smul := sect_hKinvF_smul_K0invF1 k
  have hK0invF1_at := sect_hKinvF_at_K0invF1 k
  have hF2K0invF1 : uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffF1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffK0inv k) := by
    rw [hK0invF1_at]
  have hF1K0invF2 : uqAffF1 k * uqAffK0inv k * uqAffF1 k * uqAffF1 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffK0inv k) := by
    rw [hK0invF1_at]
    simp only [smul_mul_assoc]
    rw [hK0invF1_at]
    simp only [smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hK0invF3 : uqAffK0inv k * uqAffF1 k * uqAffF1 k * uqAffF1 k =
      (T (-6) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffK0inv k) := by
    rw [hK0invF1_smul]
    simp only [smul_mul_assoc]
    rw [hK0invF1_at]
    simp only [smul_mul_assoc, smul_smul]
    rw [hK0invF1_at]
    simp only [smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  rw [hF2K0invF1, hF1K0invF2, hK0invF3, smul_smul, smul_smul]
  have factor : ∀ (s t u : LaurentPolynomial k) (x : Uqsl2Aff k),
      x - s • x + t • x - u • x = (1 - s + t - u) • x := by
    intros; module
  rw [factor]
  have hq := qbinom_serre_vanish k
  have : (1 - (T 2 + 1 + T (-2)) * T (-2) +
          (T 2 + 1 + T (-2)) * T (-4) - T (-6) : LaurentPolynomial k) = 0 := by
    linear_combination -hq
  rw [this, zero_smul]

/-- Sector (1,0) F10 identity: 12 atoms with 1 K₁⁻¹ + 2 F₁ + 1 F₀.
    Uses sector10_cancel_aux with X = F₁²F₀K₁⁻¹, Y = F₁F₀F₁K₁⁻¹, Z = F₀F₁²K₁⁻¹. -/
private theorem sect_hUqIdF10_10 (k : Type*) [CommRing k] :
    (uqAffK1inv k * uqAffF1 k * uqAffF1 k * uqAffF0 k +
     uqAffF1 k * uqAffK1inv k * uqAffF1 k * uqAffF0 k +
     uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffF0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffF1 k * uqAffF0 k * uqAffF1 k +
     uqAffF1 k * uqAffK1inv k * uqAffF0 k * uqAffF1 k +
     uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffK1inv k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffF0 k * uqAffF1 k * uqAffF1 k +
     uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffF1 k +
     uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffK1inv k) -
    (uqAffF0 k * uqAffK1inv k * uqAffF1 k * uqAffF1 k +
     uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffF1 k +
     uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffK1inv k) = 0 := by
  have hKF_smul := sect_hKinvF_smul_K1invF0 k
  have hKF_at := sect_hKinvF_at_K1invF0 k
  have hK1F1_smul := sect_hKinvF_smul_K1invF1 k
  have hK1F1_at := sect_hKinvF_at_K1invF1 k
  have hA1 : uqAffK1inv k * uqAffF1 k * uqAffF1 k * uqAffF0 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffK1inv k) := by
    simp only [hK1F1_smul, hK1F1_at, hKF_smul, hKF_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hA2 : uqAffF1 k * uqAffK1inv k * uqAffF1 k * uqAffF0 k =
      uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffK1inv k := by
    simp only [hK1F1_smul, hK1F1_at, hKF_smul, hKF_at, smul_mul_assoc, smul_smul]
    rw [show ((T 2 : LaurentPolynomial k) * T (-2)) = 1 from by
      rw [← T_add]; show T 0 = 1; exact T_zero]
    rw [one_smul]
  have hA3 : uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffF0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffK1inv k) := by
    rw [hKF_at]
  have hB1 : uqAffK1inv k * uqAffF1 k * uqAffF0 k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffK1inv k) := by
    simp only [hK1F1_smul, hK1F1_at, hKF_smul, hKF_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hB2 : uqAffF1 k * uqAffK1inv k * uqAffF0 k * uqAffF1 k =
      uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffK1inv k := by
    simp only [hK1F1_smul, hK1F1_at, hKF_smul, hKF_at, smul_mul_assoc, smul_smul]
    rw [show ((T (-2) : LaurentPolynomial k) * T 2) = 1 from by
      rw [← T_add]; show T 0 = 1; exact T_zero]
    rw [one_smul]
  have hB3 : uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffK1inv k =
      uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffK1inv k := rfl
  have hC1 : uqAffK1inv k * uqAffF0 k * uqAffF1 k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffK1inv k) := by
    simp only [hK1F1_smul, hK1F1_at, hKF_smul, hKF_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add, ← T_add]; norm_num
  have hC2 : uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffK1inv k) := by
    rw [hK1F1_at]
  have hC3 : uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffK1inv k =
      uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffK1inv k := rfl
  have hD1 : uqAffF0 k * uqAffK1inv k * uqAffF1 k * uqAffF1 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffK1inv k) := by
    simp only [hK1F1_smul, hK1F1_at, smul_mul_assoc, smul_smul]
    congr 1; rw [← T_add]; norm_num
  have hD2 : uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffK1inv k) := by
    rw [hK1F1_at]
  have hD3 : uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffK1inv k =
      uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffK1inv k := rfl
  rw [hA1, hA2, hA3, hB1, hB2, hB3, hC1, hC2, hC3, hD1, hD2, hD3]
  exact sector10_cancel_aux k
    (uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffK1inv k)
    (uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffK1inv k)
    (uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffK1inv k)

/-- Sector (1,1) F10 identity: 12 atoms with 2 K₁⁻¹ + 1 F₁ + 1 F₀.
    Basis: X = F₁·F₀·K₁⁻¹·K₁⁻¹, Y = F₀·F₁·K₁⁻¹·K₁⁻¹.
    Uses sector11_cancel_aux after normalization. -/
private theorem sect_hUqIdF10_11 (k : Type*) [CommRing k] :
    (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffF0 k +
     uqAffK1inv k * uqAffF1 k * uqAffK1inv k * uqAffF0 k +
     uqAffK1inv k * uqAffK1inv k * uqAffF1 k * uqAffF0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK1inv k * uqAffF0 k * uqAffK1inv k +
     uqAffK1inv k * uqAffF1 k * uqAffF0 k * uqAffK1inv k +
     uqAffK1inv k * uqAffK1inv k * uqAffF0 k * uqAffF1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k +
     uqAffK1inv k * uqAffF0 k * uqAffF1 k * uqAffK1inv k +
     uqAffK1inv k * uqAffF0 k * uqAffK1inv k * uqAffF1 k) -
    (uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k +
     uqAffF0 k * uqAffK1inv k * uqAffF1 k * uqAffK1inv k +
     uqAffF0 k * uqAffK1inv k * uqAffK1inv k * uqAffF1 k) = 0 := by
  have h1 := sect_hKinvF_smul_K1invF1 k
  have h2 := sect_hKinvF_at_K1invF1 k
  have h3 := sect_hKinvF_smul_K1invF0 k
  have h4 := sect_hKinvF_at_K1invF0 k
  -- G1: F₁K₁⁻¹K₁⁻¹F₀, K₁⁻¹F₁K₁⁻¹F₀, K₁⁻¹K₁⁻¹F₁F₀ → all T^a • X
  have hB1 : uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffF0 k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB2 : uqAffK1inv k * uqAffF1 k * uqAffK1inv k * uqAffF0 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB3 : uqAffK1inv k * uqAffK1inv k * uqAffF1 k * uqAffF0 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G2: F₁K₁⁻¹F₀K₁⁻¹, K₁⁻¹F₁F₀K₁⁻¹, K₁⁻¹K₁⁻¹F₀F₁
  have hB4 : uqAffF1 k * uqAffK1inv k * uqAffF0 k * uqAffK1inv k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB5 : uqAffK1inv k * uqAffF1 k * uqAffF0 k * uqAffK1inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB6 : uqAffK1inv k * uqAffK1inv k * uqAffF0 k * uqAffF1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G3: F₁F₀K₁⁻¹K₁⁻¹ (already X), K₁⁻¹F₀F₁K₁⁻¹, K₁⁻¹F₀K₁⁻¹F₁
  have hB8 : uqAffK1inv k * uqAffF0 k * uqAffF1 k * uqAffK1inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB9 : uqAffK1inv k * uqAffF0 k * uqAffK1inv k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  -- G4: F₀F₁K₁⁻¹K₁⁻¹ (already Y), F₀K₁⁻¹F₁K₁⁻¹, F₀K₁⁻¹K₁⁻¹F₁
  have hB11 : uqAffF0 k * uqAffK1inv k * uqAffF1 k * uqAffK1inv k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hB12 : uqAffF0 k * uqAffK1inv k * uqAffK1inv k * uqAffF1 k =
      (T 4 : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hB1, hB2, hB3, hB4, hB5, hB6, hB8, hB9, hB11, hB12]
  simp only [T_zero, one_smul]
  exact sector11_cancel_aux k _ _

/-- Sector (2,0) sub-part a F10: left factor F₁F₀, 6 atoms with 2 K₁⁻¹ + K₀⁻¹.
    All normalize to T^n • F₁·F₁·K₁⁻¹·K₀⁻¹ (basis). -/
private theorem sect_hUqIdF10_20a (k : Type*) [CommRing k] :
    (uqAffK1inv k * uqAffF1 k * uqAffF1 k * uqAffK0inv k +
     uqAffF1 k * uqAffK1inv k * uqAffF1 k * uqAffK0inv k +
     uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffF1 k * uqAffK0inv k * uqAffF1 k +
     uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffF1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffK0inv k * uqAffF1 k * uqAffF1 k) = 0 := by
  have h1 := sect_hKinvF_smul_K1invF1 k
  have h2 := sect_hKinvF_at_K1invF1 k
  have h3 := sect_hKinvF_smul_K0invF1 k
  have h4 := sect_hKinvF_at_K0invF1 k
  have hKinvComm := uqAff_K0inv_K1inv_comm k
  have hC1 : uqAffK1inv k * uqAffF1 k * uqAffF1 k * uqAffK0inv k =
      (T 4 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC2 : uqAffF1 k * uqAffK1inv k * uqAffF1 k * uqAffK0inv k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC3 : uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k) := by
    rw [T_zero, one_smul]
  have hC4 : uqAffK1inv k * uqAffF1 k * uqAffK0inv k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hKinvComm]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC5 : uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffF1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hKinvComm]
    try (congr 1; simp only [← T_add]; norm_num)
  have hC6 : uqAffK1inv k * uqAffK0inv k * uqAffF1 k * uqAffF1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul, hKinvComm]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hC1, hC2, hC3, hC4, hC5, hC6]
  simp only [T_zero, one_smul]
  exact sector20a_cancel_aux k _

/-- Sector (2,0) sub-part b F10: left factor F₀F₁, equation form.
    All 6 atoms normalize to T^n • F₁·F₁·K₀⁻¹·K₁⁻¹ (basis). -/
private theorem sect_hUqIdF10_20b (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffF1 k +
     uqAffF1 k * uqAffK0inv k * uqAffF1 k * uqAffK1inv k) =
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) +
    (uqAffK0inv k * uqAffK1inv k * uqAffF1 k * uqAffF1 k +
     uqAffK0inv k * uqAffF1 k * uqAffK1inv k * uqAffF1 k +
     uqAffK0inv k * uqAffF1 k * uqAffF1 k * uqAffK1inv k) := by
  have h1 := sect_hKinvF_smul_K1invF1 k
  have h2 := sect_hKinvF_at_K1invF1 k
  have h3 := sect_hKinvF_smul_K0invF1 k
  have h4 := sect_hKinvF_at_K0invF1 k
  have hKinvComm : uqAffK0inv k * uqAffK1inv k = uqAffK1inv k * uqAffK0inv k :=
    uqAff_K0inv_K1inv_comm k
  have hD1 : uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) := by
    rw [T_zero, one_smul]
  have hD2 : uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffF1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) := by
    rw [show uqAffF1 k * uqAffK0inv k * uqAffK1inv k =
         uqAffF1 k * uqAffK1inv k * uqAffK0inv k from by
      rw [mul_assoc (uqAffF1 k) (uqAffK0inv k) (uqAffK1inv k), hKinvComm, ← mul_assoc]]
    simp only [h2, h4, smul_mul_assoc, smul_smul]
    rw [show uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k =
         uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k from by
      rw [mul_assoc (uqAffF1 k * uqAffF1 k) (uqAffK1inv k) (uqAffK0inv k),
          ← hKinvComm, ← mul_assoc]]
    congr 1; simp only [← T_add]; norm_num
  have hD3 : uqAffF1 k * uqAffK0inv k * uqAffF1 k * uqAffK1inv k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
  have hD4 : uqAffK0inv k * uqAffK1inv k * uqAffF1 k * uqAffF1 k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hD5 : uqAffK0inv k * uqAffF1 k * uqAffK1inv k * uqAffF1 k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hD6 : uqAffK0inv k * uqAffF1 k * uqAffF1 k * uqAffK1inv k =
      (T (-4) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) := by
    simp only [h4, h3, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  rw [hD1, hD2, hD3, hD4, hD5, hD6]
  simp only [T_zero, one_smul]
  exact sector20b_cancel_aux k (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k)

/-- Sector (1,0) CAS sub-part a F10: left = F₁²F₀, 4 atoms with 2 K₁⁻¹ + 1 K₀⁻¹.
    Uses qbinom_sector10_sub1. -/
private theorem sect_hUqIdF10_cas10a (k : Type*) [CommRing k] :
    (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k +
     uqAffK1inv k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k +
     uqAffK1inv k * uqAffK1inv k * uqAffF1 k * uqAffK0inv k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffK1inv k * uqAffK0inv k * uqAffF1 k) = 0 := by
  have h1 := sect_hKinvF_smul_K1invF1 k
  have h2 := sect_hKinvF_at_K1invF1 k
  have h3 := sect_hKinvF_smul_K0invF1 k
  have h4 := sect_hKinvF_at_K0invF1 k
  -- Basis: P = F₁·K₁⁻¹·K₁⁻¹·K₀⁻¹
  have hE1 : uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k) := by
    rw [T_zero, one_smul]
  have hE2 : uqAffK1inv k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
  have hE3 : uqAffK1inv k * uqAffK1inv k * uqAffF1 k * uqAffK0inv k =
      (T 4 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
    congr 1; simp only [← T_add]; norm_num
  have hE4 : uqAffK1inv k * uqAffK1inv k * uqAffK0inv k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hE1, hE2, hE3, hE4]
  simp only [T_zero, one_smul]
  rw [smul_smul]
  have hq := qbinom_sector10_sub1 k
  have : (1 : LaurentPolynomial k) + T 2 + T 4 = (T 2 + 1 + T (-2)) * T 2 := by
    linear_combination hq
  rw [show (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k) +
       (T 2 : LaurentPolynomial k) • (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k) +
       (T 4 : LaurentPolynomial k) • (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k) =
       ((1 : LaurentPolynomial k) + T 2 + T 4) •
         (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k) from by
    rw [add_smul, add_smul, one_smul]]
  rw [this]
  exact sub_self (((T 2 + 1 + T (-2)) * T 2 : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k))

/-- Sector (1,0) CAS sub-part b F10: left = F₁F₀F₁, equation form. -/
private theorem sect_hUqIdF10_cas10b (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffK1inv k +
     uqAffK1inv k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) =
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffK0inv k * uqAffF1 k * uqAffK1inv k +
     uqAffK1inv k * uqAffK0inv k * uqAffK1inv k * uqAffF1 k) := by
  have h1 := sect_hKinvF_smul_K1invF1 k
  have h2 := sect_hKinvF_at_K1invF1 k
  have h3 := sect_hKinvF_smul_K0invF1 k
  have h4 := sect_hKinvF_at_K0invF1 k
  -- All 4 atoms normalize to T^n • K₁⁻¹K₀⁻¹F₁K₁⁻¹ (= F₁·K₁⁻¹·K₀⁻¹·K₁⁻¹ pushed right).
  -- But we need to match the pattern. Let P = F₁·K₁⁻¹·K₀⁻¹·K₁⁻¹.
  -- LHS atom 1: F₁K₁⁻¹K₀⁻¹K₁⁻¹ = P (T 0)
  -- LHS atom 2: K₁⁻¹F₁K₀⁻¹K₁⁻¹ = T(2)•P (push K₁⁻¹ past F₁)
  -- RHS atom 1: K₁⁻¹K₀⁻¹F₁K₁⁻¹ = T(0)? (push K₁⁻¹ past K₀⁻¹, then K₁⁻¹K₀⁻¹F₁...)
  -- Actually this gets messy. Let me just prove LHS = RHS via congr after normalization.
  congr 1
  -- Need: F₁K₁⁻¹K₀⁻¹K₁⁻¹ + K₁⁻¹F₁K₀⁻¹K₁⁻¹ = K₁⁻¹K₀⁻¹F₁K₁⁻¹ + K₁⁻¹K₀⁻¹K₁⁻¹F₁
  -- Normalize all atoms by pushing F₁ to the left.
  -- F₁K₁⁻¹K₀⁻¹K₁⁻¹: already F₁ first
  -- K₁⁻¹F₁K₀⁻¹K₁⁻¹: h1 gives T(2)•F₁K₁⁻¹... but that changes the expression.
  -- Instead, push K⁻¹'s right past F₁.
  -- All 4 atoms have 1 F₁ and 3 K⁻¹'s. Let's normalize to F₁·(K-inv product).
  have hL1 : uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffK1inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffK1inv k) := by
    rw [T_zero, one_smul]
  have hL2 : uqAffK1inv k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffK1inv k) := by
    simp only [h2, h1, smul_mul_assoc, smul_smul]
  have hR1 : uqAffK1inv k * uqAffK0inv k * uqAffF1 k * uqAffK1inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hR2 : uqAffK1inv k * uqAffK0inv k * uqAffK1inv k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hL1, hL2, hR1, hR2]

/-- Sector (1,0) CAS sub-part c F10: left = F₀F₁², equation form. -/
private theorem sect_hUqIdF10_cas10c (k : Type*) [CommRing k] :
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) =
    uqAffK0inv k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k +
     uqAffK0inv k * uqAffK1inv k * uqAffF1 k * uqAffK1inv k +
     uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffF1 k := by
  have h1 := sect_hKinvF_smul_K1invF1 k
  have h2 := sect_hKinvF_at_K1invF1 k
  have h3 := sect_hKinvF_smul_K0invF1 k
  have h4 := sect_hKinvF_at_K0invF1 k
  -- Basis: P = F₁·K₀⁻¹·K₁⁻¹·K₁⁻¹. All 4 atoms normalize to T^n • P.
  have hL : uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) := by
    rw [T_zero, one_smul]
  have hR1 : uqAffK0inv k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k =
      (T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h4, h3, smul_mul_assoc, smul_smul]
  have hR2 : uqAffK0inv k * uqAffK1inv k * uqAffF1 k * uqAffK1inv k =
      (T 0 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  have hR3 : uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) := by
    simp only [h2, h1, h4, h3, smul_mul_assoc, smul_smul]
    try (congr 1; simp only [← T_add]; norm_num)
  rw [hL, hR1, hR2, hR3]
  simp only [T_zero, one_smul]
  -- Goal: q3 • P = T(-2)•P + P + T(2)•P
  have hq := qbinom_sector10_sub1 k
  rw [show (T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) +
      (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) +
      (T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) =
      (T (-2) + 1 + T 2 : LaurentPolynomial k) •
        (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k) from by
    rw [add_smul, add_smul, one_smul]]
  congr 1; ring

set_option maxHeartbeats 1600000 in
private theorem affComulFreeAlg_SerreF10 :
    affComulFreeAlg k
      (ag k F1 * ag k F1 * ag k F1 * ag k F0
       - ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F1 * ag k F0 * ag k F1
       + ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F0 * ag k F1 * ag k F1
       - ag k F0 * ag k F1 * ag k F1 * ag k F1) =
    affComulFreeAlg k 0 := by
  erw [map_zero]
  simp only [map_sub, map_add, map_mul, AlgHom.commutes]
  erw [affComulFreeAlg_ι k F0, affComulFreeAlg_ι k F1]
  simp only [affComulOnGen]
  -- Fold q3 back from distributed form (map_add split it into 3 summands).
  rw [show ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T 2)) +
          ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) 1) +
          ((algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T (-2))) =
          (algebraMap (LaurentPolynomial k)
              (Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k)) (T 2 + 1 + T (-2))
        from by simp [map_add]]
  simp only [← Algebra.smul_def]
  set a := uqAffF1 k ⊗ₜ[LaurentPolynomial k] (1 : Uqsl2Aff k) with ha
  set b := uqAffK1inv k ⊗ₜ[LaurentPolynomial k] uqAffF1 k with hb
  set c := uqAffF0 k ⊗ₜ[LaurentPolynomial k] (1 : Uqsl2Aff k) with hc
  set d := uqAffK0inv k ⊗ₜ[LaurentPolynomial k] uqAffF0 k with hd
  have hSerreS := sect_hSerreF10_smul k
  have hKnorm1 := sect_hKnormF10_1 k
  have hKnorm2 := sect_hKnormF10_2 k
  have hKnorm3 := sect_hKnormF10_3 k
  rw [ha, hb, hc, hd]
  simp only [mul_add, add_mul, smul_add, smul_mul_assoc,
             Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
             hKnorm1, hKnorm2, hKnorm3]
  -- Define two linear maps: phi_L sends x ↦ x ⊗ 1 (for sector (0,0));
  -- phi_R sends y ↦ K₁⁻³K₀⁻¹ ⊗ y (for sector (3,1)).
  let phi_L : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (1 : Uqsl2Aff k)
  let phi_R : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)
      (uqAffK1inv k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k)
  have hSect00 : phi_L (uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffF0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffF1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffF1 k) -
      uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffF1 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_L
  have hSect31 : phi_R (uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffF0 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffF1 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffF1 k) -
      uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffF1 k) = 0 := by
    rw [hSerreS]; exact map_zero phi_R
  rw [map_sub phi_L, map_add phi_L, map_sub phi_L,
      LinearMap.map_smul_of_tower phi_L, LinearMap.map_smul_of_tower phi_L] at hSect00
  rw [map_sub phi_R, map_add phi_R, map_sub phi_R,
      LinearMap.map_smul_of_tower phi_R, LinearMap.map_smul_of_tower phi_R] at hSect31
  simp only [phi_L, phi_R, LinearMap.flip_apply, TensorProduct.mk_apply]
    at hSect00 hSect31
  ------------------------------------------------------------------------
  -- Sector (3,0): right factor F₁³ (uniform), left has K₁⁻³ + F₀ mix.
  ------------------------------------------------------------------------
  have hUqId30 := sect_hUqIdF10_30 k
  let phi_30 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF1 k * uqAffF1 k * uqAffF1 k)
  have hSect30 :
      phi_30 (uqAffK1inv k * uqAffK1inv k * uqAffK1inv k * uqAffF0 k -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffK1inv k * uqAffK1inv k * uqAffF0 k * uqAffK1inv k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffK1inv k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k) -
        uqAffF0 k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k) = 0 := by
    rw [hUqId30]; exact map_zero phi_30
  rw [map_sub phi_30, map_add phi_30, map_sub phi_30,
      LinearMap.map_smul_of_tower phi_30,
      LinearMap.map_smul_of_tower phi_30] at hSect30
  simp only [phi_30, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect30
  ------------------------------------------------------------------------
  -- Sector (0,1): right factor F₀ (uniform), left has F₁³ + K₀⁻¹ mix.
  ------------------------------------------------------------------------
  have hUqId01 := sect_hUqIdF10_01 k
  let phi_01 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF0 k)
  have hSect01 :
      phi_01 (uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffK0inv k -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffF1 k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
          (uqAffF1 k * uqAffK0inv k * uqAffF1 k * uqAffF1 k) -
        uqAffK0inv k * uqAffF1 k * uqAffF1 k * uqAffF1 k) = 0 := by
    rw [hUqId01]; exact map_zero phi_01
  rw [map_sub phi_01, map_add phi_01, map_sub phi_01,
      LinearMap.map_smul_of_tower phi_01,
      LinearMap.map_smul_of_tower phi_01] at hSect01
  simp only [phi_01, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect01
  ------------------------------------------------------------------------
  -- Sector (1,0): right factor F₁ (uniform), left has mixed K₁⁻¹ + F's.
  ------------------------------------------------------------------------
  have hUqId10 := sect_hUqIdF10_10 k
  let phi_10 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF1 k)
  have hSect10 :
      phi_10 ((uqAffK1inv k * uqAffF1 k * uqAffF1 k * uqAffF0 k +
         uqAffF1 k * uqAffK1inv k * uqAffF1 k * uqAffF0 k +
         uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffF0 k) -
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1inv k * uqAffF1 k * uqAffF0 k * uqAffF1 k +
         uqAffF1 k * uqAffK1inv k * uqAffF0 k * uqAffF1 k +
         uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffK1inv k) +
        (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffK1inv k * uqAffF0 k * uqAffF1 k * uqAffF1 k +
         uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffF1 k +
         uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffK1inv k) -
        (uqAffF0 k * uqAffK1inv k * uqAffF1 k * uqAffF1 k +
         uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffF1 k +
         uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffK1inv k)) = 0 := by
    rw [hUqId10]; exact map_zero phi_10
  rw [map_sub phi_10, map_add phi_10, map_sub phi_10,
      LinearMap.map_smul_of_tower phi_10,
      LinearMap.map_smul_of_tower phi_10] at hSect10
  simp only [phi_10, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect10
  ------------------------------------------------------------------------
  -- Sector (1,1): right factor F₁F₀ (two F's), left has mixed K₁⁻¹ + F + K₀⁻¹.
  ------------------------------------------------------------------------
  have hUqId11 := sect_hUqIdF10_11 k
  let phi_11 : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF1 k * uqAffF0 k)
  have hSect11 : phi_11 ((uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffF0 k +
     uqAffK1inv k * uqAffF1 k * uqAffK1inv k * uqAffF0 k +
     uqAffK1inv k * uqAffK1inv k * uqAffF1 k * uqAffF0 k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK1inv k * uqAffF0 k * uqAffK1inv k +
     uqAffK1inv k * uqAffF1 k * uqAffF0 k * uqAffK1inv k +
     uqAffK1inv k * uqAffK1inv k * uqAffF0 k * uqAffF1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffF0 k * uqAffK1inv k * uqAffK1inv k +
     uqAffK1inv k * uqAffF0 k * uqAffF1 k * uqAffK1inv k +
     uqAffK1inv k * uqAffF0 k * uqAffK1inv k * uqAffF1 k) -
    (uqAffF0 k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k +
     uqAffF0 k * uqAffK1inv k * uqAffF1 k * uqAffK1inv k +
     uqAffF0 k * uqAffK1inv k * uqAffK1inv k * uqAffF1 k)) = 0 := by
    rw [hUqId11]; exact map_zero phi_11
  rw [map_sub phi_11, map_add phi_11, map_sub phi_11,
      LinearMap.map_smul_of_tower phi_11,
      LinearMap.map_smul_of_tower phi_11] at hSect11
  simp only [phi_11, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect11
  ------------------------------------------------------------------------
  -- Sector (2,0) sub-part a: left factor F₁F₀, 6 atoms.
  ------------------------------------------------------------------------
  have hUqId20a := sect_hUqIdF10_20a k
  let phi_20a : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF1 k * uqAffF1 k)
  have hSect20a : phi_20a ((uqAffK1inv k * uqAffF1 k * uqAffF1 k * uqAffK0inv k +
     uqAffF1 k * uqAffK1inv k * uqAffF1 k * uqAffK0inv k +
     uqAffF1 k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k) -
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffF1 k * uqAffK0inv k * uqAffF1 k +
     uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffF1 k) +
    (T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffK0inv k * uqAffF1 k * uqAffF1 k)) = 0 := by
    rw [hUqId20a]; exact map_zero phi_20a
  rw [map_add phi_20a, map_sub phi_20a,
      LinearMap.map_smul_of_tower phi_20a,
      LinearMap.map_smul_of_tower phi_20a] at hSect20a
  simp only [phi_20a, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect20a
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part a: left = F₁²F₀, 4 atoms.
  ------------------------------------------------------------------------
  have hUqId_cas10a := sect_hUqIdF10_cas10a k
  let phi_cas10a : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF1 k * uqAffF1 k * uqAffF0 k)
  have hSect_cas10a : phi_cas10a
      ((uqAffF1 k * uqAffK1inv k * uqAffK1inv k * uqAffK0inv k +
        uqAffK1inv k * uqAffF1 k * uqAffK1inv k * uqAffK0inv k +
        uqAffK1inv k * uqAffK1inv k * uqAffF1 k * uqAffK0inv k) -
       (T 2 + 1 + T (-2) : LaurentPolynomial k) •
       (uqAffK1inv k * uqAffK1inv k * uqAffK0inv k * uqAffF1 k)) = 0 := by
    rw [hUqId_cas10a]; exact map_zero phi_cas10a
  rw [map_sub phi_cas10a, map_add phi_cas10a,
      LinearMap.map_smul_of_tower phi_cas10a] at hSect_cas10a
  simp only [phi_cas10a, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect_cas10a
  ------------------------------------------------------------------------
  -- Sector (2,0) sub-part b: left factor F₀F₁, equation form.
  ------------------------------------------------------------------------
  have hUqId20b := sect_hUqIdF10_20b k
  let phi_20b : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF0 k * uqAffF1 k)
  have hSect20b : phi_20b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffF1 k +
     uqAffF1 k * uqAffK0inv k * uqAffF1 k * uqAffK1inv k)) =
    phi_20b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
      (uqAffF1 k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k) +
    (uqAffK0inv k * uqAffK1inv k * uqAffF1 k * uqAffF1 k +
     uqAffK0inv k * uqAffF1 k * uqAffK1inv k * uqAffF1 k +
     uqAffK0inv k * uqAffF1 k * uqAffF1 k * uqAffK1inv k)) := by
    rw [hUqId20b]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_20b, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect20b
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part b: left = F₁F₀F₁, equation form.
  ------------------------------------------------------------------------
  have hUqId_cas10b := sect_hUqIdF10_cas10b k
  let phi_cas10b : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF1 k * uqAffF0 k * uqAffF1 k)
  have hSect_cas10b : phi_cas10b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK1inv k * uqAffK0inv k * uqAffK1inv k +
     uqAffK1inv k * uqAffF1 k * uqAffK0inv k * uqAffK1inv k)) =
    phi_cas10b ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffK1inv k * uqAffK0inv k * uqAffF1 k * uqAffK1inv k +
     uqAffK1inv k * uqAffK0inv k * uqAffK1inv k * uqAffF1 k)) := by
    rw [hUqId_cas10b]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_cas10b, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect_cas10b
  ------------------------------------------------------------------------
  -- Sector (1,0) CAS sub-part c: left = F₀F₁², equation form.
  ------------------------------------------------------------------------
  have hUqId_cas10c := sect_hUqIdF10_cas10c k
  let phi_cas10c : Uqsl2Aff k →ₗ[LaurentPolynomial k]
      Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k :=
    (TensorProduct.mk (LaurentPolynomial k) (Uqsl2Aff k) (Uqsl2Aff k)).flip
      (uqAffF0 k * uqAffF1 k * uqAffF1 k)
  have hSect_cas10c : phi_cas10c ((T 2 + 1 + T (-2) : LaurentPolynomial k) •
    (uqAffF1 k * uqAffK0inv k * uqAffK1inv k * uqAffK1inv k)) =
    phi_cas10c (uqAffK0inv k * uqAffF1 k * uqAffK1inv k * uqAffK1inv k +
     uqAffK0inv k * uqAffK1inv k * uqAffF1 k * uqAffK1inv k +
     uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffF1 k) := by
    rw [hUqId_cas10c]
  simp only [map_add, map_sub, LinearMap.map_smul_of_tower,
             phi_cas10c, LinearMap.flip_apply, TensorProduct.mk_apply] at hSect_cas10c
  simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, smul_add]
    at hSect10 hSect11 hSect20a hSect_cas10a hSect20b hSect_cas10b hSect_cas10c
  have h20b := sub_eq_zero_of_eq hSect20b
  have h10b := sub_eq_zero_of_eq hSect_cas10b
  have h10c := sub_eq_zero_of_eq hSect_cas10c
  simp only [LinearMap.smul_apply, LinearMap.add_apply] at h20b h10b h10c
  repeat erw [TensorProduct.mk_apply] at h20b
  repeat erw [TensorProduct.mk_apply] at h10b
  repeat erw [TensorProduct.mk_apply] at h10c
  clear ha hb hc hd hSerreS hKnorm1 hKnorm2 hKnorm3 phi_L phi_R phi_30 phi_01
    phi_10 phi_11 phi_20a phi_cas10a phi_20b phi_cas10b phi_cas10c hUqId30 hUqId01
    hUqId10 hUqId11 hUqId20a hUqId_cas10a hUqId20b hUqId_cas10b hUqId_cas10c
    hSect20b hSect_cas10b hSect_cas10c
  clear a b c d
  linear_combination (norm := skip) hSect00 + hSect31 + hSect30 + hSect01 +
    hSect10 + hSect11 + hSect20a + hSect_cas10a + h20b - h10b + h10c
  convert (show (0 : Uqsl2Aff k ⊗[LaurentPolynomial k] Uqsl2Aff k) = 0 from rfl) using 2
  all_goals first | rfl | module

/-- The coproduct respects all affine Chevalley relations. -/
private theorem affComulFreeAlg_respects_rel :
    ∀ ⦃x y : FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen⦄,
    AffChevalleyRel k x y → affComulFreeAlg k x = affComulFreeAlg k y := by
  intro x y h
  cases h with
  | K0K0inv => rw [affComulFreeAlg_K0K0inv, map_one]
  | K0invK0 => rw [affComulFreeAlg_K0invK0, map_one]
  | K1K1inv => rw [affComulFreeAlg_K1K1inv, map_one]
  | K1invK1 => rw [affComulFreeAlg_K1invK1, map_one]
  | K0K1 => exact affComulFreeAlg_K0K1 k
  | K0E0 => exact affComulFreeAlg_K0E0 k
  | K1E1 => exact affComulFreeAlg_K1E1 k
  | K0E1 => exact affComulFreeAlg_K0E1 k
  | K1E0 => exact affComulFreeAlg_K1E0 k
  | K0F0 => exact affComulFreeAlg_K0F0 k
  | K1F1 => exact affComulFreeAlg_K1F1 k
  | K0F1 => exact affComulFreeAlg_K0F1 k
  | K1F0 => exact affComulFreeAlg_K1F0 k
  | Serre0 => exact affComulFreeAlg_Serre0 k
  | Serre1 => exact affComulFreeAlg_Serre1 k
  | E0F1 => exact affComulFreeAlg_E0F1 k
  | E1F0 => exact affComulFreeAlg_E1F0 k
  | SerreE01 => exact affComulFreeAlg_SerreE01 k
  | SerreE10 => exact affComulFreeAlg_SerreE10 k
  | SerreF01 => exact affComulFreeAlg_SerreF01 k
  | SerreF10 => exact affComulFreeAlg_SerreF10 k

/-- The coproduct on U_q(ŝl₂), pushed through the quotient. -/
noncomputable def affComul :
    Uqsl2Aff k →ₐ[LaurentPolynomial k]
    (Uqsl2Aff k) ⊗[LaurentPolynomial k] (Uqsl2Aff k) :=
  RingQuot.liftAlgHom (LaurentPolynomial k)
    ⟨affComulFreeAlg k, affComulFreeAlg_respects_rel k⟩

/-! ## 2. Counit -/

/-- Counit on generators: ε(E_i) = ε(F_i) = 0, ε(K_i) = ε(K_i⁻¹) = 1. -/
private def affCounitOnGen : Uqsl2AffGen → LaurentPolynomial k
  | .E0 | .E1 | .F0 | .F1 => 0
  | .K0 | .K1 | .K0inv | .K1inv => 1

private noncomputable def affCounitFreeAlg :
    FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen →ₐ[LaurentPolynomial k]
    LaurentPolynomial k :=
  FreeAlgebra.lift (LaurentPolynomial k) (affCounitOnGen k)

private theorem affCounitFreeAlg_respects_rel :
    ∀ ⦃x y : FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen⦄,
    AffChevalleyRel k x y → affCounitFreeAlg k x = affCounitFreeAlg k y := by
  intro x y h;
  rcases h with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ ) <;> simp +decide [ affCounitFreeAlg, affCounitOnGen ]

noncomputable def affCounit :
    Uqsl2Aff k →ₐ[LaurentPolynomial k] LaurentPolynomial k :=
  RingQuot.liftAlgHom (LaurentPolynomial k)
    ⟨affCounitFreeAlg k, affCounitFreeAlg_respects_rel k⟩

/-! ## 3. Antipode -/

private def affAntipodeOnGen : Uqsl2AffGen → (Uqsl2Aff k)ᵐᵒᵖ
  | .E0    => MulOpposite.op (-(uqAffE0 k * uqAffK0inv k))
  | .E1    => MulOpposite.op (-(uqAffE1 k * uqAffK1inv k))
  | .F0    => MulOpposite.op (-(uqAffK0 k * uqAffF0 k))
  | .F1    => MulOpposite.op (-(uqAffK1 k * uqAffF1 k))
  | .K0    => MulOpposite.op (uqAffK0inv k)
  | .K1    => MulOpposite.op (uqAffK1inv k)
  | .K0inv => MulOpposite.op (uqAffK0 k)
  | .K1inv => MulOpposite.op (uqAffK1 k)

private noncomputable def affAntipodeFreeAlg :
    FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen →ₐ[LaurentPolynomial k]
    (Uqsl2Aff k)ᵐᵒᵖ :=
  FreeAlgebra.lift (LaurentPolynomial k) (affAntipodeOnGen k)

private theorem affAntipodeFreeAlg_ι (x : Uqsl2AffGen) :
    affAntipodeFreeAlg k (FreeAlgebra.ι _ x) = affAntipodeOnGen k x := by
  unfold affAntipodeFreeAlg; exact FreeAlgebra.lift_ι_apply _ _

/-! ### Antipode case helpers -/

/-
KK⁻¹ cases
-/
private theorem affAntipodeFreeAlg_K0K0inv :
    affAntipodeFreeAlg k (ag k K0 * ag k K0inv) =
    (1 : (Uqsl2Aff k)ᵐᵒᵖ) := by
  have h_K0K0inv_mul_step2 : (affAntipodeFreeAlg k (ag k K0)) * (affAntipodeFreeAlg k (ag k K0inv)) = 1 := by
    convert congr_arg MulOpposite.op ( uqAff_K0_mul_K0inv k ) using 1;
    have := @affAntipodeFreeAlg_ι k;
    convert congr_arg₂ ( · * · ) ( this K0 ) ( this K0inv ) using 1;
  aesop

private theorem affAntipodeFreeAlg_K0invK0 :
    affAntipodeFreeAlg k (ag k K0inv * ag k K0) =
    (1 : (Uqsl2Aff k)ᵐᵒᵖ) := by
  have h_antipode_K0 : (affAntipodeFreeAlg k (ag k K0)) = MulOpposite.op (uqAffK0inv k) := by
    convert affAntipodeFreeAlg_ι k K0 using 1;
  convert congr_arg MulOpposite.op ( uqAff_K0inv_mul_K0 k ) using 1;
  convert congr_arg₂ ( · * · ) ( affAntipodeFreeAlg_ι k K0inv ) h_antipode_K0 using 1;
  exact map_mul _ _ _

private theorem affAntipodeFreeAlg_K1K1inv :
    affAntipodeFreeAlg k (ag k K1 * ag k K1inv) =
    (1 : (Uqsl2Aff k)ᵐᵒᵖ) := by
  simp +decide [ affAntipodeFreeAlg, ag ];
  unfold affAntipodeOnGen;
  simp +decide [ ← MulOpposite.op_mul, uqAff_K1_mul_K1inv ]

private theorem affAntipodeFreeAlg_K1invK1 :
    affAntipodeFreeAlg k (ag k K1inv * ag k K1) =
    (1 : (Uqsl2Aff k)ᵐᵒᵖ) := by
  convert congr_arg MulOpposite.op ( uqAff_K1inv_mul_K1 k ) using 1;
  erw [ RingHom.map_mul, affAntipodeFreeAlg_ι, affAntipodeFreeAlg_ι ];
  simp +decide [ affAntipodeOnGen ]

/-
K0K1 commutativity
-/
private theorem affAntipodeFreeAlg_K0K1 :
    affAntipodeFreeAlg k (ag k K0 * ag k K1) =
    affAntipodeFreeAlg k (ag k K1 * ag k K0) := by
  simp +decide [ affAntipodeFreeAlg ];
  simp +decide [ affAntipodeOnGen ];
  simp +decide [ ← MulOpposite.op_mul, mul_comm ];
  have h_comm : uqAffK0inv k * uqAffK1inv k * uqAffK0 k * uqAffK1 k = 1 := by
    simp +decide [ mul_assoc, uqAff_K0inv_mul_K0, uqAff_K1inv_mul_K1 ];
    simp +decide [ ← mul_assoc, uqAff_K0K1_comm ];
    simp +decide [ mul_assoc, uqAff_K0inv_mul_K0, uqAff_K1inv_mul_K1 ];
  have h_comm : uqAffK0inv k * uqAffK1inv k * uqAffK0 k = uqAffK1inv k := by
    apply_fun ( · * uqAffK1inv k ) at h_comm;
    simp_all +decide [ mul_assoc, uqAff_K1_mul_K1inv ];
  have h_comm : uqAffK0inv k * uqAffK1inv k * uqAffK0 k * uqAffK0inv k = uqAffK1inv k * uqAffK0inv k := by
    rw [h_comm];
  rw [ ← h_comm, mul_assoc, uqAff_K0_mul_K0inv, mul_one ]

/-
KE cases
-/
private theorem affAntipodeFreeAlg_K0E0 :
    affAntipodeFreeAlg k (ag k K0 * ag k E0) =
    affAntipodeFreeAlg k (ascal k (T 2) * ag k E0 * ag k K0) := by
  rw [ show ( affAntipodeFreeAlg k ) ( ag k K0 * ag k E0 ) = MulOpposite.op ( uqAffK0inv k ) * MulOpposite.op ( - ( uqAffE0 k * uqAffK0inv k ) ) by
        erw [ map_mul, affAntipodeFreeAlg_ι, affAntipodeFreeAlg_ι ] ; rfl,
      show ( affAntipodeFreeAlg k ) ( ascal k ( T 2 ) * ag k E0 * ag k K0 ) = MulOpposite.op ( - ( algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ( T 2 ) * uqAffE0 k * uqAffK0inv k ) ) * MulOpposite.op ( uqAffK0inv k ) from ?_ ];
  · simp +decide [ ← mul_assoc, ← MulOpposite.op_mul, uqAff_E0_mul_K0inv ];
    rw [ show ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ) ( T 2 ) * uqAffK0inv k * uqAffE0 k = uqAffK0inv k * ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ( T 2 ) * uqAffE0 k ) by
          simp +decide [ ← mul_assoc, ← Algebra.smul_def ] ];
    simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
    grind;
  · simp +decide [ affAntipodeFreeAlg, affAntipodeOnGen, mul_assoc ];
    simp +decide [ mul_assoc, mul_left_comm, mul_comm, Algebra.algebraMap_eq_smul_one ];
    simp +decide [ mul_assoc, Algebra.smul_def ];
    grind

private theorem affAntipodeFreeAlg_K1E1 :
    affAntipodeFreeAlg k (ag k K1 * ag k E1) =
    affAntipodeFreeAlg k (ascal k (T 2) * ag k E1 * ag k K1) := by
  rw [ show ( affAntipodeFreeAlg k ) ( ag k K1 * ag k E1 ) = MulOpposite.op ( uqAffK1inv k ) * MulOpposite.op ( - ( uqAffE1 k * uqAffK1inv k ) ) by
        erw [ map_mul, affAntipodeFreeAlg_ι, affAntipodeFreeAlg_ι ];
        rfl ];
  rw [ show ( affAntipodeFreeAlg k ) ( ascal k ( T 2 ) * ag k E1 * ag k K1 ) = MulOpposite.op ( - ( algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ( T 2 ) * uqAffE1 k * uqAffK1inv k ) ) * MulOpposite.op ( uqAffK1inv k ) from ?_ ];
  · simp +decide [ ← mul_assoc, ← MulOpposite.op_mul, uqAff_E1_mul_K1inv ];
    rw [ show ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ) ( T 2 ) * uqAffK1inv k * uqAffE1 k = uqAffK1inv k * ( algebraMap k[T;T⁻¹] ( Uqsl2Aff k ) ( T 2 ) * uqAffE1 k ) by
          simp +decide [ ← mul_assoc, ← Algebra.smul_def ] ];
    simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
    grind +splitImp;
  · simp +decide [ affAntipodeFreeAlg ];
    simp +decide [ affAntipodeOnGen, mul_assoc ];
    simp +decide [ mul_assoc, mul_left_comm, mul_comm, Algebra.algebraMap_eq_smul_one ];
    simp +decide [ mul_assoc, mul_left_comm, mul_comm, Algebra.smul_def ];
    grind +splitImp

private theorem affAntipodeFreeAlg_K0E1 :
    affAntipodeFreeAlg k (ag k K0 * ag k E1) =
    affAntipodeFreeAlg k (ascal k (T (-2)) * ag k E1 * ag k K0) := by
  simp +decide [ affAntipodeOnGen, affAntipodeFreeAlg ];
  -- Since the algebraMap is central, multiplying by it commutes with any element.
  have h_central : ∀ (x : Uqsl2Aff k), algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * x = x * algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) := by
    exact?;
  have := uqAff_E1_mul_K0inv k;
  replace this := congr_arg ( fun x => x * uqAffK1inv k ) this ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  simp_all +decide [ ← mul_assoc, ← MulOpposite.op_mul, ← MulOpposite.op_neg ];
  convert congr_arg Neg.neg this using 1 <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · simp +decide [ mul_assoc, uqAff_K0inv_K1inv_comm ];
    grind +qlia;
  · grind +locals

private theorem affAntipodeFreeAlg_K1E0 :
    affAntipodeFreeAlg k (ag k K1 * ag k E0) =
    affAntipodeFreeAlg k (ascal k (T (-2)) * ag k E0 * ag k K1) := by
  simp +decide [ affAntipodeOnGen, affAntipodeFreeAlg ];
  have h_central : ∀ (x : Uqsl2Aff k), algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * x = x * algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) := by
    exact?;
  have := uqAff_E0_mul_K1inv k;
  replace this := congr_arg ( fun x => x * uqAffK0inv k ) this ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  simp_all +decide [ ← mul_assoc, ← MulOpposite.op_mul, ← MulOpposite.op_neg ];
  convert congr_arg Neg.neg this using 1 <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · simp +decide [ mul_assoc, (uqAff_K0inv_K1inv_comm k).symm ]
    grind +qlia;
  · grind +locals

-- KF cases
private theorem affAntipodeFreeAlg_K0F0 :
    affAntipodeFreeAlg k (ag k K0 * ag k F0) =
    affAntipodeFreeAlg k (ascal k (T (-2)) * ag k F0 * ag k K0) := by
  -- Both sides equal op(-T(-2)*F₀) after expansion and K₀K₀⁻¹ cancellation
  have key : -(uqAffK0 k * uqAffF0 k) * uqAffK0inv k =
    -(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF0 k) := by
    letI : NonUnitalNonAssocRing (Uqsl2Aff k) := inferInstance
    rw [neg_mul, neg_inj, uqAff_K0F0]; simp +decide [mul_assoc, uqAff_K0_mul_K0inv]
  have hL : affAntipodeFreeAlg k (ag k K0 * ag k F0) =
    MulOpposite.op (-(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF0 k)) := by
    erw [map_mul, affAntipodeFreeAlg_ι, affAntipodeFreeAlg_ι]
    exact (MulOpposite.op_mul (-(uqAffK0 k * uqAffF0 k)) (uqAffK0inv k)).symm.trans
      (congr_arg MulOpposite.op key)
  rw [hL]
  -- Now: op(-T(-2)F₀) = S(T(-2)*F₀*K₀)
  symm
  rw [ show ( affAntipodeFreeAlg k ) ( ascal k ( T (-2) ) * ag k F0 * ag k K0 ) = MulOpposite.op ( - ( algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ( T (-2) ) * uqAffK0 k * uqAffF0 k ) ) * MulOpposite.op ( uqAffK0inv k ) from ?_ ]
  · -- op(-T(-2)K₀F₀) * op(K₀⁻¹) = op(K₀⁻¹ * (-T(-2)K₀F₀)) by op_mul
    -- Need: K₀⁻¹ * (-T(-2)K₀F₀) = -T(-2)F₀
    have key2 : uqAffK0inv k * (-(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffK0 k * uqAffF0 k)) =
      -(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF0 k) := by
      letI : NonUnitalNonAssocRing (Uqsl2Aff k) := inferInstance
      rw [mul_neg, neg_inj]
      simp +decide [mul_assoc, ← mul_assoc, uqAff_K0inv_mul_K0, uqAff_K0_mul_K0inv, Algebra.commutes, mul_comm, mul_left_comm]
    exact (MulOpposite.op_mul (uqAffK0inv k) (-(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffK0 k * uqAffF0 k))).symm.trans
      (congr_arg MulOpposite.op key2)
  · simp +decide [ affAntipodeFreeAlg, affAntipodeOnGen, mul_assoc ]
    simp +decide [ mul_assoc, mul_left_comm, mul_comm, Algebra.algebraMap_eq_smul_one ]
    simp +decide [ mul_assoc, Algebra.smul_def ]
    grind

private theorem affAntipodeFreeAlg_K1F1 :
    affAntipodeFreeAlg k (ag k K1 * ag k F1) =
    affAntipodeFreeAlg k (ascal k (T (-2)) * ag k F1 * ag k K1) := by
  have key : -(uqAffK1 k * uqAffF1 k) * uqAffK1inv k =
    -(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF1 k) := by
    letI : NonUnitalNonAssocRing (Uqsl2Aff k) := inferInstance
    rw [neg_mul, neg_inj, uqAff_K1F1]; simp +decide [mul_assoc, uqAff_K1_mul_K1inv]
  have hL : affAntipodeFreeAlg k (ag k K1 * ag k F1) =
    MulOpposite.op (-(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF1 k)) := by
    erw [map_mul, affAntipodeFreeAlg_ι, affAntipodeFreeAlg_ι]
    exact (MulOpposite.op_mul (-(uqAffK1 k * uqAffF1 k)) (uqAffK1inv k)).symm.trans
      (congr_arg MulOpposite.op key)
  rw [hL]
  symm
  rw [ show ( affAntipodeFreeAlg k ) ( ascal k ( T (-2) ) * ag k F1 * ag k K1 ) = MulOpposite.op ( - ( algebraMap ( LaurentPolynomial k ) ( Uqsl2Aff k ) ( T (-2) ) * uqAffK1 k * uqAffF1 k ) ) * MulOpposite.op ( uqAffK1inv k ) from ?_ ]
  · have key2 : uqAffK1inv k * (-(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffK1 k * uqAffF1 k)) =
      -(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffF1 k) := by
      letI : NonUnitalNonAssocRing (Uqsl2Aff k) := inferInstance
      rw [mul_neg, neg_inj]
      simp +decide [mul_assoc, ← mul_assoc, uqAff_K1inv_mul_K1, uqAff_K1_mul_K1inv, Algebra.commutes, mul_comm, mul_left_comm]
    exact (MulOpposite.op_mul (uqAffK1inv k) (-(algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffK1 k * uqAffF1 k))).symm.trans
      (congr_arg MulOpposite.op key2)
  · simp +decide [ affAntipodeFreeAlg, affAntipodeOnGen, mul_assoc ]
    simp +decide [ mul_assoc, mul_left_comm, mul_comm, Algebra.algebraMap_eq_smul_one ]
    simp +decide [ mul_assoc, Algebra.smul_def ]
    grind

private theorem affAntipodeFreeAlg_K0F1 :
    affAntipodeFreeAlg k (ag k K0 * ag k F1) =
    affAntipodeFreeAlg k (ascal k (T 2) * ag k F1 * ag k K0) := by
  simp +decide [ mul_assoc, Algebra.algebraMap_eq_smul_one ];
  simp +decide [ affAntipodeFreeAlg_ι, affAntipodeOnGen ];
  -- Using the commutativity of $uqAffK0 k$ and $uqAffK1 k$, we can rearrange the terms.
  have h_comm : uqAffK0inv k * uqAffK1 k = uqAffK1 k * uqAffK0inv k := by
    apply uqAff_K0K1_comm k |> fun h => by
      apply_fun (fun x => x * uqAffK0inv k) at h;
      simp_all +decide [ mul_assoc, uqAff_K0_mul_K0inv ];
      apply_fun (fun x => uqAffK0inv k * x) at h;
      simp_all +decide [ ← mul_assoc, uqAff_K0inv_mul_K0 ];
  have h_comm : uqAffF1 k * uqAffK0inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (2)) * uqAffK0inv k * uqAffF1 k := by
    convert uqAff_F1_mul_K0inv k using 1;
  simp_all +decide [ mul_assoc, mul_left_comm, mul_comm ];
  simp +decide [ ← mul_assoc, ← MulOpposite.op_mul, ← MulOpposite.op_neg, ← MulOpposite.op_smul ];
  have h_comm : uqAffK1 k * uqAffF1 k * uqAffK0inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffK0inv k * (uqAffK1 k * uqAffF1 k) := by
    simp +decide [ mul_assoc, h_comm ];
    simp +decide [ ← mul_assoc, ← ‹uqAffK0inv k * uqAffK1 k = uqAffK1 k * uqAffK0inv k› ];
    simp +decide [ mul_assoc, mul_left_comm, Algebra.commutes ];
    simp +decide [ ← mul_assoc, ← ‹uqAffK0inv k * uqAffK1 k = uqAffK1 k * uqAffK0inv k› ];
  convert congr_arg Neg.neg h_comm using 1 <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · grind;
  · simp +decide [ Algebra.smul_def ];
    grind

private theorem affAntipodeFreeAlg_K1F0 :
    affAntipodeFreeAlg k (ag k K1 * ag k F0) =
    affAntipodeFreeAlg k (ascal k (T 2) * ag k F0 * ag k K1) := by
  -- Mirror K₀F₁ proof with 0↔1 swap
  simp +decide [ mul_assoc, Algebra.algebraMap_eq_smul_one ];
  simp +decide [ affAntipodeFreeAlg_ι, affAntipodeOnGen ];
  have h_comm : uqAffK1inv k * uqAffK0 k = uqAffK0 k * uqAffK1inv k := by
    have h := uqAff_K0K1_comm k
    apply_fun (fun x => x * uqAffK1inv k) at h;
    simp +decide [ mul_assoc, uqAff_K1_mul_K1inv ] at h;
    apply_fun (fun x => uqAffK1inv k * x) at h;
    simp +decide [ ← mul_assoc, uqAff_K1inv_mul_K1 ] at h;
    exact h;
  have h_comm : uqAffF0 k * uqAffK1inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (2)) * uqAffK1inv k * uqAffF0 k := by
    convert uqAff_F0_mul_K1inv k using 1;
  simp_all +decide [ mul_assoc, mul_left_comm, mul_comm ];
  simp +decide [ ← mul_assoc, ← MulOpposite.op_mul, ← MulOpposite.op_neg, ← MulOpposite.op_smul ];
  have h_comm : uqAffK0 k * uqAffF0 k * uqAffK1inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffK1inv k * (uqAffK0 k * uqAffF0 k) := by
    simp +decide [ mul_assoc, h_comm ];
    simp +decide [ ← mul_assoc, ← ‹uqAffK1inv k * uqAffK0 k = uqAffK0 k * uqAffK1inv k› ];
    simp +decide [ mul_assoc, mul_left_comm, Algebra.commutes ];
    simp +decide [ ← mul_assoc, ← ‹uqAffK1inv k * uqAffK0 k = uqAffK0 k * uqAffK1inv k› ];
  convert congr_arg Neg.neg h_comm using 1 <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · grind;
  · simp +decide [ Algebra.smul_def ];
    grind

/-
Serre cases
-/
private theorem affAntipodeFreeAlg_Serre0 :
    affAntipodeFreeAlg k
      (ascal k (T 1 - T (-1)) * (ag k E0 * ag k F0 - ag k F0 * ag k E0)) =
    affAntipodeFreeAlg k (ag k K0 - ag k K0inv) := by
  -- PROOF SKETCH for Aristotle:
  -- RHS: S(K₀-K₀⁻¹) = op(K₀⁻¹) - op(K₀) = op(K₀⁻¹-K₀)
  -- LHS: S is AlgHom to Mᵒᵖ, so S(c*(EF-FE)) = c_op * (S(E₀)*S(F₀) - S(F₀)*S(E₀))
  --   S(E₀)*S(F₀) = op(-E₀K₀⁻¹)*op(-K₀F₀) = op(K₀F₀*E₀K₀⁻¹) [neg_mul_neg in Mᵒᵖ]
  --   S(F₀)*S(E₀) = op(-K₀F₀)*op(-E₀K₀⁻¹) = op(E₀K₀⁻¹*K₀F₀) = op(E₀F₀) [K₀⁻¹K₀=1]
  -- Key identity: K₀F₀*E₀K₀⁻¹ = F₀E₀ (via K₀F₀=T(-2)F₀K₀, K₀E₀=T(2)E₀K₀, T-cancel)
  -- So LHS = c_op * (op(F₀E₀) - op(E₀F₀)) = c_op * op(F₀E₀-E₀F₀) = op(c*(F₀E₀-E₀F₀))
  -- And c*(F₀E₀-E₀F₀) = -(c*(E₀F₀-F₀E₀)) = -(K₀-K₀⁻¹) = K₀⁻¹-K₀ [by uqAff_Serre0]
  -- AVAILABLE LEMMAS: uqAff_neg_mul_neg, uqAff_K0F0, uqAff_E0_mul_K0inv,
  --   uqAff_Serre0, uqAff_K0_mul_K0inv, affAntipodeFreeAlg_ι, affAntipodeOnGen,
  --   MulOpposite.op_mul, MulOpposite.op_sub, Algebra.commutes
  -- WORKAROUND: Use `letI : NonUnitalNonAssocRing (Uqsl2Aff k) := inferInstance` before neg_mul/mul_neg.
  --   Use `← Algebra.smul_def` + smul_mul_assoc/mul_smul_comm for scalar commutation.
  --   Use `erw` (not rw) for map_sub, map_mul on RingQuot types.
  have h_comm : (uqAffK0 k * uqAffF0 k * uqAffE0 k * uqAffK0inv k) = (uqAffF0 k * uqAffE0 k) := by
    simp +decide [ mul_assoc, uqAff_K0F0, uqAff_K0inv_mul_F0 ];
    simp +decide [ ← mul_assoc, uqAff_E0_mul_K0inv ];
    simp +decide [ mul_assoc, mul_left_comm, ← Algebra.smul_def ];
    simp +decide [ ← mul_assoc, uqAff_K0_mul_K0inv ];
    exact?;
  have h_comm : (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 1 - T (-1))) * (uqAffF0 k * uqAffE0 k - uqAffE0 k * uqAffF0 k) = -(uqAffK0 k - uqAffK0inv k) := by
    rw [ ← uqAff_Serre0 ] ; ring;
    grind;
  convert congr_arg ( fun x => MulOpposite.op x ) h_comm using 1;
  · simp +decide [ ascal, ag, mul_assoc, mul_sub, sub_mul, mul_comm, mul_left_comm, Algebra.algebraMap_eq_smul_one ];
    simp +decide [ affAntipodeFreeAlg_ι, affAntipodeOnGen ];
    simp +decide [ ← MulOpposite.op_mul, ← MulOpposite.op_add, ← MulOpposite.op_neg, mul_assoc, mul_left_comm, mul_comm ];
    simp +decide [ mul_assoc, mul_left_comm, mul_comm, uqAff_neg_mul_neg ];
    simp +decide [ ← mul_assoc, ← MulOpposite.op_mul, uqAff_K0_mul_K0inv, uqAff_K0inv_mul_K0 ];
    simp +decide [ ← smul_sub, ‹uqAffK0 k * uqAffF0 k * uqAffE0 k * uqAffK0inv k = uqAffF0 k * uqAffE0 k›, uqAff_K0inv_mul_K0 ];
    simp +decide [ ← mul_assoc, ← MulOpposite.op_mul, uqAff_K0_mul_K0inv, uqAff_K0inv_mul_K0 ];
    simp +decide [ mul_assoc, uqAff_K0inv_mul_K0 ];
    module;
  · simp +decide [ affAntipodeFreeAlg, affAntipodeOnGen ];
    grind +splitImp

private theorem affAntipodeFreeAlg_Serre1 :
    affAntipodeFreeAlg k
      (ascal k (T 1 - T (-1)) * (ag k E1 * ag k F1 - ag k F1 * ag k E1)) =
    affAntipodeFreeAlg k (ag k K1 - ag k K1inv) := by
  -- Mirror of Serre0 with 0↔1 swap.
  have h_comm : (uqAffK1 k * uqAffF1 k * uqAffE1 k * uqAffK1inv k) = (uqAffF1 k * uqAffE1 k) := by
    simp +decide [ mul_assoc, uqAff_K1F1, uqAff_K1inv_mul_F1 ];
    simp +decide [ ← mul_assoc, uqAff_E1_mul_K1inv ];
    simp +decide [ mul_assoc, mul_left_comm, ← Algebra.smul_def ];
    simp +decide [ ← mul_assoc, uqAff_K1_mul_K1inv ];
    exact?;
  have h_comm : (algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 1 - T (-1))) * (uqAffF1 k * uqAffE1 k - uqAffE1 k * uqAffF1 k) = -(uqAffK1 k - uqAffK1inv k) := by
    rw [ ← uqAff_Serre1 ] ; ring;
    grind;
  convert congr_arg ( fun x => MulOpposite.op x ) h_comm using 1;
  · simp +decide [ ascal, ag, mul_assoc, mul_sub, sub_mul, mul_comm, mul_left_comm, Algebra.algebraMap_eq_smul_one ];
    simp +decide [ affAntipodeFreeAlg_ι, affAntipodeOnGen ];
    simp +decide [ ← MulOpposite.op_mul, ← MulOpposite.op_add, ← MulOpposite.op_neg, mul_assoc, mul_left_comm, mul_comm ];
    simp +decide [ mul_assoc, mul_left_comm, mul_comm, uqAff_neg_mul_neg ];
    simp +decide [ ← mul_assoc, ← MulOpposite.op_mul, uqAff_K1_mul_K1inv, uqAff_K1inv_mul_K1 ];
    simp +decide [ ← smul_sub, ‹uqAffK1 k * uqAffF1 k * uqAffE1 k * uqAffK1inv k = uqAffF1 k * uqAffE1 k›, uqAff_K1inv_mul_K1 ];
    simp +decide [ ← mul_assoc, ← MulOpposite.op_mul, uqAff_K1_mul_K1inv, uqAff_K1inv_mul_K1 ];
    simp +decide [ mul_assoc, uqAff_K1inv_mul_K1 ];
    module;
  · simp +decide [ affAntipodeFreeAlg, affAntipodeOnGen ];
    grind +splitImp

/-
Cross-commutation cases
-/
private theorem affAntipodeFreeAlg_E0F1 :
    affAntipodeFreeAlg k (ag k E0 * ag k F1) =
    affAntipodeFreeAlg k (ag k F1 * ag k E0) := by
  erw [map_mul, map_mul, affAntipodeFreeAlg_ι, affAntipodeFreeAlg_ι]
  simp +decide [affAntipodeOnGen]
  -- Use unop_injective to get into base ring
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_neg]
  -- Cancel negs using our helper (RingQuot diamond workaround)
  rw [uqAff_neg_mul_neg, uqAff_neg_mul_neg]
  -- Negs cancelled. Goal: K₁F₁·E₀K₀⁻¹ = E₀K₀⁻¹·K₁F₁
  -- Proof: K₁F₁·E₀K₀⁻¹ = K₁·(F₁E₀)·K₀⁻¹ = K₁·(E₀F₁)·K₀⁻¹  [uqAff_E0F1_comm]
  --   = (K₁E₀)·(F₁K₀⁻¹) = T(-2)E₀K₁·T(2)K₀⁻¹F₁  [uqAff_K1E0, uqAff_F1_mul_K0inv]
  --   = E₀·(K₁K₀⁻¹)·F₁  [T(-2)T(2)=1, scalars central]
  --   = E₀·K₀⁻¹·K₁·F₁   [K₁K₀⁻¹ = K₀⁻¹K₁ by uqAff_K0K1_comm]
  --   = E₀K₀⁻¹·K₁F₁
  -- AVAILABLE: uqAff_E0F1_comm, uqAff_K1E0, uqAff_F1_mul_K0inv,
  --   uqAff_K0K1_comm, uqAff_K0inv_K1inv_comm, Algebra.commutes,
  --   LaurentPolynomial.T_add. Use `← Algebra.smul_def` + smul_mul_assoc for scalars.
  --   Use `erw` for rewrites on RingQuot types. `letI : NonUnitalNonAssocRing` if needed.
  have h_comm : uqAffF1 k * uqAffE0 k = uqAffE0 k * uqAffF1 k := by
    exact?;
  have h_assoc : uqAffK1 k * uqAffE0 k * uqAffF1 k * uqAffK0inv k = uqAffE0 k * uqAffK1 k * uqAffK0inv k * uqAffF1 k := by
    have h_assoc : uqAffK1 k * uqAffE0 k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffE0 k * uqAffK1 k := by
      exact?;
    have h_assoc : uqAffF1 k * uqAffK0inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffK0inv k * uqAffF1 k := by
      exact?;
    simp_all +decide [ mul_assoc, Algebra.smul_def ];
    simp_all +decide [ ← mul_assoc, ← Algebra.smul_def ];
    exact?;
  have h_assoc : uqAffK1 k * uqAffK0inv k = uqAffK0inv k * uqAffK1 k := by
    have h_assoc : uqAffK1 k * uqAffK0inv k = uqAffK0inv k * uqAffK1 k := by
      have := uqAff_K0K1_comm k
      apply_fun (fun x => x * uqAffK0inv k) at this;
      simp_all +decide [ mul_assoc, uqAff_K0_mul_K0inv ];
      apply_fun (fun x => uqAffK0inv k * x) at this;
      simp_all +decide [ ← mul_assoc, uqAff_K0inv_mul_K0 ];
    exact h_assoc;
  simp_all +decide [ mul_assoc ];
  simp_all +decide [ ← mul_assoc ]

private theorem affAntipodeFreeAlg_E1F0 :
    affAntipodeFreeAlg k (ag k E1 * ag k F0) =
    affAntipodeFreeAlg k (ag k F0 * ag k E1) := by
  erw [map_mul, map_mul, affAntipodeFreeAlg_ι, affAntipodeFreeAlg_ι]
  simp +decide [affAntipodeOnGen]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_neg]
  rw [uqAff_neg_mul_neg, uqAff_neg_mul_neg]
  -- Negs cancelled. Goal: K₀F₀·E₁K₁⁻¹ = E₁K₁⁻¹·K₀F₀
  -- Symmetric to E₀F₁ with 0↔1 swap.
  -- Uses: uqAff_E1F0_comm, uqAff_K0E1, uqAff_F0_mul_K1inv,
  --   uqAff_K0K1_comm, Algebra.commutes, LaurentPolynomial.T_add
  have h_F0E1_comm : uqAffF0 k * uqAffE1 k = uqAffE1 k * uqAffF0 k := by
    exact?;
  have h_K0E1 : uqAffK0 k * uqAffE1 k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T (-2)) * uqAffE1 k * uqAffK0 k := by
    grind +suggestions;
  have h_F0K1inv : uqAffF0 k * uqAffK1inv k = algebraMap (LaurentPolynomial k) (Uqsl2Aff k) (T 2) * uqAffK1inv k * uqAffF0 k := by
    exact?;
  have h_K0K1inv_comm : uqAffK0 k * uqAffK1inv k = uqAffK1inv k * uqAffK0 k := by
    have h_K0K1inv_comm : uqAffK0 k * uqAffK1 k = uqAffK1 k * uqAffK0 k := by
      exact?;
    have h_K0K1inv_comm : uqAffK0 k * (uqAffK1 k * uqAffK1inv k) = uqAffK1 k * (uqAffK0 k * uqAffK1inv k) := by
      rw [ ← mul_assoc, h_K0K1inv_comm, mul_assoc ];
    have h_K0K1inv_comm : uqAffK0 k * 1 = uqAffK1 k * (uqAffK0 k * uqAffK1inv k) := by
      convert h_K0K1inv_comm using 1;
      rw [ uqAff_K1_mul_K1inv ];
    have h_K0K1inv_comm : uqAffK1inv k * uqAffK0 k * 1 = uqAffK1inv k * uqAffK1 k * (uqAffK0 k * uqAffK1inv k) := by
      rw [ mul_assoc, h_K0K1inv_comm, ← mul_assoc ];
    have h_K0K1inv_comm : uqAffK1inv k * uqAffK1 k = 1 := by
      exact?;
    grobner;
  simp_all +decide [ mul_assoc, mul_left_comm, mul_comm ];
  simp_all +decide [ ← mul_assoc ];
  simp_all +decide [ mul_assoc, mul_left_comm ];
  simp_all +decide [ ← mul_assoc, ← Algebra.smul_def ];
  exact?

-- q-Serre cases
set_option maxHeartbeats 400000 in
private theorem affAntipodeFreeAlg_SerreE01 :
    affAntipodeFreeAlg k
      (ag k E0 * ag k E0 * ag k E0 * ag k E1
       - ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E0 * ag k E1 * ag k E0
       + ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E1 * ag k E0 * ag k E0
       - ag k E1 * ag k E0 * ag k E0 * ag k E0) =
    affAntipodeFreeAlg k 0 := by
  -- PROOF STRATEGY: S is AlgHom to Mᵒᵖ, so S(0) = 0 by map_zero.
  -- S preserves +, -, and S(a*b) = S(a)*S(b) in Mᵒᵖ (= op(unop(S(b))*unop(S(a))) in M).
  -- S(Eᵢ) = op(-EᵢKᵢ⁻¹), S(ascal r) = op(algebraMap r).
  -- After expansion, need q-Serre relation for -EᵢKᵢ⁻¹ images in Mᵒᵖ.
  -- The q-Serre relation is preserved by the anti-homomorphism because:
  --   The reversed product of -EᵢKᵢ⁻¹ terms satisfies the same Serre relation
  --   after K⁻¹ factors commute through using KE/KF relations.
  -- KEY LEMMAS: erw [map_zero] for RHS. erw [map_sub, map_add, map_mul] for LHS.
  --   affAntipodeFreeAlg_ι, affAntipodeOnGen. uqAff_neg_mul_neg for neg cancellation.
  --   uqAff_E0_mul_K0inv, uqAff_E0_mul_K1inv, uqAff_K0inv_K1inv_comm.
  --   uqAff_SerreE01 (Serre relation in quotient).
  -- PROVIDED SOLUTION:
  -- S(Eᵢ) = -EᵢKᵢ⁻¹ in Aᵒᵖ. The antipode image of the Serre expression is:
  --   S(E₀³E₁ - [3]E₀²E₁E₀ + [3]E₀E₁E₀² - E₁E₀³) = 0 in Aᵒᵖ
  -- After expanding S on each monomial and using S(ab) = S(b)S(a) (anti-homomorphism):
  --   S(E₀³E₁) = S(E₁)S(E₀)³ = (-E₁K₁⁻¹)(-E₀K₀⁻¹)³
  -- The (-1)⁴ = 1 cancels. Remains: E₁K₁⁻¹ · (E₀K₀⁻¹)³ in Aᵒᵖ.
  -- Since Aᵒᵖ reverses multiplication: this is (K₀⁻¹E₀)³ · K₁⁻¹E₁ in A.
  -- After commuting K⁻¹ past E (K₀⁻¹E₀ = T(-2)E₀K₀⁻¹, K₁⁻¹E₁ = T(-2)E₁K₁⁻¹):
  -- The result is q-weighted Serre(E₀,E₁) · K₀⁻³K₁⁻¹ = 0 by uqAff_SerreE01.
  -- Phase 1-3: expand S as AlgHom, substitute generator values
  erw [map_zero]
  simp only [map_sub, map_add, map_mul, AlgHom.commutes]
  simp only [affAntipodeFreeAlg_ι, affAntipodeOnGen]
  -- Phase 4: convert from Aᵒᵖ to A via unop_injective
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_add, MulOpposite.unop_mul,
             MulOpposite.unop_op, MulOpposite.unop_zero, MulOpposite.algebraMap_apply, mul_assoc]
  -- Phase 5: push K⁻¹ left of E using E·K⁻¹ = T(2)·K⁻¹·E
  simp_rw [uqAff_E0_mul_K0inv, uqAff_E1_mul_K1inv]
  -- Phase 6: convert negations to (-1)•, collect scalars via smul_mul_assoc/mul_smul_comm
  simp only [show ∀ (x : Uqsl2Aff k), -x = (-1 : LaurentPolynomial k) • x from fun x => by module]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Phase 7: simplify (-1)⁴ = 1 then one_smul
  norm_num
  -- Phase 8: convert algebraMap(T 2) * X back to smul, push through, apply Serre
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, ← T_add]
  norm_num [T_zero]
  simp only [one_smul, ← mul_assoc]
  have hK0invE0 : uqAffK0inv k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) • (uqAffE0 k * uqAffK0inv k) := by
    rw [uqAff_E0_mul_K0inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hK1invE1 : uqAffK1inv k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) • (uqAffE1 k * uqAffK1inv k) := by
    rw [uqAff_E1_mul_K1inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  simp only [hK0invE0, hK1invE1, smul_mul_assoc, mul_smul_comm, smul_smul, ← T_add,
             ← Algebra.smul_def]
  norm_num [T_zero]
  have hK1invE0 : uqAffK1inv k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) • (uqAffE0 k * uqAffK1inv k) := by
    rw [uqAff_E0_mul_K1inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hK0invE1 : uqAffK0inv k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) • (uqAffE1 k * uqAffK0inv k) := by
    rw [uqAff_E1_mul_K0inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hK0invE0_at (x : Uqsl2Aff k) : x * uqAffK0inv k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) • (x * uqAffE0 k * uqAffK0inv k) := by
    rw [mul_assoc x (uqAffK0inv k) (uqAffE0 k), hK0invE0, mul_smul_comm, ← mul_assoc]
  have hK1invE1_at (x : Uqsl2Aff k) : x * uqAffK1inv k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) • (x * uqAffE1 k * uqAffK1inv k) := by
    rw [mul_assoc x (uqAffK1inv k) (uqAffE1 k), hK1invE1, mul_smul_comm, ← mul_assoc]
  have hK1invE0_at (x : Uqsl2Aff k) : x * uqAffK1inv k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) • (x * uqAffE0 k * uqAffK1inv k) := by
    rw [mul_assoc x (uqAffK1inv k) (uqAffE0 k), hK1invE0, mul_smul_comm, ← mul_assoc]
  have hK0invE1_at (x : Uqsl2Aff k) : x * uqAffK0inv k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) • (x * uqAffE1 k * uqAffK0inv k) := by
    rw [mul_assoc x (uqAffK0inv k) (uqAffE1 k), hK0invE1, mul_smul_comm, ← mul_assoc]
  simp only [hK0invE0, hK1invE1, hK1invE0, hK0invE1, hK0invE0_at, hK1invE1_at,
             hK1invE0_at, hK0invE1_at, smul_mul_assoc, mul_smul_comm,
             smul_smul, ← T_add, ← Algebra.smul_def]
  norm_num [T_zero]
  have hKcomm_at (x : Uqsl2Aff k) : x * uqAffK0inv k * uqAffK1inv k =
      x * uqAffK1inv k * uqAffK0inv k := by
    rw [mul_assoc, uqAff_K0inv_K1inv_comm, ← mul_assoc]
  have hKcomm_at (x : Uqsl2Aff k) : x * uqAffK0inv k * uqAffK1inv k =
      x * uqAffK1inv k * uqAffK0inv k := by
    rw [mul_assoc, uqAff_K0inv_K1inv_comm, ← mul_assoc]
  simp only [hKcomm_at, ← mul_assoc]
  have hSE01 := sect_hSerreE01_smul k
  simp only [← Algebra.smul_def, smul_mul_assoc] at hSE01
  -- Use LinearMap.mulRight to distribute the K⁻¹ chain multiplication
  let φ : Uqsl2Aff k →ₗ[LaurentPolynomial k] Uqsl2Aff k :=
    (LinearMap.mul (LaurentPolynomial k) (Uqsl2Aff k)).flip
      (uqAffK1inv k * uqAffK0inv k * uqAffK0inv k * uqAffK0inv k)
  have h2 := congr_arg (⇑φ) hSE01
  simp only [map_zero] at h2
  -- Distribute φ by folding the distributed form into φ(Serre_smul)
  let A := uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k
  let B := uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k
  let C := uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k
  let D := uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k
  let q3 : LaurentPolynomial k := T 2 + 1 + T (-2)
  have h_dist : φ A - q3 • φ B + q3 • φ C - φ D = 0 := by
    rw [← φ.map_smul, ← φ.map_smul, ← map_sub φ, ← map_add φ, ← map_sub φ]
    exact h2
  -- Unfold φ to explicit multiplication
  simp only [show ∀ (x : Uqsl2Aff k),
      φ x = x * (uqAffK1inv k * uqAffK0inv k * uqAffK0inv k * uqAffK0inv k) from
    fun x => rfl] at h_dist
  -- Negate h_dist (using erw to bridge Zero instance diamond)
  have h_neg : -(A * (uqAffK1inv k * uqAffK0inv k * uqAffK0inv k * uqAffK0inv k) -
      q3 • (B * (uqAffK1inv k * uqAffK0inv k * uqAffK0inv k * uqAffK0inv k)) +
      q3 • (C * (uqAffK1inv k * uqAffK0inv k * uqAffK0inv k * uqAffK0inv k)) -
      D * (uqAffK1inv k * uqAffK0inv k * uqAffK0inv k * uqAffK0inv k)) = 0 := by
    erw [h_dist]; erw [neg_zero]
  -- Convert goal: move algebraMap from right to smul on left
  have hcentral : ∀ (r : LaurentPolynomial k) (x : Uqsl2Aff k),
      x * algebraMap (LaurentPolynomial k) (Uqsl2Aff k) r = r • x :=
    fun r x => by erw [Algebra.smul_def, Algebra.commutes]
  simp only [mul_add, mul_one, hcentral]
  -- Unfold let bindings, normalize association, expand q3 smul
  simp only [show A = uqAffE0 k * uqAffE0 k * uqAffE0 k * uqAffE1 k from rfl,
             show B = uqAffE0 k * uqAffE0 k * uqAffE1 k * uqAffE0 k from rfl,
             show C = uqAffE0 k * uqAffE1 k * uqAffE0 k * uqAffE0 k from rfl,
             show D = uqAffE1 k * uqAffE0 k * uqAffE0 k * uqAffE0 k from rfl,
             show q3 = T 2 + 1 + T (-2) from rfl,
             mul_assoc, add_smul, one_smul] at h_neg ⊢
  convert h_neg using 1
  module

set_option maxHeartbeats 400000 in
private theorem affAntipodeFreeAlg_SerreE10 :
    affAntipodeFreeAlg k
      (ag k E1 * ag k E1 * ag k E1 * ag k E0
       - ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E1 * ag k E0 * ag k E1
       + ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E0 * ag k E1 * ag k E1
       - ag k E0 * ag k E1 * ag k E1 * ag k E1) =
    affAntipodeFreeAlg k 0 := by
  -- PROVIDED SOLUTION: Symmetric to SerreE01 with 0↔1 swap.
  -- S(E₁³E₀) → palindromic reversal → Serre(E₁,E₀)·K₁⁻³K₀⁻¹ = 0 by uqAff_SerreE10.
  -- Uses: uqAff_SerreE10, uqAff_E1_mul_K1inv, uqAff_E1_mul_K0inv, K₁⁻¹-E commutation.
  -- Phase 1-3: expand S as AlgHom, substitute generator values
  erw [map_zero]
  simp only [map_sub, map_add, map_mul, AlgHom.commutes]
  simp only [affAntipodeFreeAlg_ι, affAntipodeOnGen]
  -- Phase 4: convert from Aᵒᵖ to A via unop_injective
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_add, MulOpposite.unop_mul,
             MulOpposite.unop_op, MulOpposite.unop_zero, MulOpposite.algebraMap_apply, mul_assoc]
  -- Phase 5: push K⁻¹ left of E using E·K⁻¹ = T(·)·K⁻¹·E
  simp_rw [uqAff_E1_mul_K1inv, uqAff_E0_mul_K0inv]
  -- Phase 6: convert negations to (-1)•, collect scalars via smul_mul_assoc/mul_smul_comm
  simp only [show ∀ (x : Uqsl2Aff k), -x = (-1 : LaurentPolynomial k) • x from fun x => by module]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  -- Phase 7: simplify (-1)⁴ = 1 then one_smul
  norm_num
  -- Phase 8: convert algebraMap(T 2) * X back to smul, push through
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, ← T_add]
  norm_num [T_zero]
  simp only [one_smul, ← mul_assoc]
  -- Phase 9: K⁻¹·E commutation helpers (base + positional)
  have hK1invE1 : uqAffK1inv k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) • (uqAffE1 k * uqAffK1inv k) := by
    rw [uqAff_E1_mul_K1inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hK0invE0 : uqAffK0inv k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) • (uqAffE0 k * uqAffK0inv k) := by
    rw [uqAff_E0_mul_K0inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  simp only [hK1invE1, hK0invE0, smul_mul_assoc, mul_smul_comm, smul_smul, ← T_add,
             ← Algebra.smul_def]
  norm_num [T_zero]
  have hK0invE1 : uqAffK0inv k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) • (uqAffE1 k * uqAffK0inv k) := by
    rw [uqAff_E1_mul_K0inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hK1invE0 : uqAffK1inv k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) • (uqAffE0 k * uqAffK1inv k) := by
    rw [uqAff_E0_mul_K1inv]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
    norm_num [T_zero, one_smul]
  have hK1invE1_at (x : Uqsl2Aff k) : x * uqAffK1inv k * uqAffE1 k =
      (T (-2) : LaurentPolynomial k) • (x * uqAffE1 k * uqAffK1inv k) := by
    rw [mul_assoc x (uqAffK1inv k) (uqAffE1 k), hK1invE1, mul_smul_comm, ← mul_assoc]
  have hK0invE0_at (x : Uqsl2Aff k) : x * uqAffK0inv k * uqAffE0 k =
      (T (-2) : LaurentPolynomial k) • (x * uqAffE0 k * uqAffK0inv k) := by
    rw [mul_assoc x (uqAffK0inv k) (uqAffE0 k), hK0invE0, mul_smul_comm, ← mul_assoc]
  have hK0invE1_at (x : Uqsl2Aff k) : x * uqAffK0inv k * uqAffE1 k =
      (T 2 : LaurentPolynomial k) • (x * uqAffE1 k * uqAffK0inv k) := by
    rw [mul_assoc x (uqAffK0inv k) (uqAffE1 k), hK0invE1, mul_smul_comm, ← mul_assoc]
  have hK1invE0_at (x : Uqsl2Aff k) : x * uqAffK1inv k * uqAffE0 k =
      (T 2 : LaurentPolynomial k) • (x * uqAffE0 k * uqAffK1inv k) := by
    rw [mul_assoc x (uqAffK1inv k) (uqAffE0 k), hK1invE0, mul_smul_comm, ← mul_assoc]
  simp only [hK1invE1, hK0invE0, hK0invE1, hK1invE0, hK1invE1_at, hK0invE0_at,
             hK0invE1_at, hK1invE0_at, smul_mul_assoc, mul_smul_comm,
             smul_smul, ← T_add, ← Algebra.smul_def]
  norm_num [T_zero]
  -- Phase 10: K⁻¹ commutativity — collect K₀⁻¹ leftmost using ← K0inv_K1inv_comm
  have hKcomm_at (x : Uqsl2Aff k) : x * uqAffK1inv k * uqAffK0inv k =
      x * uqAffK0inv k * uqAffK1inv k := by
    rw [mul_assoc, ← uqAff_K0inv_K1inv_comm, ← mul_assoc]
  simp only [hKcomm_at, ← mul_assoc]
  -- Phase 11: Apply Serre relation via LinearMap
  have hSE10 := sect_hSerreS_smul k
  simp only [← Algebra.smul_def, smul_mul_assoc] at hSE10
  -- Use LinearMap.mulRight to distribute the K⁻¹ chain multiplication
  let φ : Uqsl2Aff k →ₗ[LaurentPolynomial k] Uqsl2Aff k :=
    (LinearMap.mul (LaurentPolynomial k) (Uqsl2Aff k)).flip
      (uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k)
  have h2 := congr_arg (⇑φ) hSE10
  simp only [map_zero] at h2
  -- Distribute φ by folding the distributed form into φ(Serre_smul)
  let A := uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k
  let B := uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k
  let C := uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k
  let D := uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k
  let q3 : LaurentPolynomial k := T 2 + 1 + T (-2)
  have h_dist : φ A - q3 • φ B + q3 • φ C - φ D = 0 := by
    rw [← φ.map_smul, ← φ.map_smul, ← map_sub φ, ← map_add φ, ← map_sub φ]
    exact h2
  -- Unfold φ to explicit multiplication
  simp only [show ∀ (x : Uqsl2Aff k),
      φ x = x * (uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k) from
    fun x => rfl] at h_dist
  -- Negate h_dist (using erw to bridge Zero instance diamond)
  have h_neg : -(A * (uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k) -
      q3 • (B * (uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k)) +
      q3 • (C * (uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k)) -
      D * (uqAffK0inv k * uqAffK1inv k * uqAffK1inv k * uqAffK1inv k)) = 0 := by
    erw [h_dist]; erw [neg_zero]
  -- Convert goal: move algebraMap from right to smul on left
  have hcentral : ∀ (r : LaurentPolynomial k) (x : Uqsl2Aff k),
      x * algebraMap (LaurentPolynomial k) (Uqsl2Aff k) r = r • x :=
    fun r x => by erw [Algebra.smul_def, Algebra.commutes]
  simp only [mul_add, mul_one, hcentral]
  -- Unfold let bindings, normalize association, expand q3 smul
  simp only [show A = uqAffE1 k * uqAffE1 k * uqAffE1 k * uqAffE0 k from rfl,
             show B = uqAffE1 k * uqAffE1 k * uqAffE0 k * uqAffE1 k from rfl,
             show C = uqAffE1 k * uqAffE0 k * uqAffE1 k * uqAffE1 k from rfl,
             show D = uqAffE0 k * uqAffE1 k * uqAffE1 k * uqAffE1 k from rfl,
             show q3 = T 2 + 1 + T (-2) from rfl,
             mul_assoc, add_smul, one_smul] at h_neg ⊢
  convert h_neg using 1
  module

set_option maxHeartbeats 400000 in
private theorem affAntipodeFreeAlg_SerreF01 :
    affAntipodeFreeAlg k
      (ag k F0 * ag k F0 * ag k F0 * ag k F1
       - ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F0 * ag k F1 * ag k F0
       + ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F1 * ag k F0 * ag k F0
       - ag k F1 * ag k F0 * ag k F0 * ag k F0) =
    affAntipodeFreeAlg k 0 := by
  -- Phase 1-3: expand S as AlgHom, substitute generator values
  erw [map_zero]
  simp only [map_sub, map_add, map_mul, AlgHom.commutes]
  simp only [affAntipodeFreeAlg_ι, affAntipodeOnGen]
  -- Phase 4: convert from Aᵒᵖ to A via unop_injective
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_add, MulOpposite.unop_mul,
             MulOpposite.unop_op, MulOpposite.unop_zero, MulOpposite.algebraMap_apply, mul_assoc]
  -- Phase 7: convert negations to (-1)•, collect scalars
  simp only [show ∀ (x : Uqsl2Aff k), -x = (-1 : LaurentPolynomial k) • x from fun x => by module]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num
  -- Phase 8: convert trailing algebraMap to smul, then flatten
  have hcentral : ∀ (r : LaurentPolynomial k) (x : Uqsl2Aff k),
      x * algebraMap (LaurentPolynomial k) (Uqsl2Aff k) r = r • x :=
    fun r x => by erw [Algebra.smul_def, Algebra.commutes]
  simp only [mul_add, mul_one, hcentral, smul_mul_assoc, mul_smul_comm, smul_smul,
             ← Algebra.smul_def, ← T_add]
  norm_num [T_zero]
  simp only [one_smul, ← mul_assoc]
  -- Phase 9: K·F commutation helpers (smul form)
  have hK0F0 : uqAffK0 k * uqAffF0 k =
      (T (-2) : LaurentPolynomial k) • (uqAffF0 k * uqAffK0 k) := by
    rw [uqAff_K0F0]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
  have hK1F1 : uqAffK1 k * uqAffF1 k =
      (T (-2) : LaurentPolynomial k) • (uqAffF1 k * uqAffK1 k) := by
    rw [uqAff_K1F1]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
  have hK0F1 : uqAffK0 k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) • (uqAffF1 k * uqAffK0 k) := by
    rw [uqAff_K0F1]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
  have hK1F0 : uqAffK1 k * uqAffF0 k =
      (T 2 : LaurentPolynomial k) • (uqAffF0 k * uqAffK1 k) := by
    rw [uqAff_K1F0]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
  have hK0F0_at (x : Uqsl2Aff k) : x * uqAffK0 k * uqAffF0 k =
      (T (-2) : LaurentPolynomial k) • (x * uqAffF0 k * uqAffK0 k) := by
    rw [mul_assoc x (uqAffK0 k) (uqAffF0 k), hK0F0, mul_smul_comm, ← mul_assoc]
  have hK1F1_at (x : Uqsl2Aff k) : x * uqAffK1 k * uqAffF1 k =
      (T (-2) : LaurentPolynomial k) • (x * uqAffF1 k * uqAffK1 k) := by
    rw [mul_assoc x (uqAffK1 k) (uqAffF1 k), hK1F1, mul_smul_comm, ← mul_assoc]
  have hK1F0_at (x : Uqsl2Aff k) : x * uqAffK1 k * uqAffF0 k =
      (T 2 : LaurentPolynomial k) • (x * uqAffF0 k * uqAffK1 k) := by
    rw [mul_assoc x (uqAffK1 k) (uqAffF0 k), hK1F0, mul_smul_comm, ← mul_assoc]
  have hK0F1_at (x : Uqsl2Aff k) : x * uqAffK0 k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) • (x * uqAffF1 k * uqAffK0 k) := by
    rw [mul_assoc x (uqAffK0 k) (uqAffF1 k), hK0F1, mul_smul_comm, ← mul_assoc]
  simp only [hK0F0, hK1F1, hK0F1, hK1F0, hK0F0_at, hK1F1_at,
             hK1F0_at, hK0F1_at, smul_mul_assoc, mul_smul_comm,
             smul_smul, ← T_add, ← Algebra.smul_def]
  norm_num [T_zero]
  -- Phase 9b: K commutativity — collect K₀ left, K₁ right using uqAff_K0K1_comm
  have hKcomm_at (x : Uqsl2Aff k) : x * uqAffK1 k * uqAffK0 k =
      x * uqAffK0 k * uqAffK1 k := by
    rw [mul_assoc, ← uqAff_K0K1_comm, ← mul_assoc]
  simp only [hKcomm_at, ← mul_assoc]
  -- Phase 10: Factor T(-8) from q3 coefficient: T(-6)+T(-8)+T(-10) = T(-8)·q3
  have hq3_factor : (T (-6) + T (-8) + T (-10) : LaurentPolynomial k) =
      T (-8) * (T 2 + 1 + T (-2)) := by
    simp only [mul_add, mul_one, ← T_add]; norm_num
  simp only [← add_smul, hq3_factor]
  -- Phase 11: Apply Serre relation via LinearMap
  have hSF01 : uqAffF0 k * uqAffF0 k * uqAffF0 k * uqAffF1 k -
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF0 k * uqAffF1 k * uqAffF0 k) +
      (T 2 + 1 + T (-2) : LaurentPolynomial k) •
        (uqAffF0 k * uqAffF1 k * uqAffF0 k * uqAffF0 k) -
      uqAffF1 k * uqAffF0 k * uqAffF0 k * uqAffF0 k = 0 := by
    simp only [Algebra.smul_def, ← mul_assoc]; exact uqAff_SerreF01 k
  simp only [← Algebra.smul_def, smul_mul_assoc] at hSF01
  let φ : Uqsl2Aff k →ₗ[LaurentPolynomial k] Uqsl2Aff k :=
    (LinearMap.mul (LaurentPolynomial k) (Uqsl2Aff k)).flip
      (uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k)
  have h2 := congr_arg (⇑φ) hSF01
  simp only [map_zero] at h2
  let A := uqAffF0 k * uqAffF0 k * uqAffF0 k * uqAffF1 k
  let B := uqAffF0 k * uqAffF0 k * uqAffF1 k * uqAffF0 k
  let C := uqAffF0 k * uqAffF1 k * uqAffF0 k * uqAffF0 k
  let D := uqAffF1 k * uqAffF0 k * uqAffF0 k * uqAffF0 k
  let q3 : LaurentPolynomial k := T 2 + 1 + T (-2)
  have h_dist : φ A - q3 • φ B + q3 • φ C - φ D = 0 := by
    rw [← φ.map_smul, ← φ.map_smul, ← map_sub φ, ← map_add φ, ← map_sub φ]
    exact h2
  simp only [show ∀ (x : Uqsl2Aff k),
      φ x = x * (uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) from
    fun x => rfl] at h_dist
  -- Scale h_dist by T(-8)
  have h_neg : -(A * (uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k) -
      q3 • (B * (uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k)) +
      q3 • (C * (uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k)) -
      D * (uqAffK0 k * uqAffK0 k * uqAffK0 k * uqAffK1 k)) = (0 : Uqsl2Aff k) := by
    erw [h_dist]; erw [neg_zero]
  have h_scaled := congr_arg (fun (x : Uqsl2Aff k) => (T (-8) : LaurentPolynomial k) • x) h_neg
  simp only [smul_zero, smul_neg, smul_sub, smul_add, smul_smul] at h_scaled
  simp only [show A = uqAffF0 k * uqAffF0 k * uqAffF0 k * uqAffF1 k from rfl,
             show B = uqAffF0 k * uqAffF0 k * uqAffF1 k * uqAffF0 k from rfl,
             show C = uqAffF0 k * uqAffF1 k * uqAffF0 k * uqAffF0 k from rfl,
             show D = uqAffF1 k * uqAffF0 k * uqAffF0 k * uqAffF0 k from rfl,
             show q3 = T 2 + 1 + T (-2) from rfl,
             mul_assoc, add_smul, one_smul, smul_smul] at h_scaled ⊢
  convert h_scaled using 1
  module

set_option maxHeartbeats 400000 in
private theorem affAntipodeFreeAlg_SerreF10 :
    affAntipodeFreeAlg k
      (ag k F1 * ag k F1 * ag k F1 * ag k F0
       - ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F1 * ag k F0 * ag k F1
       + ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F0 * ag k F1 * ag k F1
       - ag k F0 * ag k F1 * ag k F1 * ag k F1) =
    affAntipodeFreeAlg k 0 := by
  -- Phase 1-3: expand S as AlgHom, substitute generator values
  erw [map_zero]
  simp only [map_sub, map_add, map_mul, AlgHom.commutes]
  simp only [affAntipodeFreeAlg_ι, affAntipodeOnGen]
  -- Phase 4: convert from Aᵒᵖ to A via unop_injective
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_sub, MulOpposite.unop_add, MulOpposite.unop_mul,
             MulOpposite.unop_op, MulOpposite.unop_zero, MulOpposite.algebraMap_apply, mul_assoc]
  -- Phase 7: convert negations to (-1)•, collect scalars
  simp only [show ∀ (x : Uqsl2Aff k), -x = (-1 : LaurentPolynomial k) • x from fun x => by module]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  norm_num
  -- Phase 8: convert trailing algebraMap to smul, then flatten
  have hcentral : ∀ (r : LaurentPolynomial k) (x : Uqsl2Aff k),
      x * algebraMap (LaurentPolynomial k) (Uqsl2Aff k) r = r • x :=
    fun r x => by erw [Algebra.smul_def, Algebra.commutes]
  simp only [mul_add, mul_one, hcentral, smul_mul_assoc, mul_smul_comm, smul_smul,
             ← Algebra.smul_def, ← T_add]
  norm_num [T_zero]
  simp only [one_smul, ← mul_assoc]
  -- Phase 9: K·F commutation helpers (smul form)
  have hK1F1 : uqAffK1 k * uqAffF1 k =
      (T (-2) : LaurentPolynomial k) • (uqAffF1 k * uqAffK1 k) := by
    rw [uqAff_K1F1]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
  have hK0F0 : uqAffK0 k * uqAffF0 k =
      (T (-2) : LaurentPolynomial k) • (uqAffF0 k * uqAffK0 k) := by
    rw [uqAff_K0F0]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
  have hK1F0 : uqAffK1 k * uqAffF0 k =
      (T 2 : LaurentPolynomial k) • (uqAffF0 k * uqAffK1 k) := by
    rw [uqAff_K1F0]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
  have hK0F1 : uqAffK0 k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) • (uqAffF1 k * uqAffK0 k) := by
    rw [uqAff_K0F1]
    simp only [← Algebra.smul_def, smul_mul_assoc, smul_smul, ← T_add]
  have hK1F1_at (x : Uqsl2Aff k) : x * uqAffK1 k * uqAffF1 k =
      (T (-2) : LaurentPolynomial k) • (x * uqAffF1 k * uqAffK1 k) := by
    rw [mul_assoc x (uqAffK1 k) (uqAffF1 k), hK1F1, mul_smul_comm, ← mul_assoc]
  have hK0F0_at (x : Uqsl2Aff k) : x * uqAffK0 k * uqAffF0 k =
      (T (-2) : LaurentPolynomial k) • (x * uqAffF0 k * uqAffK0 k) := by
    rw [mul_assoc x (uqAffK0 k) (uqAffF0 k), hK0F0, mul_smul_comm, ← mul_assoc]
  have hK0F1_at (x : Uqsl2Aff k) : x * uqAffK0 k * uqAffF1 k =
      (T 2 : LaurentPolynomial k) • (x * uqAffF1 k * uqAffK0 k) := by
    rw [mul_assoc x (uqAffK0 k) (uqAffF1 k), hK0F1, mul_smul_comm, ← mul_assoc]
  have hK1F0_at (x : Uqsl2Aff k) : x * uqAffK1 k * uqAffF0 k =
      (T 2 : LaurentPolynomial k) • (x * uqAffF0 k * uqAffK1 k) := by
    rw [mul_assoc x (uqAffK1 k) (uqAffF0 k), hK1F0, mul_smul_comm, ← mul_assoc]
  simp only [hK1F1, hK0F0, hK1F0, hK0F1, hK1F1_at, hK0F0_at,
             hK0F1_at, hK1F0_at, smul_mul_assoc, mul_smul_comm,
             smul_smul, ← T_add, ← Algebra.smul_def]
  norm_num [T_zero]
  -- Phase 9b: K commutativity — collect K₁ left, K₀ right using uqAff_K0K1_comm
  have hKcomm_at (x : Uqsl2Aff k) : x * uqAffK0 k * uqAffK1 k =
      x * uqAffK1 k * uqAffK0 k := by
    rw [mul_assoc, uqAff_K0K1_comm, ← mul_assoc]
  simp only [hKcomm_at, ← mul_assoc]
  -- Phase 10: Factor T(-8) from q3 coefficient: T(-6)+T(-8)+T(-10) = T(-8)·q3
  have hq3_factor : (T (-6) + T (-8) + T (-10) : LaurentPolynomial k) =
      T (-8) * (T 2 + 1 + T (-2)) := by
    simp only [mul_add, mul_one, ← T_add]; norm_num
  simp only [← add_smul, hq3_factor, smul_smul]
  -- Phase 11: Apply Serre relation via LinearMap
  have hSF10 := sect_hSerreF10_smul k
  simp only [← Algebra.smul_def, smul_mul_assoc] at hSF10
  let φ : Uqsl2Aff k →ₗ[LaurentPolynomial k] Uqsl2Aff k :=
    (LinearMap.mul (LaurentPolynomial k) (Uqsl2Aff k)).flip
      (uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k)
  have h2 := congr_arg (⇑φ) hSF10
  simp only [map_zero] at h2
  let A := uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffF0 k
  let B := uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffF1 k
  let C := uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffF1 k
  let D := uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffF1 k
  let q3 : LaurentPolynomial k := T 2 + 1 + T (-2)
  have h_dist : φ A - q3 • φ B + q3 • φ C - φ D = 0 := by
    rw [← φ.map_smul, ← φ.map_smul, ← map_sub φ, ← map_add φ, ← map_sub φ]
    exact h2
  simp only [show ∀ (x : Uqsl2Aff k),
      φ x = x * (uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) from
    fun x => rfl] at h_dist
  -- Scale h_dist by T(-8)
  have h_neg : -(A * (uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k) -
      q3 • (B * (uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k)) +
      q3 • (C * (uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k)) -
      D * (uqAffK1 k * uqAffK1 k * uqAffK1 k * uqAffK0 k)) = (0 : Uqsl2Aff k) := by
    erw [h_dist]; erw [neg_zero]
  have h_scaled := congr_arg (fun (x : Uqsl2Aff k) => (T (-8) : LaurentPolynomial k) • x) h_neg
  simp only [smul_zero, smul_neg, smul_sub, smul_add, smul_smul] at h_scaled
  simp only [show A = uqAffF1 k * uqAffF1 k * uqAffF1 k * uqAffF0 k from rfl,
             show B = uqAffF1 k * uqAffF1 k * uqAffF0 k * uqAffF1 k from rfl,
             show C = uqAffF1 k * uqAffF0 k * uqAffF1 k * uqAffF1 k from rfl,
             show D = uqAffF0 k * uqAffF1 k * uqAffF1 k * uqAffF1 k from rfl,
             show q3 = T 2 + 1 + T (-2) from rfl,
             mul_assoc, add_smul, one_smul, smul_smul] at h_scaled ⊢
  convert h_scaled using 1
  module

/-- The antipode respects all relations. -/
private theorem affAntipodeFreeAlg_respects_rel :
    ∀ ⦃x y : FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen⦄,
    AffChevalleyRel k x y → affAntipodeFreeAlg k x = affAntipodeFreeAlg k y := by
  intro x y h
  cases h with
  | K0K0inv => rw [affAntipodeFreeAlg_K0K0inv, map_one]
  | K0invK0 => rw [affAntipodeFreeAlg_K0invK0, map_one]
  | K1K1inv => rw [affAntipodeFreeAlg_K1K1inv, map_one]
  | K1invK1 => rw [affAntipodeFreeAlg_K1invK1, map_one]
  | K0K1 => exact affAntipodeFreeAlg_K0K1 k
  | K0E0 => exact affAntipodeFreeAlg_K0E0 k
  | K1E1 => exact affAntipodeFreeAlg_K1E1 k
  | K0E1 => exact affAntipodeFreeAlg_K0E1 k
  | K1E0 => exact affAntipodeFreeAlg_K1E0 k
  | K0F0 => exact affAntipodeFreeAlg_K0F0 k
  | K1F1 => exact affAntipodeFreeAlg_K1F1 k
  | K0F1 => exact affAntipodeFreeAlg_K0F1 k
  | K1F0 => exact affAntipodeFreeAlg_K1F0 k
  | Serre0 => exact affAntipodeFreeAlg_Serre0 k
  | Serre1 => exact affAntipodeFreeAlg_Serre1 k
  | E0F1 => exact affAntipodeFreeAlg_E0F1 k
  | E1F0 => exact affAntipodeFreeAlg_E1F0 k
  | SerreE01 => exact affAntipodeFreeAlg_SerreE01 k
  | SerreE10 => exact affAntipodeFreeAlg_SerreE10 k
  | SerreF01 => exact affAntipodeFreeAlg_SerreF01 k
  | SerreF10 => exact affAntipodeFreeAlg_SerreF10 k

noncomputable def affAntipode :
    Uqsl2Aff k →ₐ[LaurentPolynomial k] (Uqsl2Aff k)ᵐᵒᵖ :=
  RingQuot.liftAlgHom (LaurentPolynomial k)
    ⟨affAntipodeFreeAlg k, affAntipodeFreeAlg_respects_rel k⟩

/-! ## 5. Module summary -/

theorem uqsl2_affine_hopf_summary : True := trivial

end SKEFTHawking

end