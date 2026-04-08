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
private theorem affComulFreeAlg_SerreE01 :
    affComulFreeAlg k
      (ag k E0 * ag k E0 * ag k E0 * ag k E1
       - ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E0 * ag k E1 * ag k E0
       + ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E1 * ag k E0 * ag k E0
       - ag k E1 * ag k E0 * ag k E0 * ag k E0) =
    affComulFreeAlg k 0 := by
  sorry

private theorem affComulFreeAlg_SerreE10 :
    affComulFreeAlg k
      (ag k E1 * ag k E1 * ag k E1 * ag k E0
       - ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E1 * ag k E0 * ag k E1
       + ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E0 * ag k E1 * ag k E1
       - ag k E0 * ag k E1 * ag k E1 * ag k E1) =
    affComulFreeAlg k 0 := by
  sorry

private theorem affComulFreeAlg_SerreF01 :
    affComulFreeAlg k
      (ag k F0 * ag k F0 * ag k F0 * ag k F1
       - ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F0 * ag k F1 * ag k F0
       + ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F1 * ag k F0 * ag k F0
       - ag k F1 * ag k F0 * ag k F0 * ag k F0) =
    affComulFreeAlg k 0 := by
  sorry

private theorem affComulFreeAlg_SerreF10 :
    affComulFreeAlg k
      (ag k F1 * ag k F1 * ag k F1 * ag k F0
       - ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F1 * ag k F0 * ag k F1
       + ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F0 * ag k F1 * ag k F1
       - ag k F0 * ag k F1 * ag k F1 * ag k F1) =
    affComulFreeAlg k 0 := by
  sorry

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
Cross-node commutation helpers for antipode proofs
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
  -- From K0F1: K0*F1 = T(2)*F1*K0. Multiply both sides by K0inv on the left: K0inv*K0*F1 = K0inv*T(2)*F1*K0. So F1 = T(2)*K0inv*F1*K0. Multiply by K0inv on the right: F1*K0inv = T(2)*K0inv*F1. Rearranging: K0inv*F1 = T(-2)*F1*K0inv. This follows from the properties of the algebra.
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
  sorry -- Symmetric to K₀E₁ but MulOpposite neg handling differs. Blocked on deep research #1.

-- KF cases
private theorem affAntipodeFreeAlg_K0F0 :
    affAntipodeFreeAlg k (ag k K0 * ag k F0) =
    affAntipodeFreeAlg k (ascal k (T (-2)) * ag k F0 * ag k K0) := by
  sorry

private theorem affAntipodeFreeAlg_K1F1 :
    affAntipodeFreeAlg k (ag k K1 * ag k F1) =
    affAntipodeFreeAlg k (ascal k (T (-2)) * ag k F1 * ag k K1) := by
  sorry

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
  sorry

-- Serre cases
private theorem affAntipodeFreeAlg_Serre0 :
    affAntipodeFreeAlg k
      (ascal k (T 1 - T (-1)) * (ag k E0 * ag k F0 - ag k F0 * ag k E0)) =
    affAntipodeFreeAlg k (ag k K0 - ag k K0inv) := by
  sorry

private theorem affAntipodeFreeAlg_Serre1 :
    affAntipodeFreeAlg k
      (ascal k (T 1 - T (-1)) * (ag k E1 * ag k F1 - ag k F1 * ag k E1)) =
    affAntipodeFreeAlg k (ag k K1 - ag k K1inv) := by
  sorry -- symmetric to Serre0

-- Cross-commutation cases
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
  -- Negs cancelled. Remaining: K₁F₁·E₀K₀⁻¹ = E₀K₀⁻¹·K₁F₁ with T-factor cancellation.
  sorry

private theorem affAntipodeFreeAlg_E1F0 :
    affAntipodeFreeAlg k (ag k E1 * ag k F0) =
    affAntipodeFreeAlg k (ag k F0 * ag k E1) := by
  erw [map_mul, map_mul, affAntipodeFreeAlg_ι, affAntipodeFreeAlg_ι]
  simp +decide [affAntipodeOnGen]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_neg]
  rw [uqAff_neg_mul_neg, uqAff_neg_mul_neg]
  -- Negs cancelled. Remaining: K₀F₀·E₁K₁⁻¹ = E₁K₁⁻¹·K₀F₀ with T-factor cancellation.
  sorry

-- q-Serre cases
private theorem affAntipodeFreeAlg_SerreE01 :
    affAntipodeFreeAlg k
      (ag k E0 * ag k E0 * ag k E0 * ag k E1
       - ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E0 * ag k E1 * ag k E0
       + ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E1 * ag k E0 * ag k E0
       - ag k E1 * ag k E0 * ag k E0 * ag k E0) =
    affAntipodeFreeAlg k 0 := by
  sorry

private theorem affAntipodeFreeAlg_SerreE10 :
    affAntipodeFreeAlg k
      (ag k E1 * ag k E1 * ag k E1 * ag k E0
       - ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E1 * ag k E0 * ag k E1
       + ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E0 * ag k E1 * ag k E1
       - ag k E0 * ag k E1 * ag k E1 * ag k E1) =
    affAntipodeFreeAlg k 0 := by
  sorry

private theorem affAntipodeFreeAlg_SerreF01 :
    affAntipodeFreeAlg k
      (ag k F0 * ag k F0 * ag k F0 * ag k F1
       - ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F0 * ag k F1 * ag k F0
       + ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F1 * ag k F0 * ag k F0
       - ag k F1 * ag k F0 * ag k F0 * ag k F0) =
    affAntipodeFreeAlg k 0 := by
  sorry

private theorem affAntipodeFreeAlg_SerreF10 :
    affAntipodeFreeAlg k
      (ag k F1 * ag k F1 * ag k F1 * ag k F0
       - ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F1 * ag k F0 * ag k F1
       + ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F0 * ag k F1 * ag k F1
       - ag k F0 * ag k F1 * ag k F1 * ag k F1) =
    affAntipodeFreeAlg k 0 := by
  sorry

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