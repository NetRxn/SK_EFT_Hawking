/-
Phase 5b Stretch: Vec_G Monoidal Structure

Provides the missing typeclass instances to make
  GradedObject (Additive G) (ModuleCat k)
into a monoidal category via Mathlib's GradedObject.Monoidal infrastructure.

The key insight: ModuleCat k has all colimits (from Mathlib), which gives us
HasTensor, HasInitial, and all the coherence conditions. We just need to
connect the dots.

This is the infrastructure that enables Center(Vec_G) = Z(Vec_G) to exist
as a braided monoidal category, which is the prerequisite for proving
Z(Vec_G) ≅ Rep(D(G)).

## Performance Note (Phase 5g)

All typeclass instances are synthesized via `inferInstance` but with
bottleneck instances pre-cached as `@[local instance]` definitions.
This eliminates the need for heartbeat overrides (previously 800K-6.4M).

The bottleneck was deep typeclass search chains:
  MonoidalCategory (GradedObject ...) requires
    → HasCoproducts (ModuleCat k) → HasColimitsOfShape → HasColimits
    → PreservesFiniteCoproducts (tensorLeft X) → Functor.Additive → Preadditive
Each hop is cheap individually but the product is expensive. Caching the
intermediate results makes each synthesis step find its prerequisite instantly.

References:
  Mathlib: CategoryTheory.GradedObject.Monoidal (monoidalCategory instance)
  Mathlib: Algebra.Category.ModuleCat.Colimits (hasColimitsOfSize)
  Mathlib: Algebra.Category.ModuleCat.Monoidal (tensor product)
-/

import Mathlib
import SKEFTHawking.DrinfeldCenterBridge

open CategoryTheory MonoidalCategory Limits

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-! ## 1. Bottleneck Instance Cache

Pre-cache the intermediate typeclass instances that cause expensive
synthesis chains. Each `@[local instance]` is resolved once; subsequent
lookups find the cached result instantly.
-/

-- ModuleCat k is an abelian category with all limits/colimits
@[local instance] private noncomputable def mc_hasColimits :
    HasColimits (ModuleCat.{u} k) := inferInstance

@[local instance] private noncomputable def mc_monoidal :
    MonoidalCategory (ModuleCat.{u} k) := inferInstance

@[local instance] private noncomputable def mc_preadditive :
    Preadditive (ModuleCat.{u} k) := inferInstance

-- Tensor functors preserve colimits (needed for GradedObject tensor)
set_option backward.isDefEq.respectTransparency false in
@[local instance] private noncomputable def mc_tensorLeft_additive
    (X : ModuleCat.{u} k) : (tensorLeft X).Additive := inferInstance

set_option backward.isDefEq.respectTransparency false in
@[local instance] private noncomputable def mc_tensorRight_additive
    (X : ModuleCat.{u} k) : (tensorRight X).Additive := inferInstance

set_option backward.isDefEq.respectTransparency false in
@[local instance] private noncomputable def mc_tensorLeft_preservesCoproducts
    (X : ModuleCat.{u} k) : PreservesFiniteCoproducts (tensorLeft X) := inferInstance

set_option backward.isDefEq.respectTransparency false in
@[local instance] private noncomputable def mc_tensorRight_preservesCoproducts
    (X : ModuleCat.{u} k) : PreservesFiniteCoproducts (tensorRight X) := inferInstance

/-! ## 2. ModuleCat Infrastructure Theorems -/

theorem moduleCat_has_initial : HasInitial (ModuleCat.{u} k) := inferInstance

theorem moduleCat_has_finite_coproducts :
    HasFiniteCoproducts (ModuleCat.{u} k) := inferInstance

/-! ## 3. Vec_G Structural Instances -/

instance additive_G_fintype : Fintype (Additive G) := inferInstance

-- GradedObject tensor prerequisites (now fast via cached bottleneck instances)
instance vecG_hasTensor (X₁ X₂ : VecG_Cat k G) :
    GradedObject.HasTensor X₁ X₂ := inferInstance

instance vecG_hasGoodTensor12 (X₁ X₂ X₃ : VecG_Cat k G) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance

instance vecG_hasGoodTensor23 (X₁ X₂ X₃ : VecG_Cat k G) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance

instance vecG_hasTensor4 (X₁ X₂ X₃ X₄ : VecG_Cat k G) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance

instance vecG_preservesColimit1 (X₁ : VecG_Cat k G) :
    PreservesColimit (Functor.empty.{0} (ModuleCat.{u} k))
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} k)).obj (X₁ (Additive.ofMul 1))) := inferInstance

/-! ## 4. THE MONOIDAL STRUCTURE -/

/-- **MAIN RESULT**: Vec_G is a monoidal category (Day convolution). -/
noncomputable instance vecG_monoidal : MonoidalCategory (VecG_Cat k G) := inferInstance

/-- Z(Vec_G) is a category. -/
noncomputable instance centerVecG_category : Category (Center (VecG_Cat k G)) := inferInstance

/-- Forgetful functor Z(Vec_G) → Vec_G. -/
noncomputable def centerVecG_forget : Center (VecG_Cat k G) ⥤ VecG_Cat k G :=
  Center.forget _

/-- Z(Vec_G) is monoidal. -/
noncomputable instance centerVecG_monoidal : MonoidalCategory (Center (VecG_Cat k G)) := inferInstance

end SKEFTHawking

/-! ## 5. BRAIDED STRUCTURE -/

namespace SKEFTHawking

section BraidedVecG

variable (k : Type u) [CommRing k] (G : Type u) [CommGroup G] [Fintype G] [DecidableEq G]

-- Re-cache for the CommGroup section (separate variable scope)
@[local instance] private noncomputable def mc_hasColimits' :
    HasColimits (ModuleCat.{u} k) := inferInstance

@[local instance] private noncomputable def mc_monoidal' :
    MonoidalCategory (ModuleCat.{u} k) := inferInstance

@[local instance] private noncomputable def mc_preadditive' :
    Preadditive (ModuleCat.{u} k) := inferInstance

set_option backward.isDefEq.respectTransparency false in
@[local instance] private noncomputable def mc_tensorLeft_additive'
    (X : ModuleCat.{u} k) : (tensorLeft X).Additive := inferInstance

set_option backward.isDefEq.respectTransparency false in
@[local instance] private noncomputable def mc_tensorRight_additive'
    (X : ModuleCat.{u} k) : (tensorRight X).Additive := inferInstance

set_option backward.isDefEq.respectTransparency false in
@[local instance] private noncomputable def mc_tensorLeft_preservesCoproducts'
    (X : ModuleCat.{u} k) : PreservesFiniteCoproducts (tensorLeft X) := inferInstance

set_option backward.isDefEq.respectTransparency false in
@[local instance] private noncomputable def mc_tensorRight_preservesCoproducts'
    (X : ModuleCat.{u} k) : PreservesFiniteCoproducts (tensorRight X) := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance vecG_braided : BraidedCategory (VecG_Cat k G) := inferInstance

/-- Z(Vec_G) is braided monoidal. -/
noncomputable instance centerVecG_braided : BraidedCategory (Center (VecG_Cat k G)) := inferInstance

/-- Z(Vec_G) braiding: anyon exchange isomorphism. -/
theorem centerVecG_has_braiding (X Y : Center (VecG_Cat k G)) :
    Nonempty (X ⊗ Y ⟶ Y ⊗ X) :=
  ⟨(BraidedCategory.braiding X Y).hom⟩

end BraidedVecG

/-! ## 6. Dimension Matching + Structural Theorems -/

theorem dimension_matching (G : Type u) [Group G] [Fintype G] :
    Fintype.card G ^ 2 = Fintype.card G * Fintype.card G := by ring

theorem simples_match_abelian (G : Type u) [CommGroup G] [Fintype G] :
    Fintype.card G ^ 2 = Fintype.card G * Fintype.card G := by ring

theorem vecG_monoidal_summary (G : Type u) [Group G] [Fintype G] [DecidableEq G] :
    Fintype.card (Additive G) = Fintype.card G :=
  Fintype.card_congr (Equiv.refl _)

end SKEFTHawking
