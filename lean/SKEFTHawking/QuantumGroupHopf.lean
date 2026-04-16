/-
Phase 5m Wave 2: Generic Hopf Algebra Structure on U_q(𝔤)

Complete Hopf algebra assembly for the generic quantum group QuantumGroup k A:
  - Counit ε: ε(E_i) = ε(F_i) = 0, ε(K_i) = ε(K_i⁻¹) = 1
  - Coalgebra axioms: coassociativity + both counit laws
  - Bialgebra instance via Bialgebra.ofAlgHom
  - Antipode as linear map + evaluation + anti-multiplicativity
  - Convolution multiplicativity steps (rTensor + lTensor)
  - Main convolution laws: m∘(S⊗id)∘Δ = η∘ε = m∘(id⊗S)∘Δ
  - HopfAlgebra instance

FULLY PROVED — ZERO sorry. First generic quantum group HopfAlgebra
in any proof assistant. Covers all symmetric Cartan matrices simultaneously.

References:
  Kassel, "Quantum Groups" (Springer, 1995), Ch. VI
  Lit-Search/Phase-5k-5l-5m-5n/Generic U_q(𝔤) quantum groups in Lean 4.md
-/

import Mathlib
import SKEFTHawking.QuantumGroupAntipode

open LaurentPolynomial

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k] {r : ℕ}

/-! ## 1. Counit on Generators -/

/-- The counit on generators: ε(E_i) = ε(F_i) = 0, ε(K_i) = ε(K_i⁻¹) = 1. -/
def counitOnGen : QGGen r → QBase k
  | .E _ => 0
  | .F _ => 0
  | .K _ => 1
  | .Kinv _ => 1

/-- The counit lifted to the free algebra via the universal property. -/
def counitFreeAlg : FreeAlgebra (QBase k) (QGGen r) →ₐ[QBase k] QBase k :=
  FreeAlgebra.lift (QBase k) (counitOnGen k)

/-! ## 2. Counit Respects All Relations -/

/-- The counit respects ALL QGRel relations, enabling descent to the quotient.

All 11 cases close by `simp` because every E and F generator maps to 0,
making all terms involving E or F vanish. K and K⁻¹ both map to 1,
so K-invertibility and K-commutativity are trivial. -/
theorem counit_respects_rel (A : Matrix (Fin r) (Fin r) ℤ) :
    ∀ a b, @QGRel k _ r A a b → counitFreeAlg k a = counitFreeAlg k b := by
  intro a b h
  induction h with
  | KKinv i =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen]
  | KinvK i =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen]
  | KK_comm i j =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen]
  | KE i j =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen, map_mul, AlgHom.commutes]
  | KF i j =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen, map_mul, AlgHom.commutes]
  | EF_diag i =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen, map_mul, map_sub, AlgHom.commutes]
  | EF_off i j _ =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen, map_mul]
  | SerreE_comm i j _ _ =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen, map_mul]
  | SerreE_quad i j _ =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen, map_mul, map_add, map_pow, AlgHom.commutes]
  | SerreF_comm i j _ _ =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen, map_mul]
  | SerreF_quad i j _ =>
    simp [counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen, map_mul, map_add, map_pow, AlgHom.commutes]

/-! ## 3. Counit on the Quotient -/

/--
**The counit on U_q(𝔤)**: ε : QuantumGroup k A → k[q,q⁻¹].

The augmentation homomorphism, fully proved for all Cartan matrices.
Descends from the free algebra counit via `RingQuot.liftAlgHom`.
-/
noncomputable def qgCounit (A : Matrix (Fin r) (Fin r) ℤ) :
    QuantumGroup k A →ₐ[QBase k] QBase k :=
  RingQuot.liftAlgHom (QBase k) ⟨counitFreeAlg k, counit_respects_rel k A⟩

/-- ε(E_i) = 0 in U_q(𝔤). -/
theorem qgCounit_E (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    qgCounit k A (qgE k A i) = 0 := by
  simp [qgCounit, qgE, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen]

/-- ε(F_i) = 0 in U_q(𝔤). -/
theorem qgCounit_F (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    qgCounit k A (qgF k A i) = 0 := by
  simp [qgCounit, qgF, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen]

/-- ε(K_i) = 1 in U_q(𝔤). -/
theorem qgCounit_K (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    qgCounit k A (qgK k A i) = 1 := by
  simp [qgCounit, qgK, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen]

/-- ε(K_i⁻¹) = 1 in U_q(𝔤). -/
theorem qgCounit_Kinv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    qgCounit k A (qgKinv k A i) = 1 := by
  simp [qgCounit, qgKinv, qgMk, RingQuot.liftAlgHom_mkAlgHom_apply,
    counitFreeAlg, FreeAlgebra.lift_ι_apply, counitOnGen]

/-! ## 4. Coalgebra axioms

Coassociativity and counit laws, proved generator-by-generator via ext. -/

variable {A : Matrix (Fin r) (Fin r) ℤ}
  (hdiag : ∀ i : Fin r, A i i = 2)
  (hsym : ∀ i j : Fin r, A i j = A j i)

/-- Coassociativity: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ (modulo associator). -/
theorem qg_comul_coassoc :
    (Algebra.TensorProduct.assoc (QBase k) (QBase k) (QBase k)
      (QuantumGroup k A) (QuantumGroup k A) (QuantumGroup k A)).toAlgHom.comp
      ((Algebra.TensorProduct.map (qgComul k hdiag hsym)
        (.id (QBase k) (QuantumGroup k A))).comp
        (qgComul k hdiag hsym)) =
    (Algebra.TensorProduct.map (.id (QBase k) (QuantumGroup k A))
      (qgComul k hdiag hsym)).comp
      (qgComul k hdiag hsym) := by
  ext x
  rcases x with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    simp only [Function.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  · -- E_i
    erw [qgComul_E k hdiag hsym i]
    simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    erw [qgComul_E k hdiag hsym i, qgComul_K k hdiag hsym i]
    simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
    simp only [Algebra.TensorProduct.assoc_tmul]
    rw [Algebra.TensorProduct.one_def]
    simp only [Algebra.TensorProduct.assoc_tmul, add_assoc]
  · -- F_i
    erw [qgComul_F k hdiag hsym i]
    simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    erw [qgComul_F k hdiag hsym i, qgComul_Kinv k hdiag hsym i]
    simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
    simp only [Algebra.TensorProduct.assoc_tmul]
    rw [Algebra.TensorProduct.one_def]
    simp only [Algebra.TensorProduct.assoc_tmul, add_assoc]
  · -- K_i
    erw [qgComul_K k hdiag hsym i]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    erw [qgComul_K k hdiag hsym i]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.assoc_tmul]
  · -- Kinv_i
    erw [qgComul_Kinv k hdiag hsym i]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    erw [qgComul_Kinv k hdiag hsym i]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.assoc_tmul]

/-- Right counitality: (ε ⊗ id) ∘ Δ = lid.symm. -/
theorem qg_comul_rTensor_counit :
    (Algebra.TensorProduct.map (qgCounit k A) (.id (QBase k) (QuantumGroup k A))).comp
      (qgComul k hdiag hsym) =
    (Algebra.TensorProduct.lid (QBase k) (QuantumGroup k A)).symm := by
  ext x
  rcases x with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    simp only [Function.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  all_goals simp only [qgComul, RingQuot.liftAlgHom_mkAlgHom_apply, comulFreeAlgQG,
    FreeAlgebra.lift_ι_apply, comulOnGenQG, map_add, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, qgCounit_E, qgCounit_F, qgCounit_K, qgCounit_Kinv, map_one,
    TensorProduct.zero_tmul, zero_add, Algebra.TensorProduct.lid_symm_apply]
  all_goals rfl

/-- Left counitality: (id ⊗ ε) ∘ Δ = rid.symm. -/
theorem qg_comul_lTensor_counit :
    (Algebra.TensorProduct.map (.id (QBase k) (QuantumGroup k A))
      (qgCounit k A)).comp (qgComul k hdiag hsym) =
    (Algebra.TensorProduct.rid (QBase k) (QBase k) (QuantumGroup k A)).symm := by
  ext x
  rcases x with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    simp only [Function.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  all_goals simp only [qgComul, RingQuot.liftAlgHom_mkAlgHom_apply, comulFreeAlgQG,
    FreeAlgebra.lift_ι_apply, comulOnGenQG, map_add, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, qgCounit_E, qgCounit_F, qgCounit_K, qgCounit_Kinv, map_one,
    TensorProduct.tmul_zero, add_zero, Algebra.TensorProduct.rid_symm_apply]
  all_goals rfl

/-! ## 5. Bialgebra instance -/

/-- **Bialgebra instance for U_q(𝔤).** -/
@[reducible] noncomputable def qgBialgebra :
    Bialgebra (QBase k) (QuantumGroup k A) :=
  Bialgebra.ofAlgHom (qgComul k hdiag hsym) (qgCounit k A)
    (qg_comul_coassoc k hdiag hsym)
    (qg_comul_rTensor_counit k hdiag hsym)
    (qg_comul_lTensor_counit k hdiag hsym)

/-! ## 6. Antipode as linear map -/

/-- **Antipode on U_q(𝔤)** as a linear map (composition of MulOpposite AlgHom + opLinearEquiv.symm). -/
noncomputable def qgAntipodeLin :
    QuantumGroup k A →ₗ[QBase k] QuantumGroup k A :=
  (MulOpposite.opLinearEquiv (QBase k)).symm.toLinearMap.comp
    (qgAntipode k hdiag hsym).toLinearMap

/-! ### Antipode linear map evaluation -/

theorem qgAntipodeLin_E (i : Fin r) :
    qgAntipodeLin k hdiag hsym (qgE k A i) = -(qgE k A i * qgKinv k A i) := by
  unfold qgAntipodeLin
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
  rw [qgAntipode_E]; rfl

theorem qgAntipodeLin_F (i : Fin r) :
    qgAntipodeLin k hdiag hsym (qgF k A i) = -(qgK k A i * qgF k A i) := by
  unfold qgAntipodeLin
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
  rw [qgAntipode_F]; rfl

theorem qgAntipodeLin_K (i : Fin r) :
    qgAntipodeLin k hdiag hsym (qgK k A i) = qgKinv k A i := by
  unfold qgAntipodeLin
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
  rw [qgAntipode_K]; rfl

theorem qgAntipodeLin_Kinv (i : Fin r) :
    qgAntipodeLin k hdiag hsym (qgKinv k A i) = qgK k A i := by
  unfold qgAntipodeLin
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap]
  rw [qgAntipode_Kinv]; rfl

theorem qgAntipodeLin_one :
    qgAntipodeLin k hdiag hsym (1 : QuantumGroup k A) = 1 := by
  unfold qgAntipodeLin
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap, map_one]
  rfl

/-! ## 7. Right convolution on generators -/

private theorem qg_convR_E (i : Fin r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.rTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym) (qgE k A i))) = 0 := by
  rw [qgComul_E]
  simp only [LinearMap.rTensor_tmul, map_add, LinearMap.mul'_apply]
  rw [qgAntipodeLin_E, qgAntipodeLin_one, qg_neg_mul, one_mul,
    show qgE k A i * qgKinv k A i * qgK k A i = qgE k A i * (qgKinv k A i * qgK k A i) from
      mul_assoc _ _ _, qg_Kinv_mul_K, mul_one]
  exact neg_add_cancel (G := QuantumGroup k A) _

private theorem qg_convR_F (i : Fin r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.rTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym) (qgF k A i))) = 0 := by
  rw [qgComul_F]
  simp only [LinearMap.rTensor_tmul, map_add, LinearMap.mul'_apply]
  rw [qgAntipodeLin_F, qgAntipodeLin_Kinv, qg_neg_mul,
    show qgK k A i * qgF k A i * 1 = qgK k A i * qgF k A i from mul_one _,
    show qgK k A i * qgF k A i = (qgK k A i * qgF k A i) from rfl]
  exact neg_add_cancel (G := QuantumGroup k A) _

private theorem qg_convR_K (i : Fin r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.rTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym) (qgK k A i))) = 1 := by
  rw [qgComul_K]
  simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, qgAntipodeLin_K]
  exact qg_Kinv_mul_K (A := A) k i

private theorem qg_convR_Kinv (i : Fin r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.rTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym) (qgKinv k A i))) = 1 := by
  rw [qgComul_Kinv]
  simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, qgAntipodeLin_Kinv]
  exact qg_K_mul_Kinv (A := A) k i

/-! ## 8. Left convolution on generators -/

private theorem qg_convL_E (i : Fin r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym) (qgE k A i))) = 0 := by
  rw [qgComul_E]
  simp only [LinearMap.lTensor_tmul, map_add, LinearMap.mul'_apply]
  rw [qgAntipodeLin_K, qgAntipodeLin_E, one_mul]
  exact add_neg_cancel (G := QuantumGroup k A) _

private theorem qg_convL_F (i : Fin r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym) (qgF k A i))) = 0 := by
  rw [qgComul_F]
  simp only [LinearMap.lTensor_tmul, map_add, LinearMap.mul'_apply]
  rw [qgAntipodeLin_one, qgAntipodeLin_F, mul_one, qg_mul_neg,
    show qgKinv k A i * (qgK k A i * qgF k A i) = (qgKinv k A i * qgK k A i) * qgF k A i from
      by rw [mul_assoc], qg_Kinv_mul_K, one_mul]
  exact add_neg_cancel (G := QuantumGroup k A) _

private theorem qg_convL_K (i : Fin r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym) (qgK k A i))) = 1 := by
  rw [qgComul_K]
  simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply, qgAntipodeLin_K]
  exact qg_K_mul_Kinv (A := A) k i

private theorem qg_convL_Kinv (i : Fin r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym) (qgKinv k A i))) = 1 := by
  rw [qgComul_Kinv]
  simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply, qgAntipodeLin_Kinv]
  exact qg_Kinv_mul_K (A := A) k i

/-! ## 9. Antipode anti-multiplicativity -/

theorem qgAntipodeLin_mul (a b : QuantumGroup k A) :
    qgAntipodeLin k hdiag hsym (a * b) =
    qgAntipodeLin k hdiag hsym b * qgAntipodeLin k hdiag hsym a := by
  unfold qgAntipodeLin
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap,
    map_mul]
  rfl

/-! ## 10. Convolution multiplicativity step -/

/-- If `mul'(rTensor(S)(u)) = algebraMap(r)`, then
    `mul'(rTensor(S)(u * v)) = algebraMap(r) * mul'(rTensor(S)(v))`.
    Core step for the FreeAlgebra.induction mul case. -/
private theorem qg_convR_mul_step
    (u v : TensorProduct (QBase k) (QuantumGroup k A) (QuantumGroup k A))
    (r : QBase k)
    (hu : (LinearMap.mul' (QBase k) (QuantumGroup k A))
            ((LinearMap.rTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym)) u) =
          algebraMap (QBase k) (QuantumGroup k A) r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.rTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym)) (u * v)) =
    algebraMap (QBase k) (QuantumGroup k A) r *
      (LinearMap.mul' (QBase k) (QuantumGroup k A))
        ((LinearMap.rTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym)) v) := by
  revert hu
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul c d =>
    intro hu
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset u
    simp only [Finset.sum_mul, map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
      Algebra.TensorProduct.tmul_mul_tmul, qgAntipodeLin_mul] at hu ⊢
    -- hu : ∑ S(aᵢ) * bᵢ = algebraMap r
    -- Goal: ∑ S(c) * S(aᵢ) * (bᵢ * d) = algebraMap(r) * (S(c) * d)
    -- Step 1: reassociate each term
    simp_rw [show ∀ p : QuantumGroup k A × QuantumGroup k A,
        (qgAntipodeLin k hdiag hsym) c * (qgAntipodeLin k hdiag hsym) p.1 * (p.2 * d) =
        ((qgAntipodeLin k hdiag hsym) c * ((qgAntipodeLin k hdiag hsym) p.1 * p.2)) * d from
        fun p => by noncomm_ring]
    -- Step 2: factor out d on the right
    rw [← Finset.sum_mul]
    -- Step 3: factor out S(c) on the left
    rw [← Finset.mul_sum]
    -- Step 4: substitute hu
    rw [hu]
    -- Step 5: commute algebraMap(r) past S(c) and reassociate
    rw [← mul_assoc, Algebra.commutes, mul_assoc]
  | add v₁ v₂ hv₁ hv₂ =>
    intro hu; simp only [mul_add, map_add, mul_add]
    rw [hv₁ hu, hv₂ hu]

/-- Left convolution multiplicativity: factors on y (right argument). -/
private theorem qg_convL_mul_step
    (u v : TensorProduct (QBase k) (QuantumGroup k A) (QuantumGroup k A))
    (r : QBase k)
    (hv : (LinearMap.mul' (QBase k) (QuantumGroup k A))
            ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym)) v) =
          algebraMap (QBase k) (QuantumGroup k A) r) :
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym)) (u * v)) =
    (LinearMap.mul' (QBase k) (QuantumGroup k A))
      ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym)) u) *
    algebraMap (QBase k) (QuantumGroup k A) r := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    -- Key helper: mul'(lTensor(S)((a ⊗ₜ b) * z)) = a * mul'(lTensor(S)(z)) * S(b)
    have h_eval : ∀ z : TensorProduct (QBase k) (QuantumGroup k A) (QuantumGroup k A),
        (LinearMap.mul' (QBase k) (QuantumGroup k A))
          ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym))
            ((a ⊗ₜ b) * z)) =
        a * (LinearMap.mul' (QBase k) (QuantumGroup k A))
              ((LinearMap.lTensor (QuantumGroup k A) (qgAntipodeLin k hdiag hsym)) z) *
        qgAntipodeLin k hdiag hsym b := by
      intro z; induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul,
          LinearMap.mul'_apply, qgAntipodeLin_mul]
        noncomm_ring
      | add z₁ z₂ hz₁ hz₂ => simp [mul_add, add_mul, map_add, hz₁, hz₂]
    rw [h_eval, hv]
    simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply]
    rw [mul_assoc, Algebra.commutes, ← mul_assoc]
  | add u₁ u₂ hu₁ hu₂ =>
    simp only [add_mul, map_add, add_mul]
    rw [hu₁, hu₂]

/-! ## 12. Main convolution theorems -/

/-- **Right antipode convolution law**: ∇ ∘ rTensor(S) ∘ Δ = unit ∘ ε.
    This is the identity m ∘ (id ⊗ S) ∘ Δ = η ∘ ε (using Mathlib's rTensor convention). -/
theorem qg_antipode_rTensor :
    letI := qgBialgebra k hdiag hsym
    LinearMap.mul' (QBase k) (QuantumGroup k A) ∘ₗ
      (qgAntipodeLin k hdiag hsym).rTensor (QuantumGroup k A) ∘ₗ
      Coalgebra.comul =
    (Algebra.linearMap (QBase k) (QuantumGroup k A)) ∘ₗ Coalgebra.counit := by
  letI := qgBialgebra k hdiag hsym
  ext x
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective (QBase k) (QGRel k A) x
  induction x using FreeAlgebra.induction with
  | grade0 r => -- scalar: S(algebraMap r) = algebraMap r
    simp only [LinearMap.comp_apply, AlgHom.commutes (RingQuot.mkAlgHom (QBase k) (QGRel k A))]
    change (LinearMap.mul' (QBase k) _)
      ((LinearMap.rTensor _ (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym).toLinearMap (algebraMap _ _ r)))
      = (Algebra.linearMap (QBase k) _) ((qgCounit k A).toLinearMap (algebraMap _ _ r))
    simp only [AlgHom.toLinearMap_apply, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, LinearMap.rTensor_tmul,
      LinearMap.mul'_apply, mul_one, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one, map_smul, qgAntipodeLin_one]
    congr 1
    · rw [map_one, Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul,
        qgAntipodeLin_one, LinearMap.mul'_apply, mul_one, map_one, one_smul]
  | grade1 x => -- generator
    rcases x with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
      simp only [LinearMap.comp_apply]
    · change (LinearMap.mul' (QBase k) _)
        ((LinearMap.rTensor _ (qgAntipodeLin k hdiag hsym)) ((qgComul k hdiag hsym) (qgE k A i)))
        = (Algebra.linearMap (QBase k) _) ((qgCounit k A) (qgE k A i))
      rw [qg_convR_E, qgCounit_E, map_zero]
    · change (LinearMap.mul' (QBase k) _)
        ((LinearMap.rTensor _ (qgAntipodeLin k hdiag hsym)) ((qgComul k hdiag hsym) (qgF k A i)))
        = (Algebra.linearMap (QBase k) _) ((qgCounit k A) (qgF k A i))
      rw [qg_convR_F, qgCounit_F, map_zero]
    · change (LinearMap.mul' (QBase k) _)
        ((LinearMap.rTensor _ (qgAntipodeLin k hdiag hsym)) ((qgComul k hdiag hsym) (qgK k A i)))
        = (Algebra.linearMap (QBase k) _) ((qgCounit k A) (qgK k A i))
      rw [qg_convR_K, qgCounit_K]; simp [Algebra.linearMap_apply]
    · change (LinearMap.mul' (QBase k) _)
        ((LinearMap.rTensor _ (qgAntipodeLin k hdiag hsym)) ((qgComul k hdiag hsym) (qgKinv k A i)))
        = (Algebra.linearMap (QBase k) _) ((qgCounit k A) (qgKinv k A i))
      rw [qg_convR_Kinv, qgCounit_Kinv]; simp [Algebra.linearMap_apply]
  | mul x y hx hy => -- multiplicativity: use qg_convR_mul_step + IH
    simp only [map_mul, LinearMap.comp_apply] at hx hy ⊢
    -- Step 1: comul(a*b) = comul(a) * comul(b)
    have hcm := map_mul (qgComul k hdiag hsym)
      ((RingQuot.mkAlgHom (QBase k) (QGRel k A)) x)
      ((RingQuot.mkAlgHom (QBase k) (QGRel k A)) y)
    rw [show CoalgebraStruct.comul _ = (qgComul k hdiag hsym) _ from rfl, hcm]
    erw [qg_convR_mul_step k hdiag hsym _ _ _ hx, hy]
    -- Step 2: ε(a*b) = ε(a) * ε(b) and η is ring hom
    have hcou := map_mul (qgCounit k A)
      ((RingQuot.mkAlgHom (QBase k) (QGRel k A)) x)
      ((RingQuot.mkAlgHom (QBase k) (QGRel k A)) y)
    simp only [Algebra.linearMap_apply,
      show ∀ z, CoalgebraStruct.counit (R := QBase k) z = (qgCounit k A) z from fun _ => rfl]
    rw [hcou, map_mul]
  | add x y hx hy => -- linearity
    simp only [map_add, LinearMap.comp_apply] at hx hy ⊢
    rw [hx, hy]

/-- **Left antipode convolution law**: ∇ ∘ lTensor(S) ∘ Δ = unit ∘ ε. -/
theorem qg_antipode_lTensor :
    letI := qgBialgebra k hdiag hsym
    LinearMap.mul' (QBase k) (QuantumGroup k A) ∘ₗ
      (qgAntipodeLin k hdiag hsym).lTensor (QuantumGroup k A) ∘ₗ
      Coalgebra.comul =
    (Algebra.linearMap (QBase k) (QuantumGroup k A)) ∘ₗ Coalgebra.counit := by
  letI := qgBialgebra k hdiag hsym
  ext x
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective (QBase k) (QGRel k A) x
  induction x using FreeAlgebra.induction with
  | grade0 r => -- scalar
    simp only [LinearMap.comp_apply, AlgHom.commutes (RingQuot.mkAlgHom (QBase k) (QGRel k A))]
    change (LinearMap.mul' (QBase k) _)
      ((LinearMap.lTensor _ (qgAntipodeLin k hdiag hsym))
        ((qgComul k hdiag hsym).toLinearMap (algebraMap _ _ r)))
      = (Algebra.linearMap (QBase k) _) ((qgCounit k A).toLinearMap (algebraMap _ _ r))
    simp only [AlgHom.toLinearMap_apply, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul,
      LinearMap.mul'_apply, mul_one, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one, map_smul, qgAntipodeLin_one]
    congr 1
    · rw [map_one, Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul,
        qgAntipodeLin_one, LinearMap.mul'_apply, mul_one, map_one, one_smul]
  | grade1 x => -- generator
    rcases x with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
      simp only [LinearMap.comp_apply]
    · change (LinearMap.mul' (QBase k) _)
        ((LinearMap.lTensor _ (qgAntipodeLin k hdiag hsym)) ((qgComul k hdiag hsym) (qgE k A i)))
        = (Algebra.linearMap (QBase k) _) ((qgCounit k A) (qgE k A i))
      rw [qg_convL_E, qgCounit_E, map_zero]
    · change (LinearMap.mul' (QBase k) _)
        ((LinearMap.lTensor _ (qgAntipodeLin k hdiag hsym)) ((qgComul k hdiag hsym) (qgF k A i)))
        = (Algebra.linearMap (QBase k) _) ((qgCounit k A) (qgF k A i))
      rw [qg_convL_F, qgCounit_F, map_zero]
    · change (LinearMap.mul' (QBase k) _)
        ((LinearMap.lTensor _ (qgAntipodeLin k hdiag hsym)) ((qgComul k hdiag hsym) (qgK k A i)))
        = (Algebra.linearMap (QBase k) _) ((qgCounit k A) (qgK k A i))
      rw [qg_convL_K, qgCounit_K]; simp [Algebra.linearMap_apply]
    · change (LinearMap.mul' (QBase k) _)
        ((LinearMap.lTensor _ (qgAntipodeLin k hdiag hsym)) ((qgComul k hdiag hsym) (qgKinv k A i)))
        = (Algebra.linearMap (QBase k) _) ((qgCounit k A) (qgKinv k A i))
      rw [qg_convL_Kinv, qgCounit_Kinv]; simp [Algebra.linearMap_apply]
  | mul x y hx hy => -- multiplicativity: use qg_convL_mul_step + IH
    simp only [map_mul, LinearMap.comp_apply] at hx hy ⊢
    have hcm := map_mul (qgComul k hdiag hsym)
      ((RingQuot.mkAlgHom (QBase k) (QGRel k A)) x)
      ((RingQuot.mkAlgHom (QBase k) (QGRel k A)) y)
    rw [show CoalgebraStruct.comul _ = (qgComul k hdiag hsym) _ from rfl, hcm]
    erw [qg_convL_mul_step k hdiag hsym _ _ _ hy, hx]
    have hcou := map_mul (qgCounit k A)
      ((RingQuot.mkAlgHom (QBase k) (QGRel k A)) x)
      ((RingQuot.mkAlgHom (QBase k) (QGRel k A)) y)
    simp only [Algebra.linearMap_apply,
      show ∀ z, CoalgebraStruct.counit (R := QBase k) z = (qgCounit k A) z from fun _ => rfl]
    rw [hcou, map_mul]
  | add x y hx hy => -- linearity
    simp only [map_add, LinearMap.comp_apply] at hx hy ⊢
    rw [hx, hy]

/-! ## 13. HopfAlgebra instance -/

/-- **HopfAlgebra instance for U_q(𝔤).** -/
noncomputable def qgHopfAlgebra :
    letI := qgBialgebra k hdiag hsym
    HopfAlgebra (QBase k) (QuantumGroup k A) := by
  letI := qgBialgebra k hdiag hsym
  exact { antipode := qgAntipodeLin k hdiag hsym
          mul_antipode_rTensor_comul := qg_antipode_rTensor k hdiag hsym
          mul_antipode_lTensor_comul := qg_antipode_lTensor k hdiag hsym }

/-! ## 12. Module summary -/

/-- QuantumGroupHopf module: Hopf algebra structure on U_q(𝔤).
  - counitOnGen + counit_respects_rel + qgCounit: ε fully proved
  - qg_comul_coassoc: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ
  - qg_comul_rTensor_counit + qg_comul_lTensor_counit: counit laws
  - qgBialgebra: Bialgebra instance via Bialgebra.ofAlgHom (0 sorry)
  - qgAntipodeLin: antipode as linear map + E/F/K/Kinv/one evaluation
  - qgAntipodeLin_mul: anti-multiplicativity S(ab)=S(b)S(a)
  - All 8 generator convolution lemmas: qg_convR/L_E/F/K/Kinv (0 sorry)
  - qg_convR/L_mul_step: convolution multiplicativity steps (0 sorry)
  - qg_antipode_rTensor + qg_antipode_lTensor: main convolution laws (0 sorry)
  - qgHopfAlgebra: HopfAlgebra instance (0 sorry)
  - First generic quantum group HopfAlgebra in any proof assistant
  - ZERO sorry. Covers all symmetric Cartan matrices simultaneously. -/
theorem quantum_group_hopf_summary : True := trivial

end SKEFTHawking
