import SKEFTHawking.ADW.QuaternionSU2HaarAnchored

/-!
# Finite polynomial transfer under the original link Haar measure

An anchored quaternion monomial contributes its joint chiral moment.
The contraction retains all other labels and adds terms that become equal
after removing the quaternion powers.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace SKEFTHawking.ADW.QuaternionSU2Sphere

open FiniteGrassmannCoframe FiniteGrassmannDiracBerezin
open FiniteDiracQuaternionSpecialization (QuaternionVariables Symbolic specialize)

private theorem continuous_anchoredCoordinate {L : Torus} (v : QuaternionVariables L) :
    Continuous (fun U : Links L ↦ anchoredCoordinate U v) := by
  obtain ⟨x, μ, side, i⟩ := v
  have h : Continuous (fun U : Links L ↦ U x μ) :=
    (continuous_apply μ).comp (continuous_apply x)
  cases side
  · have hm : Continuous (fun U : Links L ↦ (U x μ).1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp h)
    fin_cases i <;>
      first
      | exact Complex.continuous_re.comp ((continuous_apply _).comp
          ((continuous_apply _).comp hm))
      | exact Complex.continuous_im.comp ((continuous_apply _).comp
          ((continuous_apply _).comp hm))
  · have hm : Continuous (fun U : Links L ↦ (U x μ).2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp h)
    fin_cases i <;>
      first
      | exact Complex.continuous_re.comp ((continuous_apply _).comp
          ((continuous_apply _).comp hm))
      | exact Complex.continuous_im.comp ((continuous_apply _).comp
          ((continuous_apply _).comp hm))

/-- The complex weight of a monomial in the quaternion variables. -/
noncomputable def anchoredMoment (L : Torus) (p : QuaternionVariables L → ℕ) : ℂ :=
  ∏ x, ∏ μ, ∏ side, (chiralMoment (fun i ↦ p (x, μ, side, i)) : ℂ)

private theorem integral_quaternionPowers (L : Torus) (p : QuaternionVariables L →₀ ℕ) :
    (∫ U : Links L, p.prod (fun v n ↦ (anchoredCoordinate U v : ℂ) ^ n)
      ∂linkHaar L) = anchoredMoment L p := by
  classical
  simp_rw [Finsupp.prod_pow]
  exact linkHaar_monomial_complex L p

private theorem continuous_quaternionPowers (L : Torus) (p : QuaternionVariables L →₀ ℕ) :
    Continuous (fun U : Links L ↦ p.prod (fun v n ↦ (anchoredCoordinate U v : ℂ) ^ n)) := by
  classical
  apply continuous_finsetProd
  intro v _
  exact (Complex.continuous_ofReal.comp (continuous_anchoredCoordinate v)).pow _


private noncomputable def contractTerm {L : Torus} {ρ : Type*}
    (e : ρ ⊕ QuaternionVariables L →₀ ℕ) (c : ℂ) : MvPolynomial ρ ℂ :=
  let d := Finsupp.sumFinsuppEquivProdFinsupp e
  MvPolynomial.monomial d.1 (c * anchoredMoment L d.2)

/-- Integrate quaternion factors while retaining every residual variable label. -/
noncomputable def contract (L : Torus) (ρ : Type*) :
    MvPolynomial (ρ ⊕ QuaternionVariables L) ℂ →ₗ[ℂ] MvPolynomial ρ ℂ where
  toFun P := (AddMonoidAlgebra.coeff P).sum contractTerm
  map_add' P Q := by
    classical
    change (AddMonoidAlgebra.coeff P + AddMonoidAlgebra.coeff Q).sum contractTerm =
      (AddMonoidAlgebra.coeff P).sum contractTerm + (AddMonoidAlgebra.coeff Q).sum contractTerm
    apply Finsupp.sum_add_index
    · intro e _
      simp [contractTerm]
    · intro e _ a b
      simp [contractTerm, add_mul]
  map_smul' c P := by
    change (c • AddMonoidAlgebra.coeff P).sum contractTerm =
      c • (AddMonoidAlgebra.coeff P).sum contractTerm
    rw [Finsupp.sum_smul_index (fun e ↦ by simp [contractTerm])]
    rw [Finsupp.sum, Finsupp.sum, Finset.smul_sum]
    simp only [contractTerm, MvPolynomial.smul_monomial, smul_eq_mul, mul_assoc]

/-- Closed contraction of one monomial, with its residual and quaternion powers separated. -/
theorem contract_monomial {L : Torus} {ρ : Type*} (d : ρ →₀ ℕ)
    (p : QuaternionVariables L →₀ ℕ) (c : ℂ) :
    contract L ρ (MvPolynomial.monomial (d.sumElim p) c) =
      MvPolynomial.monomial d (c * anchoredMoment L p) := by
  change (AddMonoidAlgebra.coeff (MvPolynomial.monomial (d.sumElim p) c)).sum contractTerm = _
  rw [MvPolynomial.sum_monomial_eq (by simp [contractTerm])]
  have hs : Finsupp.sumFinsuppEquivProdFinsupp (d.sumElim p) = (d, p) :=
    Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply (d, p)
  simp [contractTerm, hs]

/-- Every retained coefficient is the sum of all source terms with its residual exponent. -/
theorem coeff_contract {L : Torus} {ρ : Type*} [DecidableEq ρ]
    (P : MvPolynomial (ρ ⊕ QuaternionVariables L) ℂ) (d : ρ →₀ ℕ) :
    (contract L ρ P).coeff d =
      ∑ e ∈ P.support,
        if (Finsupp.sumFinsuppEquivProdFinsupp e).1 = d then
          P.coeff e * anchoredMoment L (Finsupp.sumFinsuppEquivProdFinsupp e).2
        else 0 := by
  classical
  change ((AddMonoidAlgebra.coeff P).sum contractTerm).coeff d = _
  rw [MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  simp only [contractTerm, MvPolynomial.coeff_monomial]

private theorem eval_monomial_sumElim {L : Torus} {ρ : Type*} (U : Links L)
    (z : ρ → ℂ) (d : ρ →₀ ℕ) (p : QuaternionVariables L →₀ ℕ) (c : ℂ) :
    MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ)))
        (MvPolynomial.monomial (d.sumElim p) c) =
      (c * d.prod (fun i n ↦ z i ^ n)) *
        p.prod (fun v n ↦ (anchoredCoordinate U v : ℂ) ^ n) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_sumElim, mul_assoc]
  rfl

private theorem continuous_eval_monomial {L : Torus} {ρ : Type*}
    (z : ρ → ℂ) (e : ρ ⊕ QuaternionVariables L →₀ ℕ) (c : ℂ) :
    Continuous (fun U : Links L ↦
      MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ)))
        (MvPolynomial.monomial e c)) := by
  obtain ⟨⟨d, p⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective e
  simp_rw [show Finsupp.sumFinsuppEquivProdFinsupp.symm (d, p) = d.sumElim p from rfl,
    eval_monomial_sumElim]
  exact continuous_const.mul (continuous_quaternionPowers L p)

private theorem integral_eval_monomial {L : Torus} {ρ : Type*}
    (z : ρ → ℂ) (e : ρ ⊕ QuaternionVariables L →₀ ℕ) (c : ℂ) :
    (∫ U : Links L, MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ)))
      (MvPolynomial.monomial e c) ∂linkHaar L) =
      MvPolynomial.eval z (contract L ρ (MvPolynomial.monomial e c)) := by
  obtain ⟨⟨d, p⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective e
  simp_rw [show Finsupp.sumFinsuppEquivProdFinsupp.symm (d, p) = d.sumElim p from rfl,
    eval_monomial_sumElim]
  rw [integral_const_mul, integral_quaternionPowers, contract_monomial, MvPolynomial.eval_monomial]
  ring

/-- Finite contraction agrees with evaluation and integration against the original Haar law. -/
theorem integral_eval_eq_contract {L : Torus} {ρ : Type*}
    (P : MvPolynomial (ρ ⊕ QuaternionVariables L) ℂ) (z : ρ → ℂ) :
    (∫ U : Links L, MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ))) P
      ∂linkHaar L) = MvPolynomial.eval z (contract L ρ P) := by
  classical
  have hexpand :
      (∫ U : Links L, MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ))) P
        ∂linkHaar L) =
      ∫ U : Links L, ∑ e ∈ P.support,
        MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ)))
          (MvPolynomial.monomial e (P.coeff e)) ∂linkHaar L := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun U ↦ ?_)
    dsimp only
    nth_rw 1 [P.as_sum]
    rw [MvPolynomial.eval_sum]
  rw [hexpand, integral_finsetSum P.support]
  · simp_rw [integral_eval_monomial]
    rw [← MvPolynomial.eval_sum, ← map_sum, ← P.as_sum]
  · intro e _
    let f (U : Links L) :=
      MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ)))
        (MvPolynomial.monomial e (P.coeff e))
    exact link_coefficient_integrable L ⟨f, continuous_eval_monomial z e (P.coeff e)⟩

/-- Shared link variables are multiplied before applying the Haar contraction. -/
theorem integral_eval_mul_eq_contract {L : Torus} {ρ : Type*}
    (P Q : MvPolynomial (ρ ⊕ QuaternionVariables L) ℂ) (z : ρ → ℂ) :
    (∫ U : Links L, MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ))) P *
      MvPolynomial.eval (Sum.elim z (fun v ↦ (anchoredCoordinate U v : ℂ))) Q
      ∂linkHaar L) = MvPolynomial.eval z (contract L ρ (P * Q)) := by
  simpa only [map_mul] using integral_eval_eq_contract (P * Q) z


/-- Reassociate the existing h/J/quaternion variables and contract only the quaternion arm. -/
noncomputable def contractSymbolic (L : Torus) :
    Symbolic L →ₗ[ℂ] MvPolynomial (Auxiliary L ⊕ Auxiliary L) ℂ :=
  (contract L (Auxiliary L ⊕ Auxiliary L)).comp
    (MvPolynomial.rename (Equiv.sumAssoc (Auxiliary L) (Auxiliary L)
      (QuaternionVariables L)).symm).toLinearMap

private theorem eval_specialize (L : Torus) (P : Symbolic L) (h : Auxiliary L → ℝ)
    (J : Auxiliary L → ℂ) (U : Links L) :
    MvPolynomial.eval (fun a ↦ (h a : ℂ)) (specialize L J (anchoredCoordinate U) P) =
      MvPolynomial.eval (Sum.elim (fun a ↦ (h a : ℂ))
        (Sum.elim J (fun v ↦ (anchoredCoordinate U v : ℂ)))) P := by
  have he :
      (MvPolynomial.eval (fun a ↦ (h a : ℂ))).comp (specialize L J (anchoredCoordinate U)) =
        MvPolynomial.eval (Sum.elim (fun a ↦ (h a : ℂ))
          (Sum.elim J (fun v ↦ (anchoredCoordinate U v : ℂ)))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [specialize]
    · intro a
      rcases a with a | a | v <;> simp [specialize]
  exact RingHom.congr_fun he P

/-- The original specialization at arbitrary h and complex J uses the same contraction. -/
theorem integral_specialize_eq_contractSymbolic (L : Torus) (P : Symbolic L)
    (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) :
    (∫ U : Links L, MvPolynomial.eval (fun a ↦ (h a : ℂ))
      (specialize L J (anchoredCoordinate U) P) ∂linkHaar L) =
      MvPolynomial.eval (Sum.elim (fun a ↦ (h a : ℂ)) J) (contractSymbolic L P) := by
  simp only [contractSymbolic, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [← integral_eval_eq_contract]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U ↦ ?_)
  dsimp only
  rw [MvPolynomial.eval_rename, eval_specialize]
  apply congrArg (fun z ↦ MvPolynomial.eval z P)
  funext a
  rcases a with a | a | v <;> rfl

private theorem anchoredMoment_single_left (L : Torus) (x : Site L) (μ : Fin 4) (n : ℕ) :
    anchoredMoment L (Finsupp.single (x, μ, false, 0) n) =
      (chiralMoment (fun i ↦ if i = 0 then n else 0) : ℂ) := by
  classical
  rw [← integral_quaternionPowers]
  have he (U : Links L) :
      (Finsupp.single (x, μ, false, 0) n).prod
          (fun v k ↦ (anchoredCoordinate U v : ℂ) ^ k) =
        ((anchoredCoordinate U (x, μ, false, 0) ^ n : ℝ) : ℂ) := by
    rw [Finsupp.prod_single_index]
    · exact (Complex.ofReal_pow _ _).symm
    · exact pow_zero _
  simp_rw [he, integral_complex_ofReal]
  have hm := linkHaar_at_anchor L x μ (fun side i ↦ if side = false ∧ i = 0 then n else 0)
  have hr : (∫ U : Links L, anchoredCoordinate U (x, μ, false, 0) ^ n ∂linkHaar L) =
      chiralMoment (fun i ↦ if i = 0 then n else 0) := by
    simpa [Fintype.prod_bool, Fin.prod_univ_four,
      show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide] using hm
  rw [hr]

private theorem anchoredMoment_left_two (L : Torus) (x : Site L) (μ : Fin 4) :
    anchoredMoment L (Finsupp.single (x, μ, false, 0) 2) = 1 / 4 := by
  rw [anchoredMoment_single_left]
  norm_num [chiralMoment, Fin.forall_fin_succ, Nat.even_iff, Fin.sum_univ_four,
    Fin.prod_univ_four, Finset.prod_range_succ,
    show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]

private theorem anchoredMoment_left_four (L : Torus) (x : Site L) (μ : Fin 4) :
    anchoredMoment L (Finsupp.single (x, μ, false, 0) 4) = 1 / 8 := by
  rw [anchoredMoment_single_left]
  norm_num [chiralMoment, Fin.forall_fin_succ, Nat.even_iff, Fin.sum_univ_four,
    Fin.prod_univ_four, Finset.prod_range_succ,
    show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]

/-- Terms with different quaternion degrees can cancel at the same residual exponent. -/
theorem contract_residual_collision_cancel (L : Torus) {ρ : Type*} (d : ρ →₀ ℕ)
    (x : Site L) (μ : Fin 4) :
    contract L ρ
      (MvPolynomial.monomial (d.sumElim (Finsupp.single (x, μ, false, 0) 2)) 4 +
       MvPolynomial.monomial (d.sumElim (Finsupp.single (x, μ, false, 0) 4)) (-8)) = 0 := by
  rw [map_add, contract_monomial, contract_monomial,
    anchoredMoment_left_two, anchoredMoment_left_four, ← map_add]
  norm_num

/-- Integrating a product of identical anchored first powers retains their shared square. -/
theorem contract_shared_left_square (L : Torus) (ρ : Type*) (x : Site L) (μ : Fin 4) :
    contract L ρ ((MvPolynomial.X (Sum.inr (x, μ, false, 0))) ^ 2) =
      MvPolynomial.C (1 / 4) := by
  rw [MvPolynomial.X_pow_eq_monomial, ← Finsupp.sumElim_zero_single,
    contract_monomial, anchoredMoment_left_two]
  simp

/-- A single anchored first power integrates to zero. -/
theorem contract_left_first (L : Torus) (ρ : Type*) (x : Site L) (μ : Fin 4) :
    contract L ρ (MvPolynomial.X (Sum.inr (x, μ, false, 0))) = 0 := by
  change contract L ρ
    (MvPolynomial.monomial (Finsupp.single (Sum.inr (x, μ, false, 0)) 1) 1) = 0
  rw [← Finsupp.sumElim_zero_single, contract_monomial, anchoredMoment_single_left]
  norm_num [chiralMoment, Fin.forall_fin_succ, Nat.even_iff]

end SKEFTHawking.ADW.QuaternionSU2Sphere
