import SKEFTHawking.ADW.QuaternionSU2SymbolicSource
import SKEFTHawking.ADW.FiniteGrassmannSourceInsertion

/-!
# Joint symbolic Haar contraction for the original compensated site weights
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal

namespace SKEFTHawking.ADW.QuaternionSU2Sphere

open FiniteGrassmannCoframe FiniteGrassmannDiracBerezin FiniteDiracQuaternionSpecialization
open FiniteGrassmannSourceAuxiliary GaussianGrassmannAuxiliary FiniteGrassmannEvaluation
open FiniteDiracExecutableAssembly

/-- Embed a quaternion polynomial into the link-coordinate arm of the h/J/q ring. -/
def embedQuaternion (L : Torus) : QuaternionCoefficients L →+* Symbolic L :=
  (MvPolynomial.rename fun v : QuaternionVariables L ↦ Sum.inr (Sum.inr v)).toRingHom

/-- Specialize source and link coordinates, then evaluate the auxiliary coordinates. -/
def evalSymbolic (L : Torus) (U : Links L) (h : Auxiliary L → ℝ)
    (J : Auxiliary L → ℂ) : Symbolic L →+* ℂ :=
  (MvPolynomial.eval fun a ↦ (h a : ℂ)).comp (specialize L J (anchoredCoordinate U))

@[simp] theorem evalSymbolic_C (L : Torus) (U : Links L) (h : Auxiliary L → ℝ)
    (J : Auxiliary L → ℂ) (c : ℂ) :
    evalSymbolic L U h J (MvPolynomial.C c) = c := by
  simp [evalSymbolic, specialize]

@[simp] theorem evalSymbolic_X_auxiliary (L : Torus) (U : Links L) (h : Auxiliary L → ℝ)
    (J : Auxiliary L → ℂ) (a : Auxiliary L) :
    evalSymbolic L U h J (MvPolynomial.X (.inl a)) = (h a : ℂ) := by
  simp [evalSymbolic, specialize]

@[simp] theorem evalSymbolic_embedQuaternion (L : Torus) (U : Links L)
    (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) (P : QuaternionCoefficients L) :
    evalSymbolic L U h J (embedQuaternion L P) = evaluateQuaternion U P := by
  have he : (evalSymbolic L U h J).comp (embedQuaternion L) = evaluateQuaternion U := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [embedQuaternion, evaluateQuaternion]
    · intro v
      simp [embedQuaternion, evaluateQuaternion, evalSymbolic, specialize]
  exact RingHom.congr_fun he P

/-- The exact finite Hermite factors in the auxiliary arm of the h/J/q ring. -/
def symbolicHermite (L : Torus) (σ : ℝ) (x : Site L) (α : D →₀ ℕ) : Symbolic L :=
  ∏ i : D, Polynomial.eval₂ (Int.castRingHom (Symbolic L))
    (MvPolynomial.C ((σ : ℂ)⁻¹) * MvPolynomial.X (.inl (x, i)))
    (Polynomial.hermite (α i))

theorem symbolicHermite_eval (L : Torus) (σ : ℝ) (x : Site L)
    (α : D →₀ ℕ) (U : Links L) (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) :
    evalSymbolic L U h J (symbolicHermite L σ x α) =
      (auxiliaryHermite σ α (fun i ↦ h (x,i)) : ℂ) := by
  rw [symbolicHermite, map_prod, auxiliaryHermite, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.ringHom_eval₂_intCastRingHom]
  simp only [map_mul, evalSymbolic_C, evalSymbolic_X_auxiliary]
  rw [show (σ : ℂ)⁻¹ * (h (x,i) : ℂ) = ((h (x,i) / σ : ℝ) : ℂ) by
    push_cast
    ring]
  exact integer_polynomial_complex_eval _ _

/-- Every retained compensated coefficient is multiplied by its actual scaled Hermite factor. -/
def symbolicSiteWeight (L : Torus) (σ : ℝ) (S : Site L → QuaternionSource L)
    (x : Site L) : Symbolic L :=
  ∑ α ∈ boundedIndices (4 * FiniteGrassmannCoframe.volume L),
    embedQuaternion L (quaternionCompensationCoeff (4 * FiniteGrassmannCoframe.volume L) σ (S x) α) *
      MvPolynomial.C (((σ ^ auxiliaryDegree α)⁻¹ : ℝ) : ℂ) *
      symbolicHermite L σ x α

theorem symbolicSiteWeight_eval (L : Torus) (σ : ℝ) (S : Site L → QuaternionSource L)
    (hS : ∀ x, (S x).constantCoeff = 0) (x : Site L) (U : Links L)
    (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) :
    evalSymbolic L U h J (symbolicSiteWeight L σ S x) =
      auxiliaryWeight σ
        (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ (MvPolynomial.map (evaluateQuaternion U) (S x)))
        (fun i ↦ h (x,i)) := by
  rw [auxiliaryWeight_bounded (4 * FiniteGrassmannCoframe.volume L) σ _ (compensationPolynomial_totalDegree _ _ _)]
  simp only [symbolicSiteWeight, map_sum, map_mul, evalSymbolic_C,
    evalSymbolic_embedQuaternion, quaternionCompensationCoeff_eval U _ _ _ (hS x),
    symbolicHermite_eval]

/-- The exact product over all original sites, with link variables shared across factors. -/
def symbolicFullWeight (L : Torus) (σ : ℝ) (S : Site L → QuaternionSource L) : Symbolic L :=
  ∏ x, symbolicSiteWeight L σ S x

theorem symbolicFullWeight_eval (L : Torus) (σ : ℝ) (S : Site L → QuaternionSource L)
    (hS : ∀ x, (S x).constantCoeff = 0) (U : Links L)
    (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) :
    evalSymbolic L U h J (symbolicFullWeight L σ S) =
      fullWeight L σ (fun x ↦ MvPolynomial.map (evaluateQuaternion U) (S x)) h := by
  simp only [symbolicFullWeight, map_prod, symbolicSiteWeight_eval L σ S hS, fullWeight]

theorem symbolicPrintedWeight_eval (L : Torus) (σ : ℝ) (g1 g2 : ℂ)
    (U : Links L) (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) :
    evalSymbolic L U h J (symbolicFullWeight L σ (fun x ↦ quaternionPrintedSource L x g1 g2)) =
      fullWeight L σ (fun x ↦ printedSource L U x g1 g2) h := by
  rw [symbolicFullWeight_eval L σ _ (fun x ↦ quaternionPrintedSource_constantCoeff L x g1 g2)]
  simp only [quaternionPrintedSource_eval]

theorem symbolicClosedWeight_eval (L : Torus) (σ : ℝ) (g1 g2 : ℂ)
    (U : Links L) (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) :
    evalSymbolic L U h J (symbolicFullWeight L σ (fun x ↦ quaternionClosedSource L x g1 g2)) =
      fullWeight L σ (fun x ↦ closedSource L U x g1 g2) h := by
  rw [symbolicFullWeight_eval L σ _ (fun x ↦ quaternionClosedSource_constantCoeff L x g1 g2)]
  simp only [quaternionClosedSource_eval]


/-- Pointwise agreement with the continuous-coefficient carrier used by Eq11. -/
theorem symbolicSiteWeight_eq_haarEvaluation (L : Torus) (σ : ℝ)
    (S : Site L → QuaternionSource L) (hS : ∀ x, (S x).constantCoeff = 0)
    (h0 : ∀ U : Links L, ∀ x, (MvPolynomial.map (evaluateQuaternion U) (S x)).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U : Links L ↦
      (MvPolynomial.map (evaluateQuaternion U) (S x)).coeff α))
    (x : Site L) (U : Links L) (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) :
    evalSymbolic L U h J (symbolicSiteWeight L σ S x) =
      haarPolynomialEvaluation L U h (siteWeightHaarPolynomial L σ
        (fun U x ↦ MvPolynomial.map (evaluateQuaternion U) (S x)) h0 hC x) := by
  rw [symbolicSiteWeight_eval L σ S hS, siteWeightHaarPolynomial_eval]

private theorem specialize_auxiliaryDerivative (L : Torus) (J : Auxiliary L → ℂ)
    (q : QuaternionVariables L → ℝ) (a : Auxiliary L) (P : Symbolic L) :
    specialize L J q (MvPolynomial.pderiv (.inl a) P) =
      MvPolynomial.pderiv a (specialize L J q P) := by
  let f : Auxiliary L ⊕ QuaternionVariables L → ℂ := Sum.elim J (fun v ↦ (q v : ℂ))
  have he (Q : Symbolic L) :
      specialize L J q Q =
        MvPolynomial.aeval (Sum.elim MvPolynomial.X (MvPolynomial.C ∘ f)) Q := by
    rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.algebraMap_eq]
    have hf : Sum.elim MvPolynomial.X (MvPolynomial.C ∘ f) =
        (Sum.elim MvPolynomial.X
          (Sum.elim (MvPolynomial.C ∘ J) (fun i ↦ MvPolynomial.C (q i : ℂ))) :
            FiniteDiracQuaternionSpecialization.Variables L → MvPolynomial (Auxiliary L) ℂ) := by
      funext x
      rcases x with x | x | x <;> rfl
    rw [hf]
    rfl
  rw [he, he]
  exact MvPolynomial.aeval_sumElim_pderiv_inl P f a

private theorem evalSymbolic_apply (L : Torus) (U : Links L) (h : Auxiliary L → ℝ)
    (J : Auxiliary L → ℂ) (P : Symbolic L) :
    evalSymbolic L U h J P =
      MvPolynomial.eval (fun a ↦ (h a : ℂ)) (specialize L J (anchoredCoordinate U) P) := rfl

private theorem integral_weightedSymbolic (L : Torus) (σ : ℝ)
    (S : Site L → QuaternionSource L) (hS : ∀ x, (S x).constantCoeff = 0)
    (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ) (P : Symbolic L) :
    (∫ U : Links L, fullWeight L σ (fun x ↦ MvPolynomial.map (evaluateQuaternion U) (S x)) h *
      evalSymbolic L U h J P ∂linkHaar L) =
        MvPolynomial.eval (Sum.elim (fun a ↦ (h a : ℂ)) J)
          (contractSymbolic L (symbolicFullWeight L σ S * P)) := by
  simpa only [← evalSymbolic_apply, map_mul, symbolicFullWeight_eval L σ S hS] using
    integral_specialize_eq_contractSymbolic L (symbolicFullWeight L σ S * P) h J

/-- The original shifted determinant is contracted jointly with all site weights. The source
word sees the original links, and only the determinant uses the supplied boundary twist. -/
theorem integral_weightedShiftedDet (L : Torus) (σ : ℝ) (S : Site L → QuaternionSource L)
    (hS : ∀ x, (S x).constantCoeff = 0) (anti : Fin 4 → Bool) (axis : Fin 4 ≃ Fin 4)
    (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ) :
    (∫ U : Links L, fullWeight L σ (fun x ↦ MvPolynomial.map (evaluateQuaternion U) (S x)) h *
      MvPolynomial.eval (fun a ↦ (h a : ℂ)) (transportedShiftedDet L anti axis J U) ∂linkHaar L) =
      MvPolynomial.eval (Sum.elim (fun a ↦ (h a : ℂ)) J)
        (contractSymbolic L (symbolicFullWeight L σ S * (symbolicAssembly L anti axis).det)) := by
  simpa only [evalSymbolic_apply, specialize_symbolicDet] using
    integral_weightedSymbolic L σ S hS J h (symbolicAssembly L anti axis).det

open FiniteDeterminantRawJet in
/-- Four joint contractions of the actual weighted raw determinant jet. Derivatives act on the
determinant before weighting, with both derivative positions kept even for coincident labels. -/
theorem integral_weightedShiftedAssembly_rawJet (L : Torus) (σ : ℝ)
    (S : Site L → QuaternionSource L) (hS : ∀ x, (S x).constantCoeff = 0)
    (anti : Fin 4 → Bool) (axis : Fin 4 ≃ Fin 4) (J : Auxiliary L → ℂ)
    (h : Auxiliary L → ℝ) (a b : Auxiliary L) :
    let z : Auxiliary L → ℂ := fun j ↦ (h j : ℂ)
    let jet (U : Links L) := determinantJet
      ((polynomialJet z a b).mapMatrix (shiftedAssembly L anti U axis J))
    let W (U : Links L) := fullWeight L σ (fun x ↦ MvPolynomial.map (evaluateQuaternion U) (S x)) h
    let evaluateJoint (P : Symbolic L) := MvPolynomial.eval (Sum.elim z J)
      (contractSymbolic L (symbolicFullWeight L σ S * P))
    let P := (symbolicAssembly L anti axis).det
    ofSlots (∫ U : Links L, W U * value (jet U) ∂linkHaar L)
      (∫ U : Links L, W U * firstOuter (jet U) ∂linkHaar L)
      (∫ U : Links L, W U * firstInner (jet U) ∂linkHaar L)
      (∫ U : Links L, W U * second (jet U) ∂linkHaar L) =
      ofSlots (evaluateJoint P) (evaluateJoint (MvPolynomial.pderiv (.inl a) P))
        (evaluateJoint (MvPolynomial.pderiv (.inl b) P))
        (evaluateJoint (MvPolynomial.pderiv (.inl b) (MvPolynomial.pderiv (.inl a) P))) := by
  dsimp only
  have hdet (U : Links L) :
      MvPolynomial.rename (sourceCoordinate L axis).symm
        (shiftedDiracDetAtLink L (twistedLinks L anti U) (J ∘ (sourceCoordinate L axis).symm)) =
      transportedShiftedDet L anti axis J U := rfl
  let P := (symbolicAssembly L anti axis).det
  have hv := integral_weightedSymbolic L σ S hS J h P
  have ha := integral_weightedSymbolic L σ S hS J h (MvPolynomial.pderiv (.inl a) P)
  have hb := integral_weightedSymbolic L σ S hS J h (MvPolynomial.pderiv (.inl b) P)
  have hab := integral_weightedSymbolic L σ S hS J h
    (MvPolynomial.pderiv (.inl b) (MvPolynomial.pderiv (.inl a) P))
  simp only [evalSymbolic_apply, specialize_auxiliaryDerivative, P, specialize_symbolicDet]
    at hv ha hb hab
  simp_rw [shiftedAssembly_rawJet, hdet, polynomialJet_eq_select, select]
  simp only [value, firstOuter, firstInner, second, ofSlots, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_mk, hv, ha, hb, hab]


/-- In the joint polynomial, the same anchored link in two factors contributes its second
moment, although each first moment vanishes. -/
theorem symbolicSharedLink_control (L : Torus) (x : Site L) (μ : Fin 4) :
    let q : Symbolic L := embedQuaternion L (MvPolynomial.X (x, μ, false, 0))
    contractSymbolic L q = 0 ∧ contractSymbolic L (q * q) = MvPolynomial.C (1 / 4) := by
  constructor
  · simpa [embedQuaternion, contractSymbolic] using
      contract_left_first L (Auxiliary L ⊕ Auxiliary L) x μ
  · simpa [embedQuaternion, contractSymbolic, pow_two] using
      contract_shared_left_square L (Auxiliary L ⊕ Auxiliary L) x μ


/-- The actual printed and closed plaquette coefficients share the same link assignment.
On the noncommuting control links their joint specialization multiplies (+i) and (-i). -/
theorem symbolicSharedPlaquette_control (h : Auxiliary controlTorus → ℝ)
    (J : Auxiliary controlTorus → ℂ) :
    ∃ U : Links controlTorus,
      evalSymbolic controlTorus U h J
        (embedQuaternion controlTorus (quaternionPlaquettePrinted controlTorus 0 0 1 0 1) *
          embedQuaternion controlTorus (quaternionPlaquetteClosed controlTorus 0 0 1 0 1)) = 1 := by
  obtain ⟨U, hp, hc⟩ := quaternionPlaquette_wordOrder_control
  change evaluateQuaternion U (quaternionPlaquettePrinted controlTorus 0 0 1 0 1) =
    Complex.I at hp
  change evaluateQuaternion U (quaternionPlaquetteClosed controlTorus 0 0 1 0 1) =
    -Complex.I at hc
  refine ⟨U, ?_⟩
  rw [map_mul, evalSymbolic_embedQuaternion, evalSymbolic_embedQuaternion, hp, hc,
    mul_neg, Complex.I_mul_I, neg_neg]

/-- Zero couplings agree for both word orientations at every link and every auxiliary value.
The original compensation and Hermite factors are retained. -/
theorem symbolicZeroCouplings_control (L : Torus) (σ : ℝ) (U : Links L)
    (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) :
    evalSymbolic L U h J (symbolicFullWeight L σ (fun x ↦ quaternionPrintedSource L x 0 0)) =
      fullWeight L σ (fun _ ↦ 0) h ∧
    evalSymbolic L U h J (symbolicFullWeight L σ (fun x ↦ quaternionClosedSource L x 0 0)) =
      fullWeight L σ (fun _ ↦ 0) h := by
  rw [symbolicPrintedWeight_eval, symbolicClosedWeight_eval]
  simp only [printedSource, closedSource, source_zero, and_self]

/-- The original periodic Eq11 determinant insertion in symbolic coordinates. -/
def symbolicEq11Insertion (L : Torus) (k : CoframeInsertion L) : Symbolic L :=
  let P := (symbolicAssembly L (fun _ ↦ false) (Equiv.refl _)).det
  match k with
  | .zero => P
  | .first a => MvPolynomial.pderiv (.inl a) P
  | .mixed a b => MvPolynomial.pderiv (.inl b) (MvPolynomial.pderiv (.inl a) P)

private theorem specialize_symbolicDet_periodic (L : Torus) (J : Auxiliary L → ℂ)
    (U : Links L) :
    specialize L J (anchoredCoordinate U)
        (symbolicAssembly L (fun _ ↦ false) (Equiv.refl _)).det =
      shiftedDiracDetAtLink L U J := by
  have he : sourceCoordinate L (Equiv.refl _) = Equiv.refl _ := by
    apply Equiv.ext
    rintro ⟨x, μ, γ⟩
    rfl
  have ht : twistedLinks L (fun _ ↦ false) U = U := by
    funext x μ
    simp [twistedLinks]
  rw [specialize_symbolicDet, transportedShiftedDet, he, ht]
  simp

/-- The symbolic insertion evaluates to the actual original ordered Berezin factor. -/
theorem symbolicEq11Insertion_eval (L : Torus) (U : Links L)
    (h : Auxiliary L → ℝ) (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    evalSymbolic L U h J (symbolicEq11Insertion L k) =
      berezin L (k.factor U * diracCoframeExp L U (fun i ↦ (h i : ℂ) + J i)) := by
  cases k with
  | zero =>
    rw [symbolicEq11Insertion, evalSymbolic_apply, specialize_symbolicDet_periodic,
      shiftedDiracDetAtLink_eval, CoframeInsertion.factor, one_mul, diracCoframeExp,
      berezin_nilExp_det]
  | first a =>
    simpa only [symbolicEq11Insertion, evalSymbolic_apply, specialize_auxiliaryDerivative,
      specialize_symbolicDet_periodic, CoframeInsertion.factor] using
        shiftedDiracDetAtLink_first L U J (fun i ↦ (h i : ℂ)) a
  | mixed a b =>
    simpa only [symbolicEq11Insertion, evalSymbolic_apply, specialize_auxiliaryDerivative,
      specialize_symbolicDet_periodic, CoframeInsertion.factor] using
        shiftedDiracDetAtLink_mixed L U J (fun i ↦ (h i : ℂ)) a b

/-- Original Eq11 via one joint symbolic Haar contraction, then the existing finite Gaussian
measure. This preserves the unnormalized Berezin insertion and every site weight. -/
theorem symbolicEq11Insertion_integral (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : Site L → QuaternionSource L)
    (hS : ∀ x, (S x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U : Links L ↦
      (MvPolynomial.map (evaluateQuaternion U) (S x)).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    (∫ U : Links L, sourceInsertionValue L U
      (fun x ↦ MvPolynomial.map (evaluateQuaternion U) (S x)) J k ∂linkHaar L) =
    ∫ h : Auxiliary L → ℝ, MvPolynomial.eval (Sum.elim (fun j ↦ (h j : ℂ)) J)
      (contractSymbolic L (symbolicFullWeight L σ S * symbolicEq11Insertion L k))
      ∂gaussianMeasure (Auxiliary L) v := by
  have h0 (U : Links L) (x : Site L) :
      (MvPolynomial.map (evaluateQuaternion U) (S x)).constantCoeff = 0 := by
    rw [MvPolynomial.constantCoeff_map, hS x, map_zero]
  refine ((sourceInsertion_iterated L σ hσ v hv
    (fun U x ↦ MvPolynomial.map (evaluateQuaternion U) (S x)) h0 hC J k).2).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
  simpa only [sourceInsertionDensity_eval, symbolicEq11Insertion_eval] using
    integral_weightedSymbolic L σ S hS J h (symbolicEq11Insertion L k)


/-- Joint Haar then Gaussian evaluation for the original printed word. -/
theorem symbolicPrintedEq11_integral (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ)
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    (∫ U : Links L, sourceInsertionValue L U (fun x ↦ printedSource L U x g1 g2) J k
      ∂linkHaar L) =
    ∫ h : Auxiliary L → ℝ, MvPolynomial.eval (Sum.elim (fun j ↦ (h j : ℂ)) J)
      (contractSymbolic L (symbolicFullWeight L σ (fun x ↦ quaternionPrintedSource L x g1 g2) *
        symbolicEq11Insertion L k)) ∂gaussianMeasure (Auxiliary L) v := by
  have hC (x : Site L) (α : D →₀ ℕ) :
      Continuous (fun U : Links L ↦
        (MvPolynomial.map (evaluateQuaternion U) (quaternionPrintedSource L x g1 g2)).coeff α) := by
    simpa only [quaternionPrintedSource_eval] using printed_source_coeff_continuous L x g1 g2 α
  simpa only [quaternionPrintedSource_eval] using symbolicEq11Insertion_integral L σ hσ v hv
    (fun x ↦ quaternionPrintedSource L x g1 g2)
    (fun x ↦ quaternionPrintedSource_constantCoeff L x g1 g2) hC J k

/-- Joint Haar then Gaussian evaluation for the original closed word. -/
theorem symbolicClosedEq11_integral (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ)
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    (∫ U : Links L, sourceInsertionValue L U (fun x ↦ closedSource L U x g1 g2) J k
      ∂linkHaar L) =
    ∫ h : Auxiliary L → ℝ, MvPolynomial.eval (Sum.elim (fun j ↦ (h j : ℂ)) J)
      (contractSymbolic L (symbolicFullWeight L σ (fun x ↦ quaternionClosedSource L x g1 g2) *
        symbolicEq11Insertion L k)) ∂gaussianMeasure (Auxiliary L) v := by
  have hC (x : Site L) (α : D →₀ ℕ) :
      Continuous (fun U : Links L ↦
        (MvPolynomial.map (evaluateQuaternion U) (quaternionClosedSource L x g1 g2)).coeff α) := by
    simpa only [quaternionClosedSource_eval] using closed_source_coeff_continuous L x g1 g2 α
  simpa only [quaternionClosedSource_eval] using symbolicEq11Insertion_integral L σ hσ v hv
    (fun x ↦ quaternionClosedSource L x g1 g2)
    (fun x ↦ quaternionClosedSource_constantCoeff L x g1 g2) hC J k

end SKEFTHawking.ADW.QuaternionSU2Sphere
