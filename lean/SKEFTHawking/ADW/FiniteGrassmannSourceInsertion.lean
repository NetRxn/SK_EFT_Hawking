import SKEFTHawking.ADW.FiniteGrassmannShiftedDiracBerezin
import SKEFTHawking.ADW.GaussianHaarPolynomialStein

/-!
# Original finite source insertion integrals

The complex source shifts the Dirac determinant alone. The complete original
site weights and the normalized Haar and Gaussian measures are retained.
-/
noncomputable section

open MeasureTheory
open scoped BigOperators NNReal IsMulCommutative

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

open FiniteGrassmannCoframe FiniteGrassmannEvaluation
open GaussianGrassmannAuxiliary FiniteGrassmannSourceAuxiliary
open scoped SKEFTHawking.ADW.FiniteGrassmannEvaluation

private def linearCoframePolynomial (L : Torus) (v : Auxiliary L → ℂ) :
    MvPolynomial (Auxiliary L) ℂ :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i

private theorem linearCoframePolynomial_constantCoeff (L : Torus) (v : Auxiliary L → ℂ) :
    (linearCoframePolynomial L v).constantCoeff = 0 := by
  simp [linearCoframePolynomial]

private theorem linearCoframePolynomial_eval (L : Torus) (U : Links L)
    (v : Auxiliary L → ℂ) :
    ((MvPolynomial.aeval (coframeEven L U) (linearCoframePolynomial L v) :
      bilinearAlgebra L) : Grassmann L) = barMpsi L (globalMatrix L U v) := by
  rw [globalMatrix_eq9]
  simp [linearCoframePolynomial, coframeEven, Algebra.smul_def]

private theorem diracCoframeExp_add (L : Torus) (U : Links L) (v w : Auxiliary L → ℂ) :
    diracCoframeExp L U (fun i ↦ v i + w i) =
      diracCoframeExp L U v * diracCoframeExp L U w := by
  let f := (bilinearAlgebra L).val
  have h := congrArg f
    (coframe_nilExp_add L U (linearCoframePolynomial L v) (linearCoframePolynomial L w)
      (linearCoframePolynomial_constantCoeff L v) (linearCoframePolynomial_constantCoeff L w))
  change f (nilExp (4 * volume L) (MvPolynomial.aeval (coframeEven L U)
    (linearCoframePolynomial L v + linearCoframePolynomial L w))) =
    f (nilExp (4 * volume L) (MvPolynomial.aeval (coframeEven L U)
      (linearCoframePolynomial L v)) *
      nilExp (4 * volume L) (MvPolynomial.aeval (coframeEven L U)
        (linearCoframePolynomial L w))) at h
  have hsum : linearCoframePolynomial L (fun i ↦ v i + w i) =
      linearCoframePolynomial L v + linearCoframePolynomial L w := by
    simp [linearCoframePolynomial, map_add, add_mul, Finset.sum_add_distrib]
  rw [← hsum, map_nilExp, map_mul, map_nilExp, map_nilExp] at h
  have he (t : Auxiliary L → ℂ) :
      f (MvPolynomial.aeval (coframeEven L U) (linearCoframePolynomial L t)) =
        barMpsi L (globalMatrix L U t) := linearCoframePolynomial_eval L U t
  rw [he, he, he] at h
  exact h

/-- The original source word evaluated in the coframe algebra, at its common finite cutoff. -/
def sourceWordExp (L : Torus) (U : Links L) (S : Site L → Polynomial) : Grassmann L :=
  nilExp (4 * volume L)
    (∑ x, ((MvPolynomial.aeval (localCoframe L U x) (S x) :
      bilinearAlgebra L) : Grassmann L))

private def insertionFunctional (L : Torus) (I E : Grassmann L) : Grassmann L →L[ℂ] ℂ :=
  ((berezin L).comp (LinearMap.mulLeft ℂ (I * E))).toContinuousLinearMap

private theorem fixedLinkSourceInsertion (L : Torus) (U : Links L) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : Site L → Polynomial)
    (hS : ∀ x, (S x).constantCoeff = 0) (J : Auxiliary L → ℂ) (I : Grassmann L) :
    (∫ h : Auxiliary L → ℝ, fullWeight L σ S h *
      berezin L (I * diracCoframeExp L U (fun i ↦ (h i : ℂ) + J i))
      ∂gaussianMeasure (Auxiliary L) v) =
      berezin L (I * (diracCoframeExp L U J * sourceWordExp L U S)) := by
  let F := insertionFunctional L I (diracCoframeExp L U J)
  have h := F.integral_comp_comm (uncurried_global_integrable L U σ hσ v hv S)
  rw [uncurried_global_eq7 L U σ hσ v hv S hS] at h
  convert h using 1
  · congr 1
    funext x
    change _ = berezin L ((I * diracCoframeExp L U J) *
      uncurriedIntegrand L U σ S x)
    have he : diracCoframeExp L U (fun i ↦ (x i : ℂ) + J i) =
        diracCoframeExp L U J * nilExp (4 * volume L)
          (∑ i, (x i : ℂ) • coframe L U i.1 i.2.1 i.2.2) := by
      simp_rw [add_comm (↑(x _) : ℂ)]
      rw [diracCoframeExp_add]
      congr 1
      rw [diracCoframeExp, globalMatrix_eq9]
    rw [he, uncurriedIntegrand, mul_smul_comm, map_smul, smul_eq_mul]
    rw [fullWeight, mul_assoc]
  · change _ = berezin L ((I * diracCoframeExp L U J) * sourceWordExp L U S)
    rw [mul_assoc]


/-- The original source coefficients of orders zero, one, and ordered mixed two. -/
inductive CoframeInsertion (L : Torus)
  | zero
  | first (a : Auxiliary L)
  | mixed (a b : Auxiliary L)

/-- Ordered Grassmann multiplication at the original link configuration. -/
def CoframeInsertion.factor {L : Torus} (U : Links L) :
    CoframeInsertion L → Grassmann L
  | .zero => 1
  | .first a => coframe L U a.1 a.2.1 a.2.2
  | .mixed a b => coframe L U a.1 a.2.1 a.2.2 * coframe L U b.1 b.2.1 b.2.2

/-- Differentiate the determinant alone, in order a then b for the mixed coefficient. -/
def CoframeInsertion.deriv {L : Torus} (P : HaarPolynomial L) :
    CoframeInsertion L → HaarPolynomial L
  | .zero => P
  | .first a => MvPolynomial.pderiv a P
  | .mixed a b => MvPolynomial.pderiv b (MvPolynomial.pderiv a P)

/-- The transferred Gaussian adjoints act in reverse order on the full weight. -/
def CoframeInsertion.adjointWeight {L : Torus} (σ : ℝ) (W : HaarPolynomial L) :
    CoframeInsertion L → HaarPolynomial L
  | .zero => W
  | .first a => haarGaussianWeightAdjoint L σ a W
  | .mixed a b => haarGaussianWeightAdjoint L σ a (haarGaussianWeightAdjoint L σ b W)

/-- The entire original weight remains fixed as the source varies. -/
def sourceWeightHaarPolynomial (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) : HaarPolynomial L :=
  ∏ x, siteWeightHaarPolynomial L σ S hS hC x

theorem sourceWeightHaarPolynomial_eval (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (U : Links L) (h : Auxiliary L → ℝ) :
    haarPolynomialEvaluation L U h (sourceWeightHaarPolynomial L σ S hS hC) =
      fullWeight L σ (S U) h := by
  classical
  simp only [sourceWeightHaarPolynomial, map_prod, siteWeightHaarPolynomial_eval, fullWeight]

/-- Original ordered Berezin insertion at a fixed link. -/
def sourceInsertionValue (L : Torus) (U : Links L) (S : Site L → Polynomial)
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) : ℂ :=
  berezin L (k.factor U * (diracCoframeExp L U J * sourceWordExp L U S))

/-- The full Haar polynomial for the inserted Gaussian integrand. -/
def sourceInsertionDensity (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) : HaarPolynomial L :=
  sourceWeightHaarPolynomial L σ S hS hC * k.deriv (shiftedDiracDetHaarPolynomial L J)

theorem sourceInsertionDensity_eval (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) (U : Links L) (h : Auxiliary L → ℝ) :
    haarPolynomialEvaluation L U h (sourceInsertionDensity L σ S hS hC J k) =
      fullWeight L σ (S U) h *
        berezin L (k.factor U * diracCoframeExp L U (fun i ↦ (h i : ℂ) + J i)) := by
  rw [sourceInsertionDensity, map_mul, sourceWeightHaarPolynomial_eval]
  congr 1
  cases k with
  | zero =>
    simp only [CoframeInsertion.deriv, CoframeInsertion.factor, one_mul,
      shiftedDiracDetHaarPolynomial_eval, diracCoframeExp, berezin_nilExp_det]
  | first a =>
    exact shiftedDiracDetHaarPolynomial_first L U J h a
  | mixed a b =>
    exact shiftedDiracDetHaarPolynomial_mixed L U J h a b

/-- Joint absolute integrability retains all link and auxiliary coordinates. -/
theorem sourceInsertionDensity_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    Integrable (fun z : Links L × (Auxiliary L → ℝ) ↦
      haarPolynomialEvaluation L z.1 z.2 (sourceInsertionDensity L σ S hS hC J k))
      ((linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) :=
  haarPolynomial_integrable L σ hσ v hv _

/-- The fixed-link source integral equals the actual original Berezin insertion. -/
theorem sourceInsertion_fixed_link (L : Torus) (U : Links L) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    (∫ h : Auxiliary L → ℝ,
      haarPolynomialEvaluation L U h (sourceInsertionDensity L σ S hS hC J k)
      ∂gaussianMeasure (Auxiliary L) v) = sourceInsertionValue L U (S U) J k := by
  simp_rw [sourceInsertionDensity_eval]
  exact fixedLinkSourceInsertion L U σ hσ v hv (S U) (hS U) J (k.factor U)

/-- The original Berezin source integrand is integrable over the normalized link measure. -/
theorem sourceInsertionValue_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    Integrable (fun U : Links L ↦ sourceInsertionValue L U (S U) J k) (linkHaar L) := by
  apply (sourceInsertionDensity_integrable L σ hσ v hv S hS hC J k).integral_prod_left.congr
  exact Filter.Eventually.of_forall (fun U ↦ sourceInsertion_fixed_link L U σ hσ v hv S hS hC J k)

/-- Original Eq11 at the fixed finite regulator, with the actual joint product measure. -/
theorem sourceInsertion_eq11 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    (∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L) =
      ∫ z : Links L × (Auxiliary L → ℝ),
        haarPolynomialEvaluation L z.1 z.2 (sourceInsertionDensity L σ S hS hC J k)
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) := by
  rw [integral_prod _ (sourceInsertionDensity_integrable L σ hσ v hv S hS hC J k)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun U ↦
    (sourceInsertion_fixed_link L U σ hσ v hv S hS hC J k).symm))

/-- Both iterated orders follow from the actual joint integrability bound. -/
theorem sourceInsertion_iterated (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    let f := fun U h ↦ haarPolynomialEvaluation L U h (sourceInsertionDensity L σ S hS hC J k)
    (∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L) =
      (∫ U : Links L, ∫ h : Auxiliary L → ℝ, f U h
        ∂gaussianMeasure (Auxiliary L) v ∂linkHaar L) ∧
    (∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L) =
      (∫ h : Auxiliary L → ℝ, ∫ U : Links L, f U h
        ∂linkHaar L ∂gaussianMeasure (Auxiliary L) v) := by
  dsimp only
  have hi := sourceInsertionDensity_integrable L σ hσ v hv S hS hC J k
  have h := (sourceInsertion_eq11 L σ hσ v hv S hS hC J k).trans (integral_prod _ hi)
  exact ⟨h, h.trans (integral_integral_swap hi)⟩

/-- Move the source derivatives onto the fixed full weight by the centered Gaussian adjoints. -/
theorem sourceInsertion_eq11_adjoint (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    (∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L) =
      ∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2
        (k.adjointWeight σ (sourceWeightHaarPolynomial L σ S hS hC) *
          shiftedDiracDetHaarPolynomial L J)
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) := by
  rw [sourceInsertion_eq11 L σ hσ v hv S hS hC J k]
  let W := sourceWeightHaarPolynomial L σ S hS hC
  let P := shiftedDiracDetHaarPolynomial L J
  cases k with
  | zero => rfl
  | first a => exact integral_haar_eval_weight_pderiv L σ hσ v hv a W P
  | mixed a b => exact integral_haar_eval_weight_pderiv_pderiv L σ hσ v hv b a W P

/-- The mixed transferred weight includes the diagonal negative contact. -/
theorem sourceInsertion_mixed_adjointWeight (L : Torus) (σ : ℝ) (a b : Auxiliary L)
    (W : HaarPolynomial L) :
    let q := constantHaarPolynomial L (((σ : ℂ) ^ 2)⁻¹)
    (CoframeInsertion.mixed a b).adjointWeight σ W =
      (q ^ 2 * MvPolynomial.X b * MvPolynomial.X a - if b = a then q else 0) * W -
        q * MvPolynomial.X b * MvPolynomial.pderiv a W -
        q * MvPolynomial.X a * MvPolynomial.pderiv b W +
        MvPolynomial.pderiv a (MvPolynomial.pderiv b W) :=
  haarGaussianWeightAdjoint_comp L σ b a W


/-- The complete inserted Berezin integrand is a single original coframe exponential. -/
theorem sourceInsertionValue_eq_nilExp (L : Torus) (U : Links L) (S : Site L → Polynomial)
    (hS : ∀ x, (S x).constantCoeff = 0) (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    sourceInsertionValue L U S J k =
      berezin L (k.factor U * nilExp (4 * volume L)
        (barMpsi L (globalMatrix L U J) +
          ∑ x, ((MvPolynomial.aeval (localCoframe L U x) (S x) :
            bilinearAlgebra L) : Grassmann L))) := by
  classical
  let P := linearCoframePolynomial L J
  let Q := ∑ x, atSite L x (S x)
  have hQ : MvPolynomial.constantCoeff Q = 0 := by
    simp [Q, atSite, hS]
  let f := (bilinearAlgebra L).val
  let e : MvPolynomial (Auxiliary L) ℂ →ₐ[ℂ] bilinearAlgebra L :=
    MvPolynomial.aeval (coframeEven L U)
  have hp : f (e P) = barMpsi L (globalMatrix L U J) := linearCoframePolynomial_eval L U J
  have hq : f (e Q) =
      ∑ x, ((MvPolynomial.aeval (localCoframe L U x) (S x) :
        bilinearAlgebra L) : Grassmann L) := by
    simp only [e, Q, map_sum, atSite_evaluation, f, Subalgebra.coe_val]
  have hadd := congrArg f (coframe_nilExp_add L U P Q
    (linearCoframePolynomial_constantCoeff L J) hQ)
  change f (nilExp (4 * volume L) (e (P + Q))) =
    f (nilExp (4 * volume L) (e P) * nilExp (4 * volume L) (e Q)) at hadd
  rw [map_nilExp, map_mul, map_nilExp, map_nilExp, map_add e, map_add f, hp, hq] at hadd
  rw [sourceInsertionValue, sourceWordExp, diracCoframeExp, hadd]

/-- At zero source and order zero, the Berezin integrand is precisely the original Eq10 one. -/
theorem sourceInsertionValue_zero (L : Torus) (U : Links L) (S : Site L → Polynomial) :
    sourceInsertionValue L U S 0 .zero = berezin L (sourceWordExp L U S) := by
  simp [sourceInsertionValue, CoframeInsertion.factor, diracCoframeExp, globalMatrix_eq9]

/-- The zero-source joint density is exactly the complete original Eq10 polynomial. -/
theorem sourceInsertionDensity_zero (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) :
    sourceInsertionDensity L σ S hS hC 0 .zero = completeHaarPolynomial L σ S hS hC := by
  rw [sourceInsertionDensity, CoframeInsertion.deriv, shiftedDiracDetHaarPolynomial_zero]
  rfl

/-- Zero source and order zero recover the exact determinant and weight integrands of Eq10. -/
theorem sourceInsertion_eq11_zero_eq10 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) :
    (∫ U : Links L, berezin L (sourceWordExp L U (S U)) ∂linkHaar L) =
      ∫ z : Links L × (Auxiliary L → ℝ),
        fullWeight L σ (S z.1) z.2 * (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) := by
  simpa only [sourceInsertionValue_zero, sourceInsertionDensity_zero,
    completeHaarPolynomial_eval] using sourceInsertion_eq11 L σ hσ v hv S hS hC 0 .zero

/-- Original Eq11 for the printed word, with direct and Gaussian-adjoint forms. -/
theorem printed_sourceInsertion_eq11 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ)
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    let S := fun U x ↦ printedSource L U x g1 g2
    let hS := fun U x ↦ printedSource_constantCoeff L U x g1 g2
    let hC := fun x α ↦ printed_source_coeff_continuous L x g1 g2 α
    let B := ∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L
    B = (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2
        (sourceInsertionDensity L σ S hS hC J k)
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) ∧
    B = (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2
        (k.adjointWeight σ (sourceWeightHaarPolynomial L σ S hS hC) *
          shiftedDiracDetHaarPolynomial L J)
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) := by
  dsimp only
  exact ⟨sourceInsertion_eq11 L σ hσ v hv _ _ _ J k,
    sourceInsertion_eq11_adjoint L σ hσ v hv _ _ _ J k⟩

/-- Original Eq11 for the closed word, with direct and Gaussian-adjoint forms. -/
theorem closed_sourceInsertion_eq11 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ)
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    let S := fun U x ↦ closedSource L U x g1 g2
    let hS := fun U x ↦ closedSource_constantCoeff L U x g1 g2
    let hC := fun x α ↦ closed_source_coeff_continuous L x g1 g2 α
    let B := ∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L
    B = (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2
        (sourceInsertionDensity L σ S hS hC J k)
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) ∧
    B = (∫ z : Links L × (Auxiliary L → ℝ), haarPolynomialEvaluation L z.1 z.2
        (k.adjointWeight σ (sourceWeightHaarPolynomial L σ S hS hC) *
          shiftedDiracDetHaarPolynomial L J)
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) := by
  dsimp only
  exact ⟨sourceInsertion_eq11 L σ hσ v hv _ _ _ J k,
    sourceInsertion_eq11_adjoint L σ hσ v hv _ _ _ J k⟩

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
