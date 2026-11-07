import SKEFTHawking.ADW.FiniteGrassmannSourceInsertion

/-!
# The finite original source generating polynomial

The source is an independent polynomial variable. Each coefficient is integrated
against the same joint Haar-Gaussian measure, with the complete original weight.
-/
noncomputable section

open MeasureTheory
open scoped BigOperators NNReal IsMulCommutative

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

open FiniteGrassmannCoframe FiniteGrassmannEvaluation
open GaussianGrassmannAuxiliary FiniteGrassmannSourceAuxiliary
open scoped SKEFTHawking.ADW.FiniteGrassmannEvaluation

/-- The outer variables are source coordinates and the coefficients retain the auxiliary ones. -/
abbrev SymbolicSourcePolynomial (L : Torus) :=
  MvPolynomial (Auxiliary L) (HaarPolynomial L)

/-- Formal addition of an independent source to the auxiliary coordinates. -/
def symbolicSourceTranslation (L : Torus) :
    HaarPolynomial L →+* SymbolicSourcePolynomial L :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun a ↦ MvPolynomial.C (MvPolynomial.X a) + MvPolynomial.X a)

/-- Specialization of the symbolic source reproduces the original shift. -/
theorem symbolicSourceTranslation_specialize (L : Torus) (J : Auxiliary L → ℂ)
    (P : HaarPolynomial L) :
    MvPolynomial.eval₂ (RingHom.id _) (fun a ↦ constantHaarPolynomial L (J a))
        (symbolicSourceTranslation L P) = translateHaarPolynomial L J P := by
  let s := MvPolynomial.eval₂Hom (RingHom.id (HaarPolynomial L))
    (fun a ↦ constantHaarPolynomial L (J a))
  have h : s.comp (symbolicSourceTranslation L) = translateHaarPolynomial L J := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [s, symbolicSourceTranslation, translateHaarPolynomial]
    · intro a
      simp [s, symbolicSourceTranslation, translateHaarPolynomial]
  exact DFunLike.congr_fun h P

private theorem translation_pderiv {ι R S : Type*} [CommSemiring R] [CommSemiring S]
    (a : ι) (f : MvPolynomial ι R →+* MvPolynomial ι S)
    (hC : ∀ c, MvPolynomial.pderiv a (f (MvPolynomial.C c)) = 0)
    (hX : ∀ b, MvPolynomial.pderiv a (f (MvPolynomial.X b)) =
      f (MvPolynomial.pderiv a (MvPolynomial.X b)))
    (P : MvPolynomial ι R) :
    MvPolynomial.pderiv a (f P) = f (MvPolynomial.pderiv a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [hC, MvPolynomial.pderiv_C, map_zero]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P b hP => simp only [map_mul, MvPolynomial.pderiv_mul, hP, hX, map_add]

/-- A symbolic source partial agrees with translating the corresponding auxiliary partial. -/
theorem symbolicSourceTranslation_pderiv (L : Torus) (a : Auxiliary L)
    (P : HaarPolynomial L) :
    MvPolynomial.pderiv a (symbolicSourceTranslation L P) =
      symbolicSourceTranslation L (MvPolynomial.pderiv a P) := by
  apply translation_pderiv
  · intro c
    simp [symbolicSourceTranslation]
  · intro b
    by_cases h : b = a
    · subst b
      simp [symbolicSourceTranslation]
    · simp [symbolicSourceTranslation, MvPolynomial.pderiv_X_of_ne h]

private theorem translateHaarPolynomial_pderiv (L : Torus) (J : Auxiliary L → ℂ)
    (a : Auxiliary L) (P : HaarPolynomial L) :
    MvPolynomial.pderiv a (translateHaarPolynomial L J P) =
      translateHaarPolynomial L J (MvPolynomial.pderiv a P) := by
  apply translation_pderiv
  · intro c
    simp [translateHaarPolynomial]
  · intro b
    by_cases h : b = a
    · subst b
      simp [translateHaarPolynomial, constantHaarPolynomial]
    · simp [translateHaarPolynomial, constantHaarPolynomial, MvPolynomial.pderiv_X_of_ne h]

/-- The coefficient integral is additive by actual joint integrability. -/
def haarCoefficientIntegral (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) : HaarPolynomial L →+ ℂ where
  toFun P := ∫ z : Links L × (Auxiliary L → ℝ),
    haarPolynomialEvaluation L z.1 z.2 P ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)
  map_zero' := by simp
  map_add' P Q := by
    simp only [map_add]
    exact integral_add (haarPolynomial_integrable L σ hσ v hv P)
      (haarPolynomial_integrable L σ hσ v hv Q)

private theorem haarCoefficientIntegral_mul_constant (L : Torus)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (P : HaarPolynomial L) (c : ℂ) :
    haarCoefficientIntegral L σ hσ v hv (P * constantHaarPolynomial L c) =
      haarCoefficientIntegral L σ hσ v hv P * c := by
  simp only [haarCoefficientIntegral, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_mul, haarPolynomialEvaluation_constant]
  exact integral_mul_const c _

/-- Integrate the finitely supported coefficients without claiming multiplicativity. -/
def integrateSymbolicSource (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    SymbolicSourcePolynomial L →+ MvPolynomial (Auxiliary L) ℂ :=
  (AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom).comp
    ((Finsupp.mapRange.addMonoidHom (haarCoefficientIntegral L σ hσ v hv)).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

@[simp] theorem integrateSymbolicSource_coeff (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (P : SymbolicSourcePolynomial L) (d : Auxiliary L →₀ ℕ) :
    MvPolynomial.coeff d (integrateSymbolicSource L σ hσ v hv P) =
      haarCoefficientIntegral L σ hσ v hv (MvPolynomial.coeff d P) := rfl

private theorem integrateSymbolicSource_monomial (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (d : Auxiliary L →₀ ℕ) (P : HaarPolynomial L) :
    integrateSymbolicSource L σ hσ v hv (MvPolynomial.monomial d P) =
      MvPolynomial.monomial d (haarCoefficientIntegral L σ hσ v hv P) := by
  classical
  ext e
  simp only [integrateSymbolicSource_coeff, MvPolynomial.coeff_monomial]
  split <;> simp_all

/-- Formal differentiation is compatible with the finite coefficient integral. -/
theorem integrateSymbolicSource_pderiv (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (P : SymbolicSourcePolynomial L) (a : Auxiliary L) :
    MvPolynomial.pderiv a (integrateSymbolicSource L σ hσ v hv P) =
      integrateSymbolicSource L σ hσ v hv (MvPolynomial.pderiv a P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d p =>
    simp only [integrateSymbolicSource_monomial, MvPolynomial.pderiv_monomial]
    congr 1
    simp only [← nsmul_eq_mul', map_nsmul]
  | add P Q hP hQ => simp [hP, hQ]

/-- Evaluating the finite coefficient integral specializes the original joint integrand. -/
theorem integrateSymbolicSource_eval (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (P : SymbolicSourcePolynomial L) (J : Auxiliary L → ℂ) :
    MvPolynomial.eval J (integrateSymbolicSource L σ hσ v hv P) =
      haarCoefficientIntegral L σ hσ v hv
        (MvPolynomial.eval₂ (RingHom.id _) (fun a ↦ constantHaarPolynomial L (J a)) P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d p =>
    rw [integrateSymbolicSource_monomial, MvPolynomial.eval_monomial,
      MvPolynomial.eval₂_monomial, RingHom.id_apply]
    change _ = haarCoefficientIntegral L σ hσ v hv
      (p * d.prod (fun i n ↦ constantHaarPolynomial L (J i) ^ n))
    let C₀ : ℂ →+* HaarPolynomial L := algebraMap ℂ (HaarPolynomial L)
    have hc (c : ℂ) : C₀ c = constantHaarPolynomial L c := rfl
    have h : d.prod (fun i n ↦ constantHaarPolynomial L (J i) ^ n) =
        constantHaarPolynomial L (d.prod (fun i n ↦ J i ^ n)) := by
      simp only [← hc, Finsupp.prod, map_prod, map_pow]
    rw [h, haarCoefficientIntegral_mul_constant]
  | add P Q hP hQ =>
    simp only [map_add, MvPolynomial.eval₂_add, hP, hQ]


/-- The original partition polynomial in the independent complex source coordinates. -/
def sourceGeneratingPolynomial (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) :
    MvPolynomial (Auxiliary L) ℂ :=
  integrateSymbolicSource L σ hσ v hv
    (MvPolynomial.C (sourceWeightHaarPolynomial L σ S hS hC) *
      symbolicSourceTranslation L (diracHaarPolynomial L).det)

/-- Select the constant, first or ordered mixed formal source partial. -/
def CoframeInsertion.formalPartial {L : Torus} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Auxiliary L) R) : CoframeInsertion L → MvPolynomial (Auxiliary L) R
  | .zero => P
  | .first a => MvPolynomial.pderiv a P
  | .mixed a b => MvPolynomial.pderiv b (MvPolynomial.pderiv a P)

private theorem sourceGenerating_specialize_partial (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (W P : HaarPolynomial L) (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    MvPolynomial.eval J
      (k.formalPartial (integrateSymbolicSource L σ hσ v hv
        (MvPolynomial.C W * symbolicSourceTranslation L P))) =
      haarCoefficientIntegral L σ hσ v hv (W * k.deriv (translateHaarPolynomial L J P)) := by
  cases k <;>
    simp only [CoframeInsertion.formalPartial, CoframeInsertion.deriv,
      integrateSymbolicSource_pderiv, MvPolynomial.pderiv_C_mul,
      symbolicSourceTranslation_pderiv, integrateSymbolicSource_eval,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, RingHom.id_apply,
      symbolicSourceTranslation_specialize, translateHaarPolynomial_pderiv]

/-- The selected source partial evaluates to the original link-integrated Berezin insertion. -/
theorem sourceGenerating_eq11 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    MvPolynomial.eval J (k.formalPartial (sourceGeneratingPolynomial L σ hσ v hv S hS hC)) =
      ∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L := by
  rw [sourceGeneratingPolynomial, sourceGenerating_specialize_partial]
  exact (sourceInsertion_eq11 L σ hσ v hv S hS hC J k).symm

/-- The constant coefficient is the original undivided partition at zero source. -/
theorem sourceGenerating_constantCoeff (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) :
    (sourceGeneratingPolynomial L σ hσ v hv S hS hC).constantCoeff =
      ∫ U : Links L, sourceInsertionValue L U (S U) 0 .zero ∂linkHaar L := by
  rw [← MvPolynomial.eval_zero]
  exact sourceGenerating_eq11 L σ hσ v hv S hS hC 0 .zero

/-- Coefficient one of a formal increment is the original first insertion at J. -/
theorem sourceGenerating_coeff_one (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (a : Auxiliary L) :
    (coordinatePerturbation J a (sourceGeneratingPolynomial L σ hσ v hv S hS hC)).coeff 1 =
      ∫ U : Links L, sourceInsertionValue L U (S U) J (.first a) ∂linkHaar L := by
  rw [coordinatePerturbation_coeff_one]
  exact sourceGenerating_eq11 L σ hσ v hv S hS hC J (.first a)

/-- Two independent increments give the mixed insertion, including equal coordinates. -/
theorem sourceGenerating_coeff_one_one (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (J : Auxiliary L → ℂ) (a b : Auxiliary L) :
    ((twoCoordinatePerturbations J a b
        (sourceGeneratingPolynomial L σ hσ v hv S hS hC)).coeff 1).coeff 1 =
      ∫ U : Links L, sourceInsertionValue L U (S U) J (.mixed a b) ∂linkHaar L := by
  rw [twoCoordinatePerturbations_coeff_one_one]
  exact sourceGenerating_eq11 L σ hσ v hv S hS hC J (.mixed a b)

/-- The printed original source word, with exact formal source partials. -/
theorem printed_sourceGenerating_eq11 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ)
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    let S := fun U x ↦ printedSource L U x g1 g2
    let hS := fun U x ↦ printedSource_constantCoeff L U x g1 g2
    let hC := fun x α ↦ printed_source_coeff_continuous L x g1 g2 α
    MvPolynomial.eval J (k.formalPartial (sourceGeneratingPolynomial L σ hσ v hv S hS hC)) =
      ∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L :=
  sourceGenerating_eq11 L σ hσ v hv _ _ _ J k

/-- The independently retained closed word, with the same exact formal partials. -/
theorem closed_sourceGenerating_eq11 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ)
    (J : Auxiliary L → ℂ) (k : CoframeInsertion L) :
    let S := fun U x ↦ closedSource L U x g1 g2
    let hS := fun U x ↦ closedSource_constantCoeff L U x g1 g2
    let hC := fun x α ↦ closed_source_coeff_continuous L x g1 g2 α
    MvPolynomial.eval J (k.formalPartial (sourceGeneratingPolynomial L σ hσ v hv S hS hC)) =
      ∫ U : Links L, sourceInsertionValue L U (S U) J k ∂linkHaar L :=
  sourceGenerating_eq11 L σ hσ v hv _ _ _ J k

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
