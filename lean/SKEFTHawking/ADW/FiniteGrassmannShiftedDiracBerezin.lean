import SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
import SKEFTHawking.ADW.PolynomialPerturbationCoeff
import Mathlib.Algebra.Polynomial.Roots

/-!
# Shifted original Dirac determinant and its Berezin coefficients

Translation acts on the auxiliary variables of the original determinant. The
fixed-link coefficient identities include coincident coframe indices.
-/
noncomputable section

open scoped BigOperators IsMulCommutative

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

open FiniteGrassmannCoframe FiniteGrassmannEvaluation
open scoped SKEFTHawking.ADW.FiniteGrassmannEvaluation

/-- Translate the auxiliary coordinates while retaining the link coefficients. -/
def translateHaarPolynomial (L : Torus) (J : Auxiliary L → ℂ) :
    HaarPolynomial L →+* HaarPolynomial L :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun a ↦ MvPolynomial.X a + constantHaarPolynomial L (J a))

/-- The determinant of the original Dirac matrix with auxiliary source J. -/
def shiftedDiracDetHaarPolynomial (L : Torus) (J : Auxiliary L → ℂ) :
    HaarPolynomial L :=
  translateHaarPolynomial L J (diracHaarPolynomial L).det

/-- Specialize the link coefficients of the shifted determinant. -/
def shiftedDiracDetAtLink (L : Torus) (U : Links L) (J : Auxiliary L → ℂ) :
    MvPolynomial (Auxiliary L) ℂ :=
  MvPolynomial.map (coefficientEvaluation L U) (shiftedDiracDetHaarPolynomial L J)

private theorem translatedEvaluation (L : Torus) (U : Links L) (J x : Auxiliary L → ℂ) :
    (MvPolynomial.eval₂Hom (coefficientEvaluation L U) x).comp (translateHaarPolynomial L J) =
      MvPolynomial.eval₂Hom (coefficientEvaluation L U) (fun i ↦ x i + J i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [translateHaarPolynomial]
  · intro i
    simp [translateHaarPolynomial, constantHaarPolynomial, coefficientEvaluation]

/-- Evaluation uses the actual original matrix at arbitrary complex coordinates x + J. -/
theorem shiftedDiracDetAtLink_eval (L : Torus) (U : Links L) (J x : Auxiliary L → ℂ) :
    MvPolynomial.eval x (shiftedDiracDetAtLink L U J) =
      (globalMatrix L U (fun i ↦ x i + J i)).det := by
  classical
  let e := MvPolynomial.eval₂Hom (coefficientEvaluation L U) (fun i ↦ x i + J i)
  have he : e.mapMatrix (diracHaarPolynomial L) = globalMatrix L U (fun i ↦ x i + J i) := by
    ext p q
    change e (diracHaarPolynomial L p q) = _
    simp [e, diracHaarPolynomial, globalMatrix, coefficientEvaluation]
  unfold shiftedDiracDetAtLink shiftedDiracDetHaarPolynomial
  rw [← MvPolynomial.eval₂_eq_eval_map]
  change ((MvPolynomial.eval₂Hom (coefficientEvaluation L U) x).comp
    (translateHaarPolynomial L J)) (diracHaarPolynomial L).det = _
  rw [translatedEvaluation]
  change e (diracHaarPolynomial L).det = _
  rw [e.map_det, he]

/-- The finite exponential of the original Dirac bilinear at complex coordinates. -/
def diracCoframeExp (L : Torus) (U : Links L) (v : Auxiliary L → ℂ) : Grassmann L :=
  nilExp (4 * volume L) (barMpsi L (globalMatrix L U v))

private def coframeAt (L : Torus) (U : Links L) (a : Auxiliary L) : Grassmann L :=
  coframe L U a.1 a.2.1 a.2.2

private def addCoordinate {ι : Type*} [DecidableEq ι] (x : ι → ℂ) (a : ι) (t : ℂ) :
    ι → ℂ :=
  fun i ↦ x i + if i = a then t else 0

private theorem eval_coordinatePerturbation {ι : Type*} [DecidableEq ι]
    (x : ι → ℂ) (a : ι) (t : ℂ) (P : MvPolynomial ι ℂ) :
    (coordinatePerturbation x a P).eval t = MvPolynomial.eval (addCoordinate x a t) P := by
  have h : (Polynomial.evalRingHom t).comp (coordinatePerturbation x a) =
      MvPolynomial.eval (addCoordinate x a t) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinatePerturbation]
    · intro i
      by_cases hi : i = a <;> simp [coordinatePerturbation, addCoordinate, hi]
  exact DFunLike.congr_fun h P

private theorem addCoordinate_shift {ι : Type*} [DecidableEq ι]
    (x J : ι → ℂ) (a : ι) (t : ℂ) :
    (fun i ↦ addCoordinate x a t i + J i) = addCoordinate (fun i ↦ x i + J i) a t := by
  funext i
  simp only [addCoordinate]
  abel

private theorem diracCoframeExp_addCoordinate (L : Torus) (U : Links L)
    (v : Auxiliary L → ℂ) (a : Auxiliary L) (t : ℂ) :
    diracCoframeExp L U (addCoordinate v a t) =
      nilExp (4 * volume L) (t • coframeAt L U a) * diracCoframeExp L U v := by
  classical
  let P : MvPolynomial (Auxiliary L) ℂ := MvPolynomial.C t * MvPolynomial.X a
  let Q : MvPolynomial (Auxiliary L) ℂ :=
    ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i
  have hP : P.constantCoeff = 0 := by simp [P]
  have hQ : Q.constantCoeff = 0 := by simp [Q]
  let f := (bilinearAlgebra L).val
  let e : MvPolynomial (Auxiliary L) ℂ →ₐ[ℂ] bilinearAlgebra L :=
    MvPolynomial.aeval (coframeEven L U)
  have hp : f (e P) = t • coframeAt L U a := by
    simp [f, e, P, coframeAt, coframeEven, Algebra.smul_def]
  have hq : f (e Q) = barMpsi L (globalMatrix L U v) := by
    rw [globalMatrix_eq9]
    simp [f, e, Q, coframeEven, Algebra.smul_def]
  have hv : barMpsi L (globalMatrix L U (addCoordinate v a t)) =
      t • coframeAt L U a + barMpsi L (globalMatrix L U v) := by
    rw [globalMatrix_eq9, globalMatrix_eq9]
    simp only [addCoordinate, add_smul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    simp [coframeAt, ite_smul]
  have hadd := congrArg f (coframe_nilExp_add L U P Q hP hQ)
  change f (nilExp (4 * volume L) (e (P + Q))) =
    f (nilExp (4 * volume L) (e P) * nilExp (4 * volume L) (e Q)) at hadd
  rw [map_nilExp, map_mul, map_nilExp, map_nilExp, map_add e, map_add f, hp, hq] at hadd
  simpa only [diracCoframeExp, hv] using hadd

private def coframeInsertionPolynomial (L : Torus) (U : Links L)
    (v : Auxiliary L → ℂ) (a : Auxiliary L) (B : Grassmann L) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (4 * volume L + 1), Polynomial.monomial k
    ((k.factorial : ℂ)⁻¹ * berezin L (B * coframeAt L U a ^ k * diracCoframeExp L U v))

private theorem coframeInsertionPolynomial_eval (L : Torus) (U : Links L)
    (v : Auxiliary L → ℂ) (a : Auxiliary L) (B : Grassmann L) (t : ℂ) :
    (coframeInsertionPolynomial L U v a B).eval t =
      berezin L (B * diracCoframeExp L U (addCoordinate v a t)) := by
  rw [diracCoframeExp_addCoordinate, nilExp]
  simp only [coframeInsertionPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Finset.sum_mul, Finset.mul_sum, smul_pow, mul_smul_comm, smul_mul_assoc, map_sum,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_assoc]
  ring

private theorem coframeInsertionPolynomial_coeff_one (L : Torus) (U : Links L)
    (v : Auxiliary L → ℂ) (a : Auxiliary L) (B : Grassmann L) :
    (coframeInsertionPolynomial L U v a B).coeff 1 =
      berezin L (B * coframeAt L U a * diracCoframeExp L U v) := by
  have hpos : 0 < volume L := Fintype.card_pos
  have hmem : 1 ∈ Finset.range (4 * volume L + 1) := by
    simp only [Finset.mem_range]
    omega
  simp only [coframeInsertionPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single_of_mem 1 hmem]
  · simp
  · intro k _ hk
    simp [hk]

/-- The first auxiliary derivative inserts the corresponding original coframe. -/
theorem shiftedDiracDetAtLink_first (L : Torus) (U : Links L)
    (J x : Auxiliary L → ℂ) (a : Auxiliary L) :
    MvPolynomial.eval x (MvPolynomial.pderiv a (shiftedDiracDetAtLink L U J)) =
      berezin L (coframe L U a.1 a.2.1 a.2.2 * diracCoframeExp L U (fun i ↦ x i + J i)) := by
  have hp : coordinatePerturbation x a (shiftedDiracDetAtLink L U J) =
      coframeInsertionPolynomial L U (fun i ↦ x i + J i) a 1 := by
    apply Polynomial.funext
    intro t
    rw [eval_coordinatePerturbation, shiftedDiracDetAtLink_eval,
      coframeInsertionPolynomial_eval, addCoordinate_shift, one_mul, diracCoframeExp,
      berezin_nilExp_det]
  have h := congrArg (fun p : Polynomial ℂ ↦ p.coeff 1) hp
  simpa only [coordinatePerturbation_coeff_one, coframeInsertionPolynomial_coeff_one,
    one_mul, coframeAt] using h

/-- Differentiating first in a and then in b inserts the ordered coframes, including a = b. -/
theorem shiftedDiracDetAtLink_mixed (L : Torus) (U : Links L)
    (J x : Auxiliary L → ℂ) (a b : Auxiliary L) :
    MvPolynomial.eval x (MvPolynomial.pderiv b
      (MvPolynomial.pderiv a (shiftedDiracDetAtLink L U J))) =
      berezin L (coframe L U a.1 a.2.1 a.2.2 * coframe L U b.1 b.2.1 b.2.2 *
        diracCoframeExp L U (fun i ↦ x i + J i)) := by
  have hp : coordinatePerturbation x b (MvPolynomial.pderiv a (shiftedDiracDetAtLink L U J)) =
      coframeInsertionPolynomial L U (fun i ↦ x i + J i) b (coframeAt L U a) := by
    apply Polynomial.funext
    intro t
    rw [eval_coordinatePerturbation, shiftedDiracDetAtLink_first,
      coframeInsertionPolynomial_eval, addCoordinate_shift, coframeAt]
  have h := congrArg (fun p : Polynomial ℂ ↦ p.coeff 1) hp
  simpa only [coordinatePerturbation_coeff_one, coframeInsertionPolynomial_coeff_one,
    coframeAt] using h

/-- With zero source, translation recovers the original determinant polynomial. -/
theorem shiftedDiracDetHaarPolynomial_zero (L : Torus) :
    shiftedDiracDetHaarPolynomial L 0 = (diracHaarPolynomial L).det := by
  have h : translateHaarPolynomial L 0 = RingHom.id (HaarPolynomial L) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [translateHaarPolynomial]
    · intro i
      simp [translateHaarPolynomial, constantHaarPolynomial]
  simp [shiftedDiracDetHaarPolynomial, h]

/-- The first Berezin insertion is the coefficient of one formal increment. -/
theorem shiftedDiracDetAtLink_coeff_one (L : Torus) (U : Links L)
    (J x : Auxiliary L → ℂ) (a : Auxiliary L) :
    (coordinatePerturbation x a (shiftedDiracDetAtLink L U J)).coeff 1 =
      berezin L (coframe L U a.1 a.2.1 a.2.2 * diracCoframeExp L U (fun i ↦ x i + J i)) := by
  rw [coordinatePerturbation_coeff_one, shiftedDiracDetAtLink_first]

/-- The mixed Berezin insertion is the outer-one, inner-one coefficient of two formal increments. -/
theorem shiftedDiracDetAtLink_coeff_one_one (L : Torus) (U : Links L)
    (J x : Auxiliary L → ℂ) (a b : Auxiliary L) :
    ((twoCoordinatePerturbations x a b (shiftedDiracDetAtLink L U J)).coeff 1).coeff 1 =
      berezin L (coframe L U a.1 a.2.1 a.2.2 * coframe L U b.1 b.2.1 b.2.2 *
        diracCoframeExp L U (fun i ↦ x i + J i)) := by
  rw [twoCoordinatePerturbations_coeff_one_one, shiftedDiracDetAtLink_mixed]

private theorem haarEvaluation_eq_specialized (L : Torus) (U : Links L)
    (h : Auxiliary L → ℝ) (P : HaarPolynomial L) :
    haarPolynomialEvaluation L U h P =
      MvPolynomial.eval (fun i ↦ (h i : ℂ)) (MvPolynomial.map (coefficientEvaluation L U) P) :=
  MvPolynomial.eval₂_eq_eval_map _ _ _

/-- The shifted determinant evaluated at real auxiliary coordinates for Gaussian-Haar integration. -/
theorem shiftedDiracDetHaarPolynomial_eval (L : Torus) (U : Links L)
    (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ) :
    haarPolynomialEvaluation L U h (shiftedDiracDetHaarPolynomial L J) =
      (globalMatrix L U (fun i ↦ (h i : ℂ) + J i)).det := by
  rw [haarEvaluation_eq_specialized]
  exact shiftedDiracDetAtLink_eval L U J (fun i ↦ (h i : ℂ))

/-- The first partial of the shifted Haar polynomial has the original coframe insertion. -/
theorem shiftedDiracDetHaarPolynomial_first (L : Torus) (U : Links L)
    (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ) (a : Auxiliary L) :
    haarPolynomialEvaluation L U h (MvPolynomial.pderiv a (shiftedDiracDetHaarPolynomial L J)) =
      berezin L (coframe L U a.1 a.2.1 a.2.2 *
        diracCoframeExp L U (fun i ↦ (h i : ℂ) + J i)) := by
  rw [haarEvaluation_eq_specialized, ← MvPolynomial.pderiv_map]
  exact shiftedDiracDetAtLink_first L U J (fun i ↦ (h i : ℂ)) a

/-- The ordered mixed partial of the shifted Haar polynomial, including the diagonal. -/
theorem shiftedDiracDetHaarPolynomial_mixed (L : Torus) (U : Links L)
    (J : Auxiliary L → ℂ) (h : Auxiliary L → ℝ) (a b : Auxiliary L) :
    haarPolynomialEvaluation L U h (MvPolynomial.pderiv b
      (MvPolynomial.pderiv a (shiftedDiracDetHaarPolynomial L J))) =
      berezin L (coframe L U a.1 a.2.1 a.2.2 * coframe L U b.1 b.2.1 b.2.2 *
        diracCoframeExp L U (fun i ↦ (h i : ℂ) + J i)) := by
  rw [haarEvaluation_eq_specialized, ← MvPolynomial.pderiv_map, ← MvPolynomial.pderiv_map]
  exact shiftedDiracDetAtLink_mixed L U J (fun i ↦ (h i : ℂ)) a b

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
