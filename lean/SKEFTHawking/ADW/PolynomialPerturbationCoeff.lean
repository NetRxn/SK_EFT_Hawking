import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff

namespace SKEFTHawking.ADW

noncomputable section

variable {ι R : Type*} [CommSemiring R] [DecidableEq ι]

/-- Substitute a formal increment in one coordinate of a polynomial. -/
def coordinatePerturbation (x : ι → R) (a : ι) : MvPolynomial ι R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i ↦ Polynomial.C (x i) + if i = a then Polynomial.X else 0)

/-- The constant term is the value at the unperturbed coordinates. -/
@[simp] theorem coordinatePerturbation_coeff_zero
    (x : ι → R) (a : ι) (P : MvPolynomial ι R) :
    (coordinatePerturbation x a P).coeff 0 = MvPolynomial.eval x P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [coordinatePerturbation]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, Polynomial.mul_coeff_zero, hP, map_mul, MvPolynomial.eval_X]
    by_cases hi : i = a <;> simp [coordinatePerturbation, hi]

/-- The coefficient of the formal increment is the evaluated partial derivative. -/
theorem coordinatePerturbation_coeff_one
    (x : ι → R) (a : ι) (P : MvPolynomial ι R) :
    (coordinatePerturbation x a P).coeff 1 =
      MvPolynomial.eval x (MvPolynomial.pderiv a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [coordinatePerturbation]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, Polynomial.mul_coeff_one, coordinatePerturbation_coeff_zero, hP,
      coordinatePerturbation_coeff_zero, MvPolynomial.eval_X, MvPolynomial.pderiv_mul,
      map_add, map_mul, map_mul, MvPolynomial.eval_X]
    by_cases hi : i = a
    · subst i
      simp [coordinatePerturbation, add_comm]
    · simp [coordinatePerturbation, hi, MvPolynomial.pderiv_X_of_ne hi]

/-- Substitute two independent formal increments, with the first increment outermost. -/
def twoCoordinatePerturbations (x : ι → R) (a b : ι) :
    MvPolynomial ι R →+* Polynomial (Polynomial R) :=
  (coordinatePerturbation
    (fun i ↦ Polynomial.C (x i) + if i = b then Polynomial.X else 0) a).comp
    (MvPolynomial.map Polynomial.C)

/-- Taking the first coefficient in each increment evaluates the iterated partial.
The two increments remain independent when both perturb the same coordinate. -/
theorem twoCoordinatePerturbations_coeff_one_one
    (x : ι → R) (a b : ι) (P : MvPolynomial ι R) :
    ((twoCoordinatePerturbations x a b P).coeff 1).coeff 1 =
      MvPolynomial.eval x (MvPolynomial.pderiv b (MvPolynomial.pderiv a P)) := by
  unfold twoCoordinatePerturbations
  rw [RingHom.comp_apply, coordinatePerturbation_coeff_one, MvPolynomial.pderiv_map,
    MvPolynomial.eval_map]
  exact coordinatePerturbation_coeff_one x b (MvPolynomial.pderiv a P)

end
end SKEFTHawking.ADW
