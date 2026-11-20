import SKEFTHawking.ADW.FiniteDeterminantSubsetDP
import SKEFTHawking.ADW.PolynomialPerturbationCoeff
import Mathlib.Algebra.DualNumber

namespace SKEFTHawking.ADW.FiniteDeterminantRawJet

open FiniteDeterminantSubsetDP

noncomputable section

variable {R : Type*} [CommRing R]

/-!
# Raw second-order determinant coefficients

The selected slots of the Python determinant jet use two derivative positions.
Each position has square zero, even when both positions select the same label.
The existing mask recurrence runs in this commutative ring. A polynomial
perturbation gives the entry values by constant, first and undivided second
coefficients. The correspondence is at the value level and leaves concrete
Python containers, budget accounting and original Dirac matrix assembly separate.
-/

/-- Two independent square-zero positions for a selected pair of raw derivative labels. -/
abbrev PositionalJet (R : Type*) := DualNumber (DualNumber R)

/-- The four raw entries, with the first position outermost. -/
def ofSlots (v da db dab : R) : PositionalJet R := ⟨⟨v, db⟩, ⟨da, dab⟩⟩

/-- Constant term in the two positions. -/
def value (x : PositionalJet R) : R := x.fst.fst
/-- First derivative in the outer position. -/
def firstOuter (x : PositionalJet R) : R := x.snd.fst
/-- First derivative in the inner position. -/
def firstInner (x : PositionalJet R) : R := x.fst.snd
/-- Undivided second derivative in the two positions. -/
def second (x : PositionalJet R) : R := x.snd.snd

/-- The four positional splits in the Python raw product. -/
theorem ofSlots_mul (v da db dab w ea eb eab : R) :
    ofSlots v da db dab * ofSlots w ea eb eab =
      ofSlots (v * w) (v * ea + da * w) (v * eb + db * w)
        (v * eab + da * eb + db * ea + dab * w) := by
  apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext <;>
    (simp [ofSlots, TrivSqZeroExt.snd_mul, MulOpposite.smul_eq_mul_unop]; try ring)

/-- Repeating the label leaves two identical cross terms, with no division. -/
theorem diagonal_mul (v d dd w e ee : R) :
    second (ofSlots v d d dd * ofSlots w e e ee) =
      v * ee + d * e + d * e + dd * w := by
  rw [ofSlots_mul]
  rfl

@[simp]
theorem ofSlots_zero : ofSlots (0 : R) 0 0 0 = 0 := rfl

@[simp]
theorem ofSlots_one : ofSlots (1 : R) 0 0 0 = 1 := rfl

/-- Accumulating colliding mask updates adds each raw slot. -/
theorem ofSlots_add (v da db dab w ea eb eab : R) :
    ofSlots v da db dab + ofSlots w ea eb eab =
      ofSlots (v + w) (da + ea) (db + eb) (dab + eab) := rfl

/-- The sign is a constant jet and therefore scales all four slots. -/
theorem ofSlots_mul_constant (v da db dab s : R) :
    ofSlots v da db dab * ofSlots s 0 0 0 =
      ofSlots (v * s) (da * s) (db * s) (dab * s) := by
  rw [ofSlots_mul]
  simp

/-- Retain the constant and linear coefficient in one independent position. -/
def coefficientPair : Polynomial R →+* DualNumber R where
  toFun p := ⟨p.coeff 0, p.coeff 1⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [Polynomial.coeff_one]
  map_add' p q := by ext <;> simp
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · exact Polynomial.mul_coeff_zero p q
    · simp [TrivSqZeroExt.snd_mul, Polynomial.mul_coeff_one,
        MulOpposite.smul_eq_mul_unop, add_comm]

/-- Retain coefficients of degree at most one separately in the two positions. -/
def positionalCoefficients : Polynomial (Polynomial R) →+* PositionalJet R :=
  coefficientPair.comp (Polynomial.mapRingHom coefficientPair)

theorem positionalCoefficients_eq (p : Polynomial (Polynomial R)) :
    positionalCoefficients p =
      ofSlots ((p.coeff 0).coeff 0) ((p.coeff 1).coeff 0)
        ((p.coeff 0).coeff 1) ((p.coeff 1).coeff 1) := by
  simp [positionalCoefficients, coefficientPair, ofSlots]

variable {ι : Type*}

/-- Select the same four raw entries as two positional Leibniz indices. -/
def select (v : R) (d : ι → R) (dd : ι → ι → R) (a b : ι) : PositionalJet R :=
  ofSlots v (d a) (d b) (dd a b)

variable [DecidableEq ι]

/-- Sorting the pair of labels leaves the iterated partial unchanged. -/
theorem pderiv_swap (a b : ι) (p : MvPolynomial ι R) :
    MvPolynomial.pderiv b (MvPolynomial.pderiv a p) =
      MvPolynomial.pderiv a (MvPolynomial.pderiv b p) := by
  by_cases hab : a = b
  · subst b
    rfl
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
      simp only [MvPolynomial.pderiv_monomial, tsub_tsub, Finsupp.tsub_apply,
        Finsupp.single_eq_of_ne (Ne.symm hab), Finsupp.single_eq_of_ne hab, tsub_zero]
      congr 1
      · rw [add_comm (Finsupp.single b 1) (Finsupp.single a 1)]
      · ring
  | add p q hp hq => simp only [map_add, hp, hq]

/-- An absent sparse slot contributes zero in the selected positions. -/
def sparseSelect (v : Option R) (d : ι → Option R) (dd : ι → ι → Option R)
    (a b : ι) : PositionalJet R :=
  select (v.getD 0) (fun j ↦ (d j).getD 0) (fun j k ↦ (dd j k).getD 0) a b

omit [DecidableEq ι] in
theorem sparseSelect_missing (a b : ι) :
    sparseSelect (R := R) none (fun _ ↦ none) (fun _ _ ↦ none) a b = 0 :=
  ofSlots_zero

/-- Polynomial input mapped to the exact selected raw derivative entries. -/
def polynomialJet (x : ι → R) (a b : ι) : MvPolynomial ι R →+* PositionalJet R :=
  positionalCoefficients.comp (twoCoordinatePerturbations x a b)

theorem polynomialJet_eq_select (x : ι → R) (a b : ι) (p : MvPolynomial ι R) :
    polynomialJet x a b p =
      select (MvPolynomial.eval x p)
        (fun j ↦ MvPolynomial.eval x (MvPolynomial.pderiv j p))
        (fun j k ↦ MvPolynomial.eval x (MvPolynomial.pderiv k (MvPolynomial.pderiv j p)))
        a b := by
  rw [polynomialJet, RingHom.comp_apply, positionalCoefficients_eq,
    twoCoordinatePerturbations_coeff_one_one]
  have outerZero (q : MvPolynomial ι R) :
      (twoCoordinatePerturbations x a b q).coeff 0 = coordinatePerturbation x b q := by
    unfold twoCoordinatePerturbations
    rw [RingHom.comp_apply, coordinatePerturbation_coeff_zero, MvPolynomial.eval_map]
    rfl
  have outerOne :
      (twoCoordinatePerturbations x a b p).coeff 1 =
        coordinatePerturbation x b (MvPolynomial.pderiv a p) := by
    unfold twoCoordinatePerturbations
    rw [RingHom.comp_apply, coordinatePerturbation_coeff_one, MvPolynomial.pderiv_map,
      MvPolynomial.eval_map]
    rfl
  rw [outerZero, outerOne, coordinatePerturbation_coeff_zero,
    coordinatePerturbation_coeff_zero, coordinatePerturbation_coeff_one]
  rfl

/-- The bitmask recurrence with two raw derivative positions. -/
def determinantJet {n : ℕ} (M : Matrix (Fin n) (Fin n) (PositionalJet R)) :
    PositionalJet R :=
  maskSubsetDP (fun i j ↦ if h : i < n then M ⟨i, h⟩ j else 0) n ((1 <<< n) - 1)

theorem determinantJet_eq_det {n : ℕ} (M : Matrix (Fin n) (Fin n) (PositionalJet R)) :
    determinantJet M = M.det :=
  maskSubsetDP_eq_det M

/-- The mask recurrence over selected raw entries agrees with the polynomial
determinant before projection, even at empty or singular inputs. -/
theorem determinantJet_polynomial {n : ℕ} (x : ι → R) (a b : ι)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial ι R)) :
    determinantJet ((polynomialJet x a b).mapMatrix M) = polynomialJet x a b M.det := by
  rw [determinantJet_eq_det]
  exact (RingHom.map_det (R := MvPolynomial ι R) (S := PositionalJet R) (polynomialJet x a b) M).symm

/-- An absent matrix entry has zero in every derivative position.
This is the zero-filled matrix interpretation of sparse omission. -/
theorem determinantJet_polynomial_sparse {n : ℕ} (x : ι → R) (a b : ι)
    (M : Fin n → Fin n → Option (MvPolynomial ι R)) :
    determinantJet (fun i j ↦ ((M i j).map (polynomialJet x a b)).getD 0) =
      polynomialJet x a b (Matrix.of (fun i j ↦ (M i j).getD 0)).det := by
  have h :
      (fun i j ↦ ((M i j).map (polynomialJet x a b)).getD 0) =
        (polynomialJet x a b).mapMatrix (Matrix.of (fun i j ↦ (M i j).getD 0)) := by
    funext i j
    cases hM : M i j <;> simp [hM, RingHom.mapMatrix]
  rw [h, determinantJet_polynomial]

/-- Each selected output slot is the corresponding derivative of the determinant.
The case `a = b` gives the actual diagonal second derivative. -/
theorem determinantJet_polynomial_slots {n : ℕ} (x : ι → R) (a b : ι)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial ι R)) :
    let result := determinantJet ((polynomialJet x a b).mapMatrix M)
    value result = MvPolynomial.eval x M.det ∧
      firstOuter result = MvPolynomial.eval x (MvPolynomial.pderiv a M.det) ∧
      firstInner result = MvPolynomial.eval x (MvPolynomial.pderiv b M.det) ∧
      second result = MvPolynomial.eval x (MvPolynomial.pderiv b (MvPolynomial.pderiv a M.det)) := by
  dsimp only
  rw [determinantJet_polynomial, polynomialJet_eq_select]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Empty determinants give the unit jet. -/
theorem determinantJet_empty (M : Matrix (Fin 0) (Fin 0) (PositionalJet R)) :
    determinantJet M = 1 := by
  rw [determinantJet_eq_det, Matrix.det_fin_zero]

/-- Repeated full jet rows vanish. Equality at value level alone need not
annihilate derivatives. -/
theorem determinantJet_zero_of_row_eq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (PositionalJet R)) {i j : Fin n}
    (hne : i ≠ j) (heq : M i = M j) : determinantJet M = 0 := by
  rw [determinantJet_eq_det, Matrix.det_zero_of_row_eq hne heq]

end
end SKEFTHawking.ADW.FiniteDeterminantRawJet
