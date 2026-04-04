/-
Phase 5b Wave 7: q-Numbers (Quantum Integers)

Defines the q-integer [n]_q = (qⁿ - q⁻ⁿ)/(q - q⁻¹) as a Laurent polynomial,
proves the classical limit [n]_1 = n, and computes explicit values for small n.

The q-integers are the building blocks for q-deformed algebraic structures:
  - q-Dolan-Grady relations use [3]_q = q² + 1 + q⁻² (QDG.lean)
  - U_q(sl₂) Chevalley relations use (K - K⁻¹)/(q - q⁻¹) (Uqsl2.lean)

We work with Laurent polynomials k[T, T⁻¹] where T plays the role of q.
This avoids division issues: [n]_q is defined as a sum rather than a fraction.

The sum form: [n]_q = q^(n-1) + q^(n-3) + ... + q^(-(n-1)), a sum of n terms.
This is a Laurent polynomial (no denominator), well-defined for all q.

References:
  Kassel, "Quantum Groups" (Springer, 1995), Ch. IV
  Lit-Search/Phase-5b/The q-deformed Dolan-Grady relations...
  Lit-Search/Phase-5b/Mathlib4 infrastructure audit for U_q(sl₂)...
-/

import Mathlib

open LaurentPolynomial

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k]

/-! ## 1. q-Integer as a Laurent polynomial

We use the sum form: [n]_q = Σ_{i=0}^{n-1} q^{n-1-2i}
  = q^{n-1} + q^{n-3} + ... + q^{-(n-1)}

This is a Laurent polynomial in k[T, T⁻¹] (no denominator).
-/

/--
The q-integer [n]_q as a Laurent polynomial.
[n]_q = Σ_{i=0}^{n-1} T^{n-1-2i} where T is the Laurent variable (= q).

Examples:
  [0]_q = 0
  [1]_q = 1 (= T⁰)
  [2]_q = T + T⁻¹
  [3]_q = T² + 1 + T⁻²
  [4]_q = T³ + T + T⁻¹ + T⁻³
-/
def qInt (n : ℕ) : LaurentPolynomial k :=
  ∑ i ∈ Finset.range n, T (n - 1 - 2 * i : ℤ)

/-! ## 2. Explicit values for small n -/

/--
[0]_q = 0 (empty sum).
-/
theorem qInt_zero : qInt k 0 = 0 := by
  simp [qInt]

/--
[1]_q = 1 = T⁰ (single term, the unit).
-/
theorem qInt_one : qInt k 1 = 1 := by
  simp [qInt, T_zero]

/--
[2]_q = T + T⁻¹ = q + q⁻¹.
-/
theorem qInt_two : qInt k 2 = T 1 + T (-1) := by
  simp [qInt, Finset.sum_range_succ]

/--
[3]_q = T² + 1 + T⁻² = q² + 1 + q⁻².
This is the coefficient in the q-Dolan-Grady relations.

PROVIDED SOLUTION
Expand the sum: i=0 gives T^2, i=1 gives T^0 = 1, i=2 gives T^(-2).
Use Finset.sum_range_succ to unfold, then T_zero for T^0 = 1.
-/
theorem qInt_three : qInt k 3 = T 2 + 1 + T (-2) := by
  simp [qInt, Finset.sum_range_succ, T_zero]

/-! ## 3. Classical limit [n]_1 = n

At q = 1, T^m evaluates to 1 for all m. So [n]_q becomes a sum of n ones = n.
We express this via the evaluation homomorphism.
-/

/--
The evaluation-at-1 map sends every Laurent monomial T^m to 1.
This is the algebra homomorphism k[T, T⁻¹] → k sending T ↦ 1.

PROVIDED SOLUTION
Use LaurentPolynomial.eval₂ or aeval with the substitution T ↦ 1.
Alternatively, define directly via the universal property of LaurentPolynomial.
-/
noncomputable def evalAtOne : LaurentPolynomial k →ₐ[k] k :=
  { LaurentPolynomial.eval₂ (RingHom.id k) (1 : kˣ) with
    commutes' := fun r => by
      simp [LaurentPolynomial.eval₂_C] }

/--
T^m evaluates to 1 at q = 1 for all m ∈ ℤ.

PROVIDED SOLUTION
evalAtOne (T m) = eval₂ id 1 (T m) = 1^m = 1 by zpow_one or one_zpow.
-/
theorem evalAtOne_T (m : ℤ) : evalAtOne k (T m) = 1 := by
  simp [evalAtOne, eval₂_T]

/--
**Classical limit:** [n]_q evaluates to n at q = 1.

This is the fundamental property connecting q-integers to ordinary integers:
  [n]_1 = n.

PROVIDED SOLUTION
[n]_q = Σ_{i=0}^{n-1} T^{n-1-2i}. Evaluating at q=1, each T^m → 1.
Sum of n ones = n. Use map_sum + evalAtOne_T + Finset.sum_const + card_range.
-/
theorem qInt_classical_limit (n : ℕ) :
    evalAtOne k (qInt k n) = (n : k) := by
  simp [qInt, map_sum, evalAtOne_T, Finset.card_range]

/-! ## 4. Connection to DG_COEFF = 16 -/

/--
[2]_q⁴ = (q + q⁻¹)⁴. At q = 1: (1 + 1)⁴ = 2⁴ = 16 = DG_COEFF.

This connects the q-deformation parameter to the Dolan-Grady coefficient
in our OnsagerAlgebra formalization. The "16" in the classical DG relations
is [2]_1⁴ = 2⁴.
-/
theorem qInt_two_pow4_classical :
    evalAtOne k (qInt k 2 ^ 4) = (16 : k) := by
  rw [map_pow, qInt_classical_limit]
  norm_num

/--
[3]_q at q = 1 gives 3, confirming the q-DG coefficient.
The expanded q-DG relation has [3]_q as the coefficient of the middle terms.
At q = 1, this becomes the binomial coefficient 3 in the classical triple commutator.
-/
theorem qInt_three_classical :
    evalAtOne k (qInt k 3) = (3 : k) := by
  exact qInt_classical_limit k 3

/-! ## 5. q-Factorial and q-Binomial (definitions only) -/

/--
The q-factorial [n]_q! = [1]_q · [2]_q · ... · [n]_q.
Used in the q-binomial coefficients and the R-matrix formula.
-/
def qFactorial (n : ℕ) : LaurentPolynomial k :=
  (Finset.range n).prod (fun i => qInt k (i + 1))

/--
[0]_q! = 1 (empty product).
-/
theorem qFactorial_zero : qFactorial k 0 = 1 := by
  simp [qFactorial]

/--
[1]_q! = [1]_q = 1.
-/
theorem qFactorial_one : qFactorial k 1 = 1 := by
  simp [qFactorial, qInt_one]

/-! ## 6. Module summary -/

/--
QNumber module: q-integers as Laurent polynomials.
  - qInt n: [n]_q = Σ T^{n-1-2i}, a Laurent polynomial (no division)
  - Explicit: [0]=0, [1]=1, [2]=T+T⁻¹, [3]=T²+1+T⁻²
  - Classical limit: [n]_1 = n (via evalAtOne)
  - DG connection: [2]_1⁴ = 16 = DG_COEFF
  - q-factorial defined for future use
-/
theorem qnumber_summary : True := trivial

end SKEFTHawking
