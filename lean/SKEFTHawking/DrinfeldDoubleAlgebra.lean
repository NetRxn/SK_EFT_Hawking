/-
Phase 5b Wave 3: D(G) as a k-Algebra

The Drinfeld double D(G) = k^G ⊗_k k[G] as a proper k-algebra.

Our existing DrinfeldDoubleElement represents basis elements (f, g).
The full algebra D(G) is the free k-module on G × G with twisted multiplication.
We represent it as `G × G → k` (coefficients in the basis δ_a ⊗ g).

The multiplication extends bilinearly from the basis multiplication:
  (δ_a ⊗ g) · (δ_b ⊗ h) = δ_{a, g·b·g⁻¹} · (δ_a ⊗ g·h)

This gives D(G) the structure of a k-algebra with:
  - Addition: pointwise on G × G → k
  - Scalar multiplication: pointwise
  - Multiplication: convolution with twisted product
  - Unit: Σ_a (δ_a ⊗ e) = the identity function on the first factor

References:
  Drinfeld, "Quantum groups" (ICM 1986)
  Kassel, "Quantum Groups" (Springer, 1995), Ch. IX
-/

import Mathlib
import SKEFTHawking.DrinfeldDouble

open Finset

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-! ## 1. D(G) as a type with algebra structure -/

/--
Elements of D(G) as functions G × G → k.
The coefficient c(a, g) represents the component along basis element δ_a ⊗ g.
-/
abbrev DDAlg := G × G → k

/--
The basis element δ_a ⊗ g as an element of DDAlg.
Returns 1 at index (a, g) and 0 elsewhere.
-/
def ddBasis (a g : G) : DDAlg k G :=
  fun p => if p.1 = a ∧ p.2 = g then 1 else 0

/--
D(G) addition: pointwise on G × G → k.
-/
instance : Add (DDAlg k G) := Pi.instAdd

/--
D(G) zero: the zero function.
-/
instance : Zero (DDAlg k G) := Pi.instZero

/--
D(G) negation: pointwise negation.
-/
instance : Neg (DDAlg k G) := Pi.instNeg

/--
D(G) scalar multiplication: pointwise scaling by k.
-/
instance : SMul k (DDAlg k G) := Pi.instSMul

/-! ## 2. Twisted Multiplication -/

/--
D(G) multiplication (twisted convolution).

For f, g : DDAlg k G, the product (f * g) at index (a, h) is:
  (f * g)(a, h) = Σ_{g1 : G} f(a, g1) * g(g1⁻¹ * a * g1, g1⁻¹ * h)

On basis elements this reduces to:
  (δ_a ⊗ g1) * (δ_b ⊗ g2) = δ_{a, g1*b*g1⁻¹} * (δ_a ⊗ g1*g2)
-/
def ddAlgMul (f g : DDAlg k G) : DDAlg k G :=
  fun p => ∑ g1 : G, f (p.1, g1) * g (g1⁻¹ * p.1 * g1, g1⁻¹ * p.2)

/--
D(G) unit element.
The unit is 1 on all (a, e) and 0 on (a, g) for g ≠ e.
This represents Σ_a (δ_a ⊗ e), the sum of all basis elements with group component e.
-/
def ddAlgOne : DDAlg k G :=
  fun p => if p.2 = 1 then 1 else 0

/-! ## 3. Algebra Properties -/

/--
Left unit law: ddAlgOne * f = f for all f in D(G).

PROVIDED SOLUTION
Unfold ddAlgMul and ddAlgOne. The sum over g1 has ddAlgOne(a, g1) = if g1 = 1 then 1 else 0.
So only g1 = 1 contributes: 1 * f(1⁻¹ * a * 1, 1⁻¹ * h) = f(a, h).
Use ext p, simp [ddAlgMul, ddAlgOne], then simplify the Finset.sum using
Finset.sum_ite_eq' or Finset.sum_eq_single. The key identity is 1⁻¹ * a * 1 = a.
-/
theorem ddAlgMul_one_left (f : DDAlg k G) :
    ddAlgMul k G (ddAlgOne k G) f = f := by
  ext ⟨x, y⟩; unfold ddAlgMul ddAlgOne
  rw [Finset.sum_eq_single 1] <;> aesop

/--
Right unit law: f * ddAlgOne = f for all f in D(G).

PROVIDED SOLUTION
Unfold ddAlgMul and ddAlgOne. In the sum over g1, ddAlgOne(g1⁻¹*a*g1, g1⁻¹*h)
requires g1⁻¹ * h = 1, i.e., g1 = h. So only g1 = h contributes:
f(a, h) * 1 = f(a, h). Use ext p, simp [ddAlgMul, ddAlgOne], then
Finset.sum_eq_single or Finset.sum_ite_eq'. Key: g1⁻¹ * h = 1 ↔ g1 = h.
-/
theorem ddAlgMul_one_right (f : DDAlg k G) :
    ddAlgMul k G f (ddAlgOne k G) = f := by
  ext ⟨a, h⟩; simp [ddAlgMul, ddAlgOne]
  simp +decide [inv_mul_eq_one]

/--
Associativity: (f * g) * h = f * (g * h) in D(G).

PROVIDED SOLUTION
Both sides expand to a double sum over G × G. The left side is
Σ_{g1} (Σ_{g2} f(a, g2) * g(g2⁻¹*a*g2, g2⁻¹*g1)) * h(g1⁻¹*a*g1, g1⁻¹*p.2).
The right side is Σ_{g1} f(a, g1) * (Σ_{g2} g(g1⁻¹*a*g1, g2) * h(...)).
Reindex using g1' = g2, g2' = g2⁻¹ * g1, or use Finset.sum_comm to
interchange the order of summation and mul_assoc for the ring.
-/
theorem ddAlgMul_assoc (f g h : DDAlg k G) :
    ddAlgMul k G (ddAlgMul k G f g) h = ddAlgMul k G f (ddAlgMul k G g h) := by
  ext ⟨a, h⟩; simp [ddAlgMul]
  simp +decide only [Finset.sum_mul _ _ _, mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_bij (fun y _ => x⁻¹ * y) ?_ ?_ ?_ ?_ <;> simp +decide [mul_assoc]
  exact fun b => ⟨x * b, by simp +decide⟩

/-! ## 4. Basis Multiplication Verification -/

/--
Basis element multiplication matches the standard Drinfeld double formula:
  (δ_a ⊗ g1) * (δ_b ⊗ g2) = δ_{a, g1*b*g1⁻¹} * (δ_a ⊗ g1*g2)

This verifies that our convolution definition agrees with DrinfeldDouble.lean's
ddMul on basis elements.

PROVIDED SOLUTION
Unfold ddAlgMul, ddBasis. The sum over g1' has ddBasis(a, g1)(p.1, g1') which
is nonzero only when p.1 = a and g1' = g1. Then ddBasis(b, g2)(g1⁻¹*a*g1, g1⁻¹*p.2)
requires g1⁻¹*a*g1 = b and g1⁻¹*p.2 = g2, i.e., a = g1*b*g1⁻¹ and p.2 = g1*g2.
So the result is ddBasis(a, g1*g2) when a = g1*b*g1⁻¹, else 0.
Use ext, simp [ddAlgMul, ddBasis], split_ifs, and group.
-/
theorem ddBasis_mul (a b g1 g2 : G) :
    ddAlgMul k G (ddBasis k G a g1) (ddBasis k G b g2) =
    if a = g1 * b * g1⁻¹ then ddBasis k G a (g1 * g2) else 0 := by
  unfold ddAlgMul ddBasis;
  split_ifs <;> ext p;
  · rw [ Finset.sum_eq_single g1 ] <;> simp +contextual [ *, mul_assoc ];
    split_ifs <;> simp_all +decide [ mul_assoc, inv_mul_eq_iff_eq_mul ];
  · rw [ Finset.sum_eq_zero ] ; aesop;
    intro x _; split_ifs <;> simp_all +decide [ mul_assoc, eq_inv_mul_iff_mul_eq ] ;
    simp_all +decide [ mul_assoc, inv_mul_eq_iff_eq_mul ];
    simp_all +decide [ ← mul_assoc, eq_mul_inv_of_mul_eq ‹a * g1 = g1 * b ∧ p.2 = g1 * g2›.1 ]

/--
The unit in basis form: ddAlgOne(a, g) = if g = 1 then 1 else 0.
-/
theorem ddAlgOne_eq : ddAlgOne k G = fun p => if p.2 = 1 then 1 else 0 := rfl

/-! ## 5. D(G) Dimension -/

/--
D(G) has dimension |G|² as a k-module.
The basis elements δ_a ⊗ g are indexed by (a, g) in G × G.
-/
theorem ddAlg_dim : Fintype.card (G × G) = Fintype.card G ^ 2 := by
  rw [Fintype.card_prod]; ring

end SKEFTHawking

/-! ## 6. Abelian Specialization -/

-- Separate namespace section with CommGroup to avoid Group/CommGroup typeclass diamond.
-- This pattern was established for VecGMonoidal (Aristotle run 48493889).

namespace SKEFTHawking

variable (G : Type u) [CommGroup G] [Fintype G] [DecidableEq G]

/--
For abelian G, conjugation is trivial: g1 * b * g1⁻¹ = b.
This means the basis multiplication simplifies to:
  (δ_a ⊗ g1) * (δ_b ⊗ g2) = δ_{a,b} * (δ_a ⊗ g1*g2)
and D(G) becomes commutative.
-/
theorem ddBasis_mul_abelian (b g1 : G) : g1 * b * g1⁻¹ = b := by
  simp [mul_comm, mul_assoc]

/--
For abelian G, the conjugation condition reduces to equality:
a = g1 * a2 * g1⁻¹ if and only if a = a2.

This means the simple modules of D(G) are indexed by G × G-hat (character group),
matching our CenterEquivalenceZ2 result for G = Z/2.

PROVIDED SOLUTION
Forward: substitute g1 * a2 * g1⁻¹ = a2 (from ddBasis_mul_abelian) into h.
Backward: substitute a1 = a2 then apply ddBasis_mul_abelian.
-/
theorem abelian_dd_conjugation (a1 a2 g1 : G) :
    (a1 = g1 * a2 * g1⁻¹) ↔ (a1 = a2) := by
  simp +decide [mul_assoc, mul_comm g1]

/-! ## 7. Module Summary -/

/--
DrinfeldDoubleAlgebra module summary:
  - D(G) represented as G × G → k (coefficient functions in basis δ_a ⊗ g)
  - Twisted multiplication via convolution with conjugation action
  - Unit laws, associativity, basis multiplication stated with PROVIDED SOLUTIONs
  - Abelian specialization: conjugation trivial, D(G) commutative
  - Connects to CenterEquivalenceZ2 (concrete Z/2 case)
  - All proofs filled by Aristotle (run 878b181f): unit laws, associativity, basis mul
-/
theorem dd_algebra_summary :
    (1 : G) * (1 : G) = 1 := mul_one 1

end SKEFTHawking
