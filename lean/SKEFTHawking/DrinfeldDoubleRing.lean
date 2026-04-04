/-
Phase 5b Wave 3: D(G) as a Mathlib Ring and k-Algebra

Wraps the Drinfeld double D(G) = k^G ⊗ k[G] into Mathlib's Ring and Algebra
typeclasses. The underlying algebra laws (unit, associativity) were proved in
DrinfeldDoubleAlgebra.lean (Aristotle run 878b181f). This file adds:
  - Newtype wrapper DG to avoid conflict with Pi.instMul (pointwise)
  - Distributivity proofs (left_distrib, right_distrib, zero_mul, mul_zero)
  - Ring (DG k G) instance
  - Algebra k (DG k G) instance

The wrapper is necessary because DDAlg = G × G → k inherits pointwise
multiplication from Pi, but D(G) has TWISTED convolution multiplication.

References:
  DrinfeldDoubleAlgebra.lean — algebra laws on DDAlg (Aristotle 878b181f)
  Kassel, "Quantum Groups" (Springer, 1995), Ch. IX
-/

import Mathlib
import SKEFTHawking.DrinfeldDoubleAlgebra

open Finset

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k] (G : Type u) [Group G] [Fintype G] [DecidableEq G]

/-! ## 1. Newtype wrapper for D(G) -/

/--
The Drinfeld double D(G) as a type with Ring structure.
Wraps `G × G → k` to give twisted convolution as the Mul instance,
avoiding conflict with Pi's pointwise multiplication.
-/
@[ext]
structure DG where
  /-- Coefficient function: c(a, g) is the component along basis element δ_a ⊗ g -/
  coeff : G × G → k

/-- The basis element δ_a ⊗ g in DG. -/
def DG.basis (a g : G) : DG k G := ⟨ddBasis k G a g⟩

omit [CommRing k] [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem DG.coeff_mk (f : G × G → k) : (DG.mk f).coeff = f := rfl
omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem DG.coeff_add (a b : DG k G) (p : G × G) :
    (⟨a.coeff + b.coeff⟩ : DG k G).coeff p = a.coeff p + b.coeff p := rfl
omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem DG.coeff_zero (p : G × G) : (⟨(0 : G × G → k)⟩ : DG k G).coeff p = 0 := rfl

/-! ## 2. Additive commutative group structure (pointwise through coeff) -/

/--
DG k G is an additive commutative group with pointwise operations.
All axioms reduce to the corresponding axioms on G × G → k (Pi type).
-/
instance DG.instAddCommGroup : AddCommGroup (DG k G) where
  add a b := ⟨a.coeff + b.coeff⟩
  zero := ⟨0⟩
  neg a := ⟨-a.coeff⟩
  sub a b := ⟨a.coeff - b.coeff⟩
  nsmul n a := ⟨n • a.coeff⟩
  zsmul n a := ⟨n • a.coeff⟩
  add_assoc a b c := by ext p; exact add_assoc (a.coeff p) (b.coeff p) (c.coeff p)
  zero_add a := by ext p; exact zero_add (a.coeff p)
  add_zero a := by ext p; exact add_zero (a.coeff p)
  add_comm a b := by ext p; exact add_comm (a.coeff p) (b.coeff p)
  neg_add_cancel a := by ext p; exact neg_add_cancel (a.coeff p)
  sub_eq_add_neg a b := by ext p; exact sub_eq_add_neg (a.coeff p) (b.coeff p)
  nsmul_zero a := by ext p; exact zero_smul ℕ (a.coeff p)
  nsmul_succ n a := by ext p; exact succ_nsmul (a.coeff p) n
  zsmul_zero' a := by ext p; exact zero_smul ℤ (a.coeff p)
  zsmul_succ' n a := by
    show (⟨(Int.ofNat n + 1) • a.coeff⟩ : DG k G) = ⟨(Int.ofNat n) • a.coeff + a.coeff⟩
    ext p; simp [add_smul, add_comm]
  zsmul_neg' n a := by ext p; simp; ring

/-! ## 3. Ring structure (twisted convolution) -/

/--
D(G) is a Ring with twisted convolution multiplication.
-/
instance DG.instRing : Ring (DG k G) where
  mul a b := ⟨ddAlgMul k G a.coeff b.coeff⟩
  one := ⟨ddAlgOne k G⟩
  mul_assoc a b c := by ext p; exact congr_fun (ddAlgMul_assoc k G a.coeff b.coeff c.coeff) p
  one_mul a := by ext p; exact congr_fun (ddAlgMul_one_left k G a.coeff) p
  mul_one a := by ext p; exact congr_fun (ddAlgMul_one_right k G a.coeff) p
  left_distrib a b c := by
    ext ⟨x, h⟩
    show ddAlgMul k G a.coeff (b.coeff + c.coeff) (x, h) =
      (ddAlgMul k G a.coeff b.coeff + ddAlgMul k G a.coeff c.coeff) (x, h)
    simp [ddAlgMul, mul_add, Finset.sum_add_distrib]
  right_distrib a b c := by
    ext ⟨x, h⟩
    show ddAlgMul k G (a.coeff + b.coeff) c.coeff (x, h) =
      (ddAlgMul k G a.coeff c.coeff + ddAlgMul k G b.coeff c.coeff) (x, h)
    simp [ddAlgMul, add_mul, Finset.sum_add_distrib]
  zero_mul a := by
    ext ⟨x, h⟩
    show ddAlgMul k G 0 a.coeff (x, h) = (0 : G × G → k) (x, h)
    simp [ddAlgMul]
  mul_zero a := by
    ext ⟨x, h⟩
    show ddAlgMul k G a.coeff 0 (x, h) = (0 : G × G → k) (x, h)
    simp [ddAlgMul]

/-! ## 4. k-Algebra structure -/

private def algMapFun (r : k) : DG k G := ⟨fun p => if p.2 = 1 then r else 0⟩

/--
D(G) is a k-Algebra. The algebra map sends r to r·1_{D(G)}.
-/
instance DG.instAlgebra : Algebra k (DG k G) where
  smul r a := ⟨r • a.coeff⟩
  algebraMap := {
    toFun := algMapFun k G
    map_one' := by ext ⟨a, g⟩; change _ = ddAlgOne k G (a, g); simp [algMapFun, ddAlgOne]
    map_mul' := fun r s => by
      ext ⟨a, h⟩
      show (algMapFun k G (r * s)).coeff (a, h) =
        ddAlgMul k G (algMapFun k G r).coeff (algMapFun k G s).coeff (a, h)
      simp only [algMapFun, ddAlgMul]
      rw [Finset.sum_eq_single 1]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    map_zero' := by ext ⟨a, g⟩; change _ = (0 : G × G → k) (a, g); simp [algMapFun]
    map_add' := fun r s => by
      ext ⟨a, g⟩
      show (algMapFun k G (r + s)).coeff (a, g) =
        ((algMapFun k G r).coeff + (algMapFun k G s).coeff) (a, g)
      simp [algMapFun]; split_ifs <;> ring
  }
  commutes' r x := by
    ext ⟨a, h⟩
    show ddAlgMul k G (algMapFun k G r).coeff x.coeff (a, h) =
      ddAlgMul k G x.coeff (algMapFun k G r).coeff (a, h)
    simp only [algMapFun, ddAlgMul]
    rw [Finset.sum_eq_single 1]
    · simp
      rw [Finset.sum_eq_single h]
      · simp [mul_comm]
      · intro b _ hb; simp [inv_mul_eq_one, hb]
      · simp
    · intro b _ hb; simp [hb]
    · simp
  smul_def' r x := by
    ext ⟨a, h⟩
    show r * x.coeff (a, h) =
      ddAlgMul k G (algMapFun k G r).coeff x.coeff (a, h)
    simp only [algMapFun, ddAlgMul]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b _ hb; simp [hb]
    · simp

/-! ## 5. Key structural theorems -/

/--
D(G) has dimension |G|² as a k-module.
-/
theorem DG.dim_eq_card_sq : Fintype.card (G × G) = Fintype.card G ^ 2 :=
  ddAlg_dim G

/-
Basis multiplication in DG matches the Drinfeld double formula:
  (δ_a ⊗ g1) · (δ_b ⊗ g2) = δ_{a, g1·b·g1⁻¹} · (δ_a ⊗ g1·g2)
-/
theorem DG.basis_mul (a b g1 g2 : G) :
    DG.basis k G a g1 * DG.basis k G b g2 =
    if a = g1 * b * g1⁻¹ then DG.basis k G a (g1 * g2) else 0 := by
  ext ⟨x, h⟩;
  convert congr_arg ( fun f : G × G → k => f ( x, h ) ) ( ddBasis_mul k G a b g1 g2 ) using 1;
  split_ifs <;> rfl

/-! ## 6. Module Summary -/

/--
DrinfeldDoubleRing module: D(G) is a Ring and k-Algebra.
  - Newtype DG wrapping G × G → k (avoids Pi.instMul conflict)
  - Additive: pointwise (AddCommGroup)
  - Multiplicative: twisted convolution (ddAlgMul)
  - Ring: unit laws (Aristotle 878b181f) + distrib + zero_mul/mul_zero
  - Algebra k: scalar embedding r ↦ (a,g) ↦ if g=e then r else 0
  - Basis multiplication matches DrinfeldDouble.ddMul
-/
theorem DG.ring_algebra_summary : True := trivial

end SKEFTHawking