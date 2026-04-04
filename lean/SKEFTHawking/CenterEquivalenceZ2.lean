/-
Phase 5b Wave 2: Concrete Z(Vec_{ℤ/2}) ↔ D(ℤ/2) Correspondence

Explicit verification that the 4 toric code anyons (from ToricCodeCenter.lean)
correspond exactly to the 4 simple D(ℤ/2)-modules (from DrinfeldDouble.lean).

This is the concrete version of the abstract equivalence Z(Vec_G) ≅ Rep(D(G)),
verified for G = ℤ/2. For each anyon we show:
  1. The grading (flux sector) matches the conjugacy class label
  2. The character (charge) matches the irrep of the centralizer
  3. Fusion is preserved under the correspondence
  4. Braiding phases match

References:
  Kitaev, Ann. Phys. 303, 2 (2003) — toric code
  Dijkgraaf-Pasquier-Roche (1991) — D(G) anyon classification
  Our ToricCodeCenter.lean — anyon data
  Our DrinfeldDouble.lean — D(G) structure
-/

import Mathlib
import SKEFTHawking.ToricCodeCenter
import SKEFTHawking.DrinfeldDouble

open Finset

namespace SKEFTHawking

/-! ## 1. D(ℤ/2) Simple Module Classification -/

/--
D(ℤ/2) simples are labeled by pairs (conjugacy class, irrep of centralizer).
Since ℤ/2 is abelian: conjugacy classes = elements, centralizer = ℤ/2.
So simples = ℤ/2 × ℤ̂/2 = {(0,+), (0,-), (1,+), (1,-)} = 4 simples.
-/
inductive DZ2Simple : Type where
  | trivTriv   -- (0, +1): trivial class, trivial irrep
  | trivSign   -- (0, -1): trivial class, sign irrep
  | flipTriv   -- (1, +1): nontrivial class, trivial irrep
  | flipSign   -- (1, -1): nontrivial class, sign irrep
  deriving DecidableEq, Fintype

theorem dz2_simple_count : Fintype.card DZ2Simple = 4 := by decide

/-! ## 2. The Correspondence Map -/

/--
The bijection between toric code anyons and D(ℤ/2) simples.
  vacuum (1)  ↔ (0, +1) trivTriv
  electric (e) ↔ (0, -1) trivSign
  magnetic (m) ↔ (1, +1) flipTriv
  fermion (ε) ↔ (1, -1) flipSign
-/
def toricToDZ2 : ToricAnyon → DZ2Simple
  | .vacuum => .trivTriv
  | .electric => .trivSign
  | .magnetic => .flipTriv
  | .fermion => .flipSign

def dz2ToToric : DZ2Simple → ToricAnyon
  | .trivTriv => .vacuum
  | .trivSign => .electric
  | .flipTriv => .magnetic
  | .flipSign => .fermion

/--
The correspondence is a bijection (left inverse).
-/
theorem left_inverse : ∀ a : ToricAnyon, dz2ToToric (toricToDZ2 a) = a := by
  intro a; cases a <;> rfl

/--
Right inverse.
-/
theorem right_inverse : ∀ s : DZ2Simple, toricToDZ2 (dz2ToToric s) = s := by
  intro s; cases s <;> rfl

/--
The correspondence is an equivalence of types.
-/
def toricDZ2Equiv : ToricAnyon ≃ DZ2Simple where
  toFun := toricToDZ2
  invFun := dz2ToToric
  left_inv := left_inverse
  right_inv := right_inverse

/-! ## 3. Grading Preservation -/

/--
The ℤ/2 grading of D(ℤ/2) simples (conjugacy class label).
-/
def dz2Grading : DZ2Simple → ZMod 2
  | .trivTriv => 0
  | .trivSign => 0
  | .flipTriv => 1
  | .flipSign => 1

/--
The correspondence preserves the grading:
toricGrading(a) = dz2Grading(toricToDZ2(a)).
-/
theorem grading_preserved (a : ToricAnyon) :
    toricGrading a = dz2Grading (toricToDZ2 a) := by
  cases a <;> rfl

/-! ## 4. Character Preservation -/

/--
The ℤ̂/2 character of D(ℤ/2) simples (irrep label: +1 or -1).
-/
def dz2Character : DZ2Simple → ℤ
  | .trivTriv => 1
  | .trivSign => -1
  | .flipTriv => 1
  | .flipSign => -1

/--
The correspondence preserves the character:
toricCharacter(a) = dz2Character(toricToDZ2(a)).
-/
theorem character_preserved (a : ToricAnyon) :
    toricCharacter a = dz2Character (toricToDZ2 a) := by
  cases a <;> rfl

/-! ## 5. Fusion Preservation -/

/--
Fusion on D(ℤ/2) simples: (g₁,χ₁) ⊗ (g₂,χ₂) = (g₁+g₂, χ₁·χ₂).
-/
def dz2Fusion : DZ2Simple → DZ2Simple → DZ2Simple
  | .trivTriv, b => b
  | a, .trivTriv => a
  | .trivSign, .trivSign => .trivTriv
  | .trivSign, .flipTriv => .flipSign
  | .trivSign, .flipSign => .flipTriv
  | .flipTriv, .trivSign => .flipSign
  | .flipTriv, .flipTriv => .trivTriv
  | .flipTriv, .flipSign => .trivSign
  | .flipSign, .trivSign => .flipTriv
  | .flipSign, .flipTriv => .trivSign
  | .flipSign, .flipSign => .trivTriv

/--
The correspondence preserves fusion:
toricToDZ2(a ⊗ b) = toricToDZ2(a) ⊗_{D} toricToDZ2(b).
-/
theorem fusion_preserved (a b : ToricAnyon) :
    toricToDZ2 (toricFusion a b) = dz2Fusion (toricToDZ2 a) (toricToDZ2 b) := by
  cases a <;> cases b <;> rfl

/--
And the inverse also preserves fusion.
-/
theorem fusion_preserved_inverse (s t : DZ2Simple) :
    dz2ToToric (dz2Fusion s t) = toricFusion (dz2ToToric s) (dz2ToToric t) := by
  cases s <;> cases t <;> rfl

/-! ## 6. Braiding Phase Preservation -/

/--
Braiding phase on D(ℤ/2) simples: R((g₁,χ₁), (g₂,χ₂)) = χ₁(g₂).
-/
def dz2BraidingPhase (s t : DZ2Simple) : ℤ :=
  match dz2Grading t with
  | 0 => 1
  | _ => dz2Character s

/--
The correspondence preserves braiding phases.
-/
theorem braiding_preserved (a b : ToricAnyon) :
    braidingPhase a b = dz2BraidingPhase (toricToDZ2 a) (toricToDZ2 b) := by
  cases a <;> cases b <;> simp [braidingPhase, dz2BraidingPhase, toricToDZ2,
    toricGrading, toricCharacter, dz2Grading, dz2Character]

/--
In particular, the toric code signature R(e,m) = -1 is preserved.
-/
theorem signature_preserved :
    braidingPhase .electric .magnetic =
    dz2BraidingPhase (toricToDZ2 .electric) (toricToDZ2 .magnetic) := by
  rfl

/-! ## 7. Summary: Full Monoidal Correspondence -/

/--
The complete correspondence: toricToDZ2 is a bijection that preserves
grading, character, fusion, and braiding. This is the concrete verification
of Z(Vec_{ℤ/2}) ≅ Rep(D(ℤ/2)) for G = ℤ/2.
-/
theorem full_correspondence :
    -- Bijection
    (∀ a : ToricAnyon, dz2ToToric (toricToDZ2 a) = a) ∧
    (∀ s : DZ2Simple, toricToDZ2 (dz2ToToric s) = s) ∧
    -- Grading preserved
    (∀ a : ToricAnyon, toricGrading a = dz2Grading (toricToDZ2 a)) ∧
    -- Character preserved
    (∀ a : ToricAnyon, toricCharacter a = dz2Character (toricToDZ2 a)) ∧
    -- Fusion preserved
    (∀ a b : ToricAnyon, toricToDZ2 (toricFusion a b) = dz2Fusion (toricToDZ2 a) (toricToDZ2 b)) ∧
    -- Braiding preserved
    (∀ a b : ToricAnyon, braidingPhase a b = dz2BraidingPhase (toricToDZ2 a) (toricToDZ2 b)) :=
  ⟨left_inverse, right_inverse, grading_preserved, character_preserved,
   fusion_preserved, braiding_preserved⟩

end SKEFTHawking
