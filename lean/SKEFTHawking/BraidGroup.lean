/-
SK_EFT_Hawking Phase 6p Wave 2a.2: The Artin Braid Group B_n

Standard algebraic braid group `BraidGroup n` for n ≥ 1, defined via
`PresentedGroup` with the Artin presentation:
  - generators: σ_i for i = 0, ..., n-2 (i.e., `Fin (n-1)` worth)
  - braid relation:  σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}  (for i, i+1 valid)
  - commutation:     σ_i σ_j = σ_j σ_i                       (for |i - j| ≥ 2)

This is consumed by Wave 2a.3 BridgeProp (the FKLW density predicate ranges
over `BraidGroup n` representations), Wave 2b.3 FibonacciQuintetUniversality
(extending the existing `FibonacciQutritUniversality.lean` qutrit case to
4-strand quintet), and Wave 3a.2 GateCompilation (Hadamard / CNOT / T-gate
braid-word compilation in Q(ζ₄₀)).

Per Wave 2a.1 DR §6 (gate G9): use `PresentedGroup` Artin presentation, ~50
lines, in-tree. Mathlib4 lacks `BraidGroup`; Hannah Fechtner's Dec 2024 "Braids
in Lean" is not merged. Template = `Mathlib/GroupTheory/Coxeter/Basic.lean`.

Relation to existing libraries:
  - Mathlib4: only categorical braiding present (`Mathlib/CategoryTheory/Monoidal/Braided*`);
    the algebraic `BraidGroup n` with σᵢ generators + Yang-Baxter is absent.
  - Fechtner Dec 2024: unmerged; not vendored here.

Primary source: Artin, *Abh. Math. Sem. Hamburg Univ.* 4, 47–72 (1925).
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking

/-! ## 1. Generators and relations of the Artin braid group

For `n : ℕ`, we use generators indexed by `Fin (n - 1)` (Lean's saturating
subtraction at `n = 0` and `n = 1` gives `Fin 0`, the empty type — so
`BraidGroup 0 ≃ BraidGroup 1 ≃ trivial group`).
-/

/-- The braid generator σᵢ as an element of `FreeGroup (Fin (n - 1))`. -/
def braidGen (n : ℕ) (i : Fin (n - 1)) : FreeGroup (Fin (n - 1)) := FreeGroup.of i

/-- The braid relation as an element of `FreeGroup (Fin (n - 1))`:

    σ_i σ_{i+1} σ_i (σ_{i+1} σ_i σ_{i+1})⁻¹

This element is 1 in the quotient iff `σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}`. -/
def braidRelation (n : ℕ) (i j : Fin (n - 1))
    (_h_adj : j.val = i.val + 1) :
    FreeGroup (Fin (n - 1)) :=
  let σi := FreeGroup.of i
  let σj := FreeGroup.of j
  (σi * σj * σi) * (σj * σi * σj)⁻¹

/-- The commutation relation σ_i σ_j (σ_j σ_i)⁻¹ as an element of `FreeGroup (Fin (n - 1))`.
    Together with the gating condition `|i - j| ≥ 2`, this gives the standard commutation. -/
def commutationRelation (n : ℕ) (i j : Fin (n - 1))
    (_h_far : 2 ≤ (Int.natAbs (i.val - j.val : Int))) :
    FreeGroup (Fin (n - 1)) :=
  let σi := FreeGroup.of i
  let σj := FreeGroup.of j
  (σi * σj) * (σj * σi)⁻¹

/-! ## 2. The set of all relations -/

/-- The set of Artin relations: all braid relations (adjacent generators) and
    all commutation relations (far-apart generators). -/
def artinRelations (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  { r | ∃ (i j : Fin (n - 1)) (h : j.val = i.val + 1),
        r = braidRelation n i j h } ∪
  { r | ∃ (i j : Fin (n - 1)) (h : 2 ≤ (Int.natAbs (i.val - j.val : Int))),
        r = commutationRelation n i j h }

/-! ## 3. The Artin braid group -/

/-- The Artin braid group on `n` strands: presented group with `n - 1`
    generators and the Artin relations (braid + commutation). -/
def BraidGroup (n : ℕ) : Type :=
  PresentedGroup (artinRelations n)

namespace BraidGroup

variable {n : ℕ}

/-- `BraidGroup n` is a group (inherited from `PresentedGroup`). -/
instance (n : ℕ) : Group (BraidGroup n) :=
  inferInstanceAs (Group (PresentedGroup _))

/-- The standard generator σᵢ as an element of `BraidGroup n`. -/
def σ (i : Fin (n - 1)) : BraidGroup n :=
  PresentedGroup.of i

/-! ## 4. Module summary

BraidGroup.lean: the Artin braid group `B_n` via `PresentedGroup`.

  - `braidGen n i : FreeGroup (Fin (n-1))` — generator helper.
  - `braidRelation n i j h_adj` — the σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1} relator.
  - `commutationRelation n i j h_far` — the σ_i σ_j = σ_j σ_i relator (|i-j| ≥ 2).
  - `artinRelations n` — the union of all braid + commutation relators.
  - `BraidGroup n := PresentedGroup (artinRelations n)`.
  - `BraidGroup n` has `Group` instance.
  - `BraidGroup.σ i : BraidGroup n` — the i-th standard generator.

Consumed by Wave 2a.3 BridgeProp, Wave 2b.3 FibonacciQuintetUniversality,
Wave 3a.2 GateCompilation.

Zero sorry. Zero axioms.
-/

end BraidGroup

end SKEFTHawking
