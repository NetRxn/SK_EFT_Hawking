/-
Phase 5q.B: kernel-pure even-unimodular E₈ (native_decide-free), via inverse exhibition.

Mathlib's `CartanMatrix.E₈` is defined *recursively* (built from E₆/E₇ via nested lambdas), so
kernel evaluation of its entries — and hence any kernel-pure `det`/`decide` proof about it — deep-
recurses and blows up. That is why `E8Lattice.lean` proves E₈'s det/even/symmetric facts with
`native_decide` (which the project is eliminating).

This module sidesteps the recursion by working with an explicit *literal* matrix `E8lit` (the E₈
Cartan matrix written out; its entries were extracted from `CartanMatrix.E₈` and match it), and proves
even-unimodularity **kernel-pure** with a cheap trick: rather than evaluate the 8×8 determinant (the
40320-term Leibniz sum is infeasible in the kernel), we exhibit the explicit integer inverse `E8inv`
(the adjugate, an integer matrix because `det = 1`) and check `E8lit * E8inv = 1` by `decide` — only
512 small integer multiplications. `E8lit * E8inv = 1` gives `IsUnit (det E8lit)`, hence `det = ±1`
(unimodular); evenness and symmetry are direct `decide` on the literal.

This is a reusable, native_decide-free even-unimodular rank-8 lattice — the hardest concrete
prerequisite for the classification route to van der Blij's `8 ∣ σ` (`E₈^a ⊕ (-E₈)^b ⊕ H^c`), and a
credible step in the discharge plan for the leg. All proofs are kernel-pure
(`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no `maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin

namespace SKEFTHawking

open Matrix

/-- The E₈ Cartan matrix as an explicit literal `Matrix (Fin 8) (Fin 8) ℤ` (entries extracted from
and matching `CartanMatrix.E₈`). Working with the literal avoids the deep recursion of Mathlib's
recursive E₈ definition, keeping kernel `decide` cheap. -/
def E8lit : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0, 0;
     0, 2, 0, -1, 0, 0, 0, 0;
     -1, 0, 2, -1, 0, 0, 0, 0;
     0, -1, -1, 2, -1, 0, 0, 0;
     0, 0, 0, -1, 2, -1, 0, 0;
     0, 0, 0, 0, -1, 2, -1, 0;
     0, 0, 0, 0, 0, -1, 2, -1;
     0, 0, 0, 0, 0, 0, -1, 2]

/-- The explicit integer inverse of `E8lit` (its adjugate; integer because `det E8lit = 1`). -/
def E8inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
     5, 8, 10, 15, 12, 9, 6, 3;
     7, 10, 14, 20, 16, 12, 8, 4;
     10, 15, 20, 30, 24, 18, 12, 6;
     8, 12, 16, 24, 20, 15, 10, 5;
     6, 9, 12, 18, 15, 12, 8, 4;
     4, 6, 8, 12, 10, 8, 6, 3;
     2, 3, 4, 6, 5, 4, 3, 2]

/-- **The inverse-exhibition identity** `E8lit · E8inv = 1` — proven by `decide` (512 small integer
multiplications), the cheap kernel-pure replacement for the 8×8 determinant computation. -/
theorem e8lit_mul_inv : E8lit * E8inv = 1 := by decide

/-- E₈ is symmetric (kernel-pure `decide` on the literal). -/
theorem e8lit_symm : E8lit.transpose = E8lit := by decide

/-- E₈ has even diagonal (kernel-pure `decide` on the literal). -/
theorem e8lit_even : ∀ i, 2 ∣ E8lit i i := by decide

/-- **E₈ is unimodular** (`det = ±1`), kernel-pure: from `E8lit · E8inv = 1` the determinant is a
unit in `ℤ`, hence `±1`. No determinant evaluation needed. -/
theorem e8lit_unimodular : IsUnimodular E8lit := by
  have hdet : E8lit.det * E8inv.det = 1 := by
    rw [← Matrix.det_mul, e8lit_mul_inv, Matrix.det_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl h1
  · exact Or.inr h1

/-- **E₈ is even unimodular**, kernel-pure (native_decide-free). The reusable even-unimodular rank-8
lattice for the classification route to van der Blij's `8 ∣ σ`. -/
theorem e8lit_even_unimodular : IsEvenUnimodular E8lit :=
  ⟨e8lit_symm, e8lit_unimodular, e8lit_even⟩

end SKEFTHawking
