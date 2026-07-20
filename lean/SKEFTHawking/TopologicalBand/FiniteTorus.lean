import Mathlib

/-!
# D11-FHS Q1 — finite periodic grid (torus) with two commuting shifts

The concrete rectangular torus `ZMod N₁ × ZMod N₂` (`NeZero` in each factor) carries the
finite periodic grid the FHS lattice-Chern construction lives on. This file is purely
finite/data-level: two commuting unit shifts and the shift-invariance of finite sums that
drives the torus telescoping.
-/

open scoped BigOperators

namespace SKEFTHawking.TopologicalBand

variable (N₁ N₂ : ℕ)

/-- The concrete rectangular torus: a finite periodic 2D grid. -/
abbrev Torus : Type := ZMod N₁ × ZMod N₂

/-- The two unit lattice vectors `ê₀ = (1,0)` and `ê₁ = (0,1)`. -/
def shiftVec : Fin 2 → Torus N₁ N₂
  | 0 => (1, 0)
  | 1 => (0, 1)

/-- The unit shift in direction `μ` as a permutation of the finite grid. -/
def shift (μ : Fin 2) : Torus N₁ N₂ ≃ Torus N₁ N₂ := Equiv.addRight (shiftVec N₁ N₂ μ)

@[simp] lemma shift_apply (μ : Fin 2) (k : Torus N₁ N₂) :
    shift N₁ N₂ μ k = k + shiftVec N₁ N₂ μ := rfl

/-- The two shifts commute (the grid is a 2-torus). -/
theorem shift_comm (μ ν : Fin 2) (k : Torus N₁ N₂) :
    shift N₁ N₂ μ (shift N₁ N₂ ν k) = shift N₁ N₂ ν (shift N₁ N₂ μ k) := by
  simp only [shift_apply]
  rw [add_right_comm]

variable [NeZero N₁] [NeZero N₂]

/-- **Shift invariance of finite sums.** Summing a grid function over all vertices is invariant
under a unit shift — the reindexing bijection is the shift permutation. This is the engine of
the torus telescoping: forward differences sum to zero. -/
theorem sum_shift (μ : Fin 2) (f : Torus N₁ N₂ → ℝ) :
    ∑ k, f (shift N₁ N₂ μ k) = ∑ k, f k :=
  Equiv.sum_comp (shift N₁ N₂ μ) f

/-- **Forward differences sum to zero.** For any grid function `f`, the sum over the torus of the
forward difference `f(k + êμ) − f(k)` vanishes. -/
theorem sum_forwardDiff_eq_zero (μ : Fin 2) (f : Torus N₁ N₂ → ℝ) :
    ∑ k, (f (shift N₁ N₂ μ k) - f k) = 0 := by
  rw [Finset.sum_sub_distrib, sum_shift, sub_self]

end SKEFTHawking.TopologicalBand
