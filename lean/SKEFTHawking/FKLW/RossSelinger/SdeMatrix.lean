/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — computable matrix `sde` + spec bridge

Lifts the per-element denominator-exponent machinery (`ZOmegaSqrt2.denExp`,
`denExp_le_iff` from `Sde.lean`) to the matrix level, giving a
**computable** smallest-denominator-exponent `sdeC : Mat2 → ℕ` and
proving it agrees with the noncomputable KMM spec `KMM.sde` (defined via
`Nat.find` on `KMM.sde_le`).

## Headline results

  * `KMM.sdeC M` — `Finset.sup` of the per-entry `denExp` over the 2×2
    matrix; computable.
  * `KMM.sde_le_sdeC` — **achievability**: `√2^(sdeC M) · M` is
    `ZOmega`-valued (`sde_le M (sdeC M)`), so every matrix has finite sde.
  * `KMM.sdeC_le_of_sde_le` — **minimality**: any clearing exponent `k`
    (`sde_le M k`) bounds `sdeC M`.
  * `KMM.sde_eq_sdeC` — `KMM.sde M = sdeC M`: the noncomputable spec
    coincides with the computable definition.

The achievability + minimality pair is exactly what makes `sdeC` the
*least* clearing exponent — the quantity `kmmReduce` recurses on
(`termination_by sde`) and the length bound `n_g ≤ N₃ + 4·sde` is stated
against.

## References

  * Pre-Implementation Research Dossier §3 (sde structure).
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §3, Corollary 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.KMM
import SKEFTHawking.FKLW.RossSelinger.Sde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open ZOmegaSqrt2

/-- **Computable smallest denominator exponent** of a `Mat2`: the `sup`
over the four entries of their per-element `denExp`. -/
def sdeC (M : Mat2) : ℕ :=
  Finset.univ.sup fun i : Fin 2 => Finset.univ.sup fun j : Fin 2 => denExp (M i j)

/-- **Every entry's `denExp` is `≤ sdeC`**. -/
theorem denExp_le_sdeC (M : Mat2) (i j : Fin 2) : denExp (M i j) ≤ sdeC M := by
  refine le_trans
    (Finset.le_sup (f := fun j : Fin 2 => denExp (M i j)) (Finset.mem_univ j)) ?_
  exact Finset.le_sup
    (f := fun i : Fin 2 => Finset.univ.sup fun j : Fin 2 => denExp (M i j))
    (Finset.mem_univ i)

/-- **Achievability**: multiplying `M` by `√2^(sdeC M)` lands every entry
in the image of `ZOmega`, i.e. `sde_le M (sdeC M)`. Hence every matrix
has finite sde. -/
theorem sde_le_sdeC (M : Mat2) : sde_le M (sdeC M) := by
  have hex : ∀ i j : Fin 2,
      ∃ w : ZOmega, (sqrt2 : ZOmegaSqrt2) ^ sdeC M * M i j = of w :=
    fun i j => denExp_le_iff.mp (denExp_le_sdeC M i j)
  choose A hA using hex
  refine ⟨Matrix.of A, ?_⟩
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, hA i j, liftZOmegaMatrix, Matrix.map_apply,
      Matrix.of_apply, algebraMap_eq_of]

/-- **Every `Mat2` has finite sde** (achievability witness `sdeC M`). -/
theorem hasFiniteSde_all (M : Mat2) : hasFiniteSde M := ⟨sdeC M, sde_le_sdeC M⟩

/-- **Minimality**: any clearing exponent `k` bounds `sdeC M`. -/
theorem sdeC_le_of_sde_le {M : Mat2} {k : ℕ} (h : sde_le M k) : sdeC M ≤ k := by
  obtain ⟨A, hA⟩ := h
  refine Finset.sup_le fun i _ => Finset.sup_le fun j _ => ?_
  refine denExp_le_of_smul_eq_of (w := A i j) ?_
  have hentry := congrFun (congrFun hA i) j
  simpa [Matrix.smul_apply, liftZOmegaMatrix, Matrix.map_apply, smul_eq_mul,
         algebraMap_eq_of] using hentry

/-- **The noncomputable spec coincides with the computable definition**:
`sde M = sdeC M`. -/
theorem sde_eq_sdeC (M : Mat2) : sde M = sdeC M := by
  have hfin := hasFiniteSde_all M
  refine le_antisymm ?_ (sdeC_le_of_sde_le (sde_spec hfin))
  by_contra hlt
  push_neg at hlt
  exact sde_min hfin hlt (sde_le_sdeC M)

end KMM

end SKEFTHawking.RossSelinger
