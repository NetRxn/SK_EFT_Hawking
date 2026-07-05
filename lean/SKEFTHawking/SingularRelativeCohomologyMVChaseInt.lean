/-
# Phase 5q.H (E1 integral topology) — the relative-cohomology MV middle-exactness CHASE (algebraic core)

The concrete heart of `relCohomMv_exact_middleInt` (`ker Σ_H ⊆ range Δ_H`), worked directly on cochains
(no dual-space transport, no compatibility bookkeeping). Given cocycles `α ∈ relCochainsInt U`,
`β ∈ relCochainsInt V` whose restriction-difference is an absolute coboundary `δg` (`g ∈ relCochainsInt
(U∩V)` — the witness produced when `Σ_H([α],[β]) = 0`), the CONCRETE cochain-MV split
(`relCochainMvSum_surjectiveInt`, `g = gU − gV`) adjusts `α ↝ α − δgU`, `β ↝ β − δgV` (each cohomologous
in its own cohomology) to a SINGLE common cochain
  `ω' := α − δgU = β − δgV`,
which — being simultaneously `α − δgU ∈ relCochainsInt U` and `β − δgV ∈ relCochainsInt V` — lies in
`relCochainsInt U ⊓ relCochainsInt V` (= `Hom(Q)`), and is a cocycle. Lifting `[ω']` to
`RelativeCohomologyInt (U∪V)` (the dual small-chains iso, separate) then gives the `Δ_H`-preimage of
`([α],[β])`, closing the middle exactness.

This module lands the field-UC-free algebraic core; the small-chains lift is the one remaining piece.
Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeCochainMVSurjInt
import SKEFTHawking.SingularRelativeCohomologyRestrictInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeCochainMVSurjInt

namespace SKEFTHawking.SingularRelativeCohomologyMVChaseInt

variable {M : TopCat}

/-- **The common-intersection-cochain construction (chase core).** If `α − β = δg` (absolute cochains)
with `g ∈ relCochainsInt (U∩V) n`, the concrete cochain-MV split `g = gU − gV` yields `gU ∈
relCochainsInt U`, `gV ∈ relCochainsInt V` with `α − δgU = β − δgV`. The common value is the `Hom(Q)`
cocycle representing the `Δ_H`-preimage of `([α],[β])`. -/
theorem exists_common_cochain_of_coboundaryInt (U V : Set M) (n : ℕ)
    (α : relCochainsInt U (n + 1)) (β : relCochainsInt V (n + 1))
    (g : relCochainsInt (U ∩ V) n)
    (hg : (α : SingularCochainInt M (n + 1)) - (β : SingularCochainInt M (n + 1))
          = coboundaryₗ M n (g : SingularCochainInt M n)) :
    ∃ (gU : relCochainsInt U n) (gV : relCochainsInt V n),
      (α : SingularCochainInt M (n + 1)) - coboundaryₗ M n (gU : SingularCochainInt M n)
        = (β : SingularCochainInt M (n + 1)) - coboundaryₗ M n (gV : SingularCochainInt M n) := by
  obtain ⟨gU, gV, hsplit⟩ := relCochainMvSum_surjectiveInt U V n g
  refine ⟨gU, gV, ?_⟩
  have hδ : coboundaryₗ M n (gU : SingularCochainInt M n)
      - coboundaryₗ M n (gV : SingularCochainInt M n)
      = coboundaryₗ M n (g : SingularCochainInt M n) := by
    rw [← map_sub, hsplit]
  have key : (α : SingularCochainInt M (n + 1)) - (β : SingularCochainInt M (n + 1))
      = coboundaryₗ M n (gU : SingularCochainInt M n)
        - coboundaryₗ M n (gV : SingularCochainInt M n) := by
    rw [hδ, hg]
  have h0 : ((α : SingularCochainInt M (n + 1)) - coboundaryₗ M n (gU : SingularCochainInt M n))
      - ((β : SingularCochainInt M (n + 1)) - coboundaryₗ M n (gV : SingularCochainInt M n)) = 0 := by
    rw [show ((α : SingularCochainInt M (n + 1)) - coboundaryₗ M n (gU : SingularCochainInt M n))
        - ((β : SingularCochainInt M (n + 1)) - coboundaryₗ M n (gV : SingularCochainInt M n))
        = ((α : SingularCochainInt M (n + 1)) - (β : SingularCochainInt M (n + 1)))
          - (coboundaryₗ M n (gU : SingularCochainInt M n)
            - coboundaryₗ M n (gV : SingularCochainInt M n)) by abel, key, sub_self]
  exact sub_eq_zero.mp h0

end SKEFTHawking.SingularRelativeCohomologyMVChaseInt
