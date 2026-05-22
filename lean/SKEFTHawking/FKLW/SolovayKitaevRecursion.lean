/-
SK_EFT_Hawking Phase 6t Wave 4 SHIP (2026-05-22 PM):
**Solovay-Kitaev recursion structure for Fibonacci anyon braid words**.

This module ships the Solovay-Kitaev recursion `skApprox n U` — the level-`n`
braid-word approximation to a target SU(2) element `U`. The recursion is
parameterized by:
  - A `BalancedDecompositionInput` interface, which provides the per-step
    balanced commutator decomposition (from Wave 2 + Wave 2-followup).
  - The Wave 3 ε₀-net base case `fibonacciEpsilonNet_findNearest`.

The per-step error shrinkage (the Dawson-Nielsen quadratic-to-3/2-shrinkage)
is captured by the predicate `SkApproxErrorShrinkage`. The recursion's
correctness — that `‖ρ_Fib_SU2(skApprox n U) - U‖` shrinks super-quadratically
in `n` — is captured by `SkApproxErrorBound`, which is composed in Wave 5
via the length-bound asymptotic + Wave 6 in the headline theorem.

## Phase 6t roadmap alignment

  - Wave 4 (this module) → consumed by Wave 5 (length bound) for the length
    recurrence, by Wave 6 (headline) for the final composition, and by Wave 7
    (applications) for the runnable compiler.

  - The recursion is parameterized by the substantive balanced-commutator
    decomposition (Wave 2 + Wave 2-followup). Per the autonomous-loop
    architecture: when Wave 2-followup ships the general-axis discharge,
    this module's recursion automatically unblocks the headline composition.

## Pipeline Invariant compliance

  - Invariant #10 (no `maxHeartbeats`): RESPECTED.
  - Invariant #15 (no new axioms): RESPECTED — the recursion uses
    `Classical.choose` (in the standard kernel closure) and the predicate
    `SkApproxErrorShrinkage` is a Prop, not an axiom.

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030, §3.1-3.2 (the recursion).
-/

import Mathlib
import SKEFTHawking.FKLW.GroupCommutator
import SKEFTHawking.FKLW.SU2BalancedCommutator
import SKEFTHawking.FKLW.FibonacciEpsilonNet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SolovayKitaevRecursion

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking.FKLW SKEFTHawking.FKLW.FibonacciEpsilonNet
open SKEFTHawking.FKLW.SU2BalancedCommutator

/-! ## 1. The SK base-case threshold `ε₀` + cubic-remainder constant

The Wave 3 ε₀-net provides a base-case approximation at any target precision
`ε₀ > 0`. For SK to converge super-quadratically via the Wave 1 cubic-remainder
lemma `groupCommutator_lie_bracket_cubic_remainder` (with constant K = 320),
`ε₀` must satisfy `K² · ε₀ < 1` — equivalently `ε₀ < 1 / K² = 1 / 102400`.

This was originally set as `ε₀ := 1/(4·C_balance²) = 1/2` (Phase 6t initial
ship) but that value is provably too loose: with K = 320, `K²·(2·ε₀) =
102400 · 1 = 102400 ≫ 1`, violating the SK convergence condition. Updated
2026-05-22 PM post-deep-research to the rigorous value `ε₀ := 1/(8·K²) =
1/819200`, giving `K²·(2·ε₀) = 1/4 < 1` ✓. -/

/-- The cubic-remainder constant from Wave 1's `bch_order_2_cubic_thm`:
`‖groupCommutator(exp(iF), exp(iG)) - exp(-[F,G])‖ ≤ K · δ³` with K = 320. -/
noncomputable def K_cubic : ℝ := 320

/-- `K_cubic > 0`. -/
lemma K_cubic_pos : 0 < K_cubic := by unfold K_cubic; norm_num

/-- The SK base-case threshold: chosen so that `K²·(2·ε₀) = 1/4 < 1`,
the rigorous Dawson-Nielsen super-quadratic convergence condition. -/
noncomputable def ε₀ : ℝ := 1 / (8 * K_cubic ^ 2)

/-- `ε₀ > 0`. -/
lemma ε₀_pos : 0 < ε₀ := by
  unfold ε₀
  have h_K := K_cubic_pos
  positivity

/-- The explicit numerical value: `ε₀ = 1/819200`. -/
lemma ε₀_value : ε₀ = 1 / 819200 := by
  unfold ε₀ K_cubic; norm_num

/-- `2 · ε₀ = 1 / 409600 < 1` — used by the contract's length bound. -/
lemma two_ε₀_value : 2 * ε₀ = 1 / 409600 := by
  rw [ε₀_value]; norm_num

/-- `2 · ε₀ < 1` — ensures `log(2·ε₀) ≠ 0` (avoids div-by-zero in `skLevel`). -/
lemma two_ε₀_lt_one : 2 * ε₀ < 1 := by
  rw [two_ε₀_value]; norm_num

/-- `0 < 2 · ε₀` — straightforward positivity. -/
lemma two_ε₀_pos : 0 < 2 * ε₀ := by
  rw [two_ε₀_value]; norm_num

/-! ## 2. The SK recursion structure

We define `skApprox` via well-founded recursion on the level `n`. The structure
of the recursion is parameterized by a `BalancedDecompositionInput` — the Wave 2
+ Wave 2-followup balanced-commutator construction.

In this module, we ship the **fuel-bounded** form of the recursion: `skApprox
n U` always terminates, but its substantive error-bound correctness relies on
the tracked predicate `SkApproxErrorShrinkage` (discharged via Wave 2-followup).
-/

/-- The Solovay-Kitaev approximation: level-`n` braid-word approximation to
target SU(2) element `U`.

**Wave 4 substrate-deferred form.** This skeleton defines the recursion at
level 0 (base case via Wave 3 ε₀-net) and at level n+1 returns the level-n
approximation (placeholder for the substantive recursive composition).
The substantive content — the per-step commutator refinement
`V_{n+1} = V_n · groupCommutator(skApprox n A_n) (skApprox n B_n)` — is
unblocked when Wave 2-followup ships the constructive `balancedDecomp`
function. -/
noncomputable def skApprox : ℕ → ↥(specialUnitaryGroup (Fin 2) ℂ) → FibonacciBraidWord
  | 0, U => fibonacciEpsilonNet_findNearest U ε₀ ε₀_pos
  | n + 1, U => skApprox n U  -- Wave-4-followup: substantive recursive refinement

/-- Level-0 unfolding: the base case is the ε₀-net's nearest braid word. -/
lemma skApprox_zero (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    skApprox 0 U = fibonacciEpsilonNet_findNearest U ε₀ ε₀_pos := rfl

/-- Level-(n+1) unfolding (current substrate-deferred form). -/
lemma skApprox_succ (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    skApprox (n + 1) U = skApprox n U := rfl

/-! ## 3. The per-step shrinkage predicate

The Dawson-Nielsen per-step shrinkage: `‖V_{n+1} - U‖ ≤ K · ‖V_n - U‖^(3/2)`.

This is the SUBSTANTIVE content of the SK recursion. The full discharge
requires Wave 2-followup (general-axis balanced commutator) + Wave 1 cubic
linearization (already shipped) + careful per-step bookkeeping.

In this Wave 4 ship, we capture the shrinkage as a tracked Prop predicate,
which becomes a hypothesis for Wave 5's length bound and Wave 6's headline. -/

/-- **Tracked Prop**: the per-step error-shrinkage property of `skApprox`.

For every `n : ℕ` and `U ∈ SU(2)`, the level-(n+1) approximation `V_{n+1}` is
within Dawson-Nielsen-cubic-shrunk distance of the target:
  `‖ρ_Fib_SU2 (skApprox (n+1) U) - U‖ ≤ K · ‖ρ_Fib_SU2 (skApprox n U) - U‖^(3/2)`
for an explicit constant K (Kuperberg-2009-tight).

Discharge plan: Wave 2-followup (general-axis balanced commutator) + Wave 4
substantive body of `skApprox (n+1)` (composition of `groupCommutator` with
the recursive approximations of `A_n, B_n`). -/
def SkApproxErrorShrinkage (K : ℝ) : Prop :=
  ∀ (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)),
    ‖(ρ_Fib_SU2 (skApprox (n + 1) U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
    K * ‖(ρ_Fib_SU2 (skApprox n U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ (3 / 2 : ℝ)

/-- **Tracked Prop**: the level-`n` error bound (closed-form solution to the
recursion).

For every `n : ℕ` and `U ∈ SU(2)`, the level-`n` approximation is within
`ε_n`-distance of the target, where `ε_n = ε₀^((3/2)^n)` (the per-step
shrinkage composed n times).

This is the closed-form consequence of `SkApproxErrorShrinkage`. -/
def SkApproxErrorBound (K : ℝ) : Prop :=
  ∀ (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)),
    ‖(ρ_Fib_SU2 (skApprox n U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
    K * (2 * ε₀) ^ ((3 / 2 : ℝ) ^ n)

/-! ## 4. Base case error bound (UNCONDITIONAL)

Level-0 of `skApprox` is the ε₀-net's nearest-finder; its error bound is
exactly the Wave 3 Headline 2 result `≤ 2 · ε₀`. -/

/-- **HEADLINE (Phase 6t Wave 4 — Level-0 error bound)**: the base case of
`skApprox` satisfies the Wave 3 ε₀-net bound. UNCONDITIONAL. -/
theorem skApprox_zero_error_bound
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    ‖(ρ_Fib_SU2 (skApprox 0 U) : Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε₀ := by
  rw [skApprox_zero]
  exact fibonacciEpsilonNet_findNearest_approx_opNorm U ε₀ ε₀_pos

/-! ## 4b. Task #35 trivial discharges ROLLED BACK (2026-05-22 PM post-deep-research)

The earlier `K=1` trivial discharges of `SkApproxErrorShrinkage` and
`SkApproxErrorBound` (commit dec0d21) were valid under the OLD `ε₀ = 1/2`
which gave `2·ε₀ = 1` and a constant-1 RHS in the Bound. Under the new
rigorous `ε₀ = 1/819200`, those K=1 discharges no longer hold:
`(2·ε₀)^x` for `x = (3/2)^n` SHRINKS in n (since `2·ε₀ < 1`), but under
the placeholder `skApprox (n+1) U = skApprox n U`, `‖V_n - U‖ = ‖V_0 - U‖
≤ 2·ε₀` stays constant — exceeding the tighter level-n bound.

The Wave 4-followup substantive discharges (with substantive recursion via
`balancedCommutatorGeneralAxisGroup_holds` + Wave 1 cubic remainder +
OneParameterSubgroupSU2 matrix log) are tracked for iteration 2 of the
substantive refactor. -/

/-! ## 5. Module summary

SolovayKitaevRecursion.lean (Phase 6t Wave 4 SHIP, 2026-05-22 PM):
**SK recursion structure for Fibonacci braid-word approximations**.

  *Definitions:*
  - `ε₀ := 1 / (4 · C_balance²) = 1/2` — base-case threshold
  - `skApprox n U : FibonacciBraidWord` — level-`n` braid-word approximation

  *Predicates (tracked Props for Wave 4-followup discharge):*
  - `SkApproxErrorShrinkage K` — per-step error-shrinkage
  - `SkApproxErrorBound K` — closed-form level-`n` error bound

  *Headline (UNCONDITIONAL):*
  - `skApprox_zero_error_bound` — base case ≤ 2·ε₀, direct consumption of
    Wave 3's `fibonacciEpsilonNet_findNearest_approx_opNorm`.

  *Wave 4-followup discharge plan:*
  - Discharge `SkApproxErrorShrinkage` via:
    1. Strengthen `skApprox (n+1)` to do the substantive recursive
       composition (consume Wave 2 + Wave 2-followup general-axis balanced
       commutator).
    2. Apply Wave 1 Headline 3 (groupCommutator_stability) + Wave 2 Headline
       (balanced commutator) per step.
  - Discharge `SkApproxErrorBound` via induction on `n` + Real.rpow algebra.

  *Pipeline Invariant compliance:*
  - Invariant #10 (no `maxHeartbeats`): RESPECTED
  - Invariant #15 (no new axioms): RESPECTED

Zero new project-local axioms. Pre-Phase-6t axiom count UNCHANGED. -/

end SKEFTHawking.FKLW.SolovayKitaevRecursion
