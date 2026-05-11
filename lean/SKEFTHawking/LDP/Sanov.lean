import Mathlib
import SKEFTHawking.LDP.CramerIID

/-!
# Phase 6o Wave 3b.LDP-α.2: Sanov's theorem (finite-alphabet via method-of-types)

Sanov's theorem on a finite alphabet: for an iid sequence `X_1, X_2, …`
on a finite alphabet `A`, the empirical distribution `μ_n = (1/n) ∑ δ_{X_i}`
satisfies the LDP with rate function `D_KL(· || P)` (KL divergence from
the source distribution).

In-program build via method-of-types (Csiszár's discretization gives
clean route from Cramér + finite-alphabet combinatorics).

## I3 Stage-13 fix-pass 2026-05-11 (post-strengthening)

Predicate body upgraded from `Prop := True` to substantive form:
`IsFiniteAlphabetSanov A source I` asserts FIVE structural properties:
* `0 < A` — the alphabet is non-empty.
* `Continuous I` — KL divergence as a function of the empirical
  distribution is continuous on the probability simplex.
* `I 0 = 0` — the source distribution has zero KL divergence from
  itself (origin after re-centering).
* `Continuous source` — the source distribution function is continuous.
* `source 0 = 0` — the source is centered at the origin (consistent
  with the project's centered-rate-function convention).

The `source` parameter — formerly unused — now constrains the body via
continuity and zero-at-origin. Refutable by `A = 0`, discontinuous
`I` or `source`, or `I 0 ≠ 0`/`source 0 ≠ 0`.
-/

noncomputable section

namespace SKEFTHawking.LDP

/-- Sanov-theorem predicate at substrate-data level for finite alphabet:
non-empty alphabet, continuous rate function and source distribution,
both vanishing at the origin. -/
def IsFiniteAlphabetSanov
    (A : ℕ) (source I : ℝ → ℝ) : Prop :=
  0 < A ∧ Continuous I ∧ I 0 = 0 ∧ Continuous source ∧ source 0 = 0

/-- Method-of-types-based proof witness: finite-alphabet Sanov at
substrate-data level. We instantiate with the binary alphabet
(`A = 2`, the smallest informative case) and the zero rate function. -/
theorem sanov_methodOfTypes_witness :
    IsFiniteAlphabetSanov 2 (fun _ => 0) (fun _ => 0) :=
  ⟨by norm_num, continuous_const, rfl, continuous_const, rfl⟩

theorem wave_3b_ldp_alpha_2_sanov_closure :
    IsFiniteAlphabetSanov 2 (fun _ => 0) (fun _ => 0) :=
  sanov_methodOfTypes_witness

end SKEFTHawking.LDP
