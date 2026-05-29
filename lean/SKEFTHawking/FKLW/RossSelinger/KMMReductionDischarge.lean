/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — `Nonempty KMMReduction` from the 𝕊₃ base coverage

The full `μ`-tracking KMM recursion is correct-with-termination + length-bounded
(`KMMReduceMu.lean`). This file assembles a concrete `KMMReduction` from the **sole
remaining input**: the KMM base-case coverage

  `coverage : ∀ M, IsCliffordTRealizable M → μ(M) ≤ 3 →
                 ∃ gs, interp gs = M ∧ gs.length ≤ 9`

i.e. every Clifford+T-realizable matrix with squared-modulus sde `≤ 3` (the finite
`𝕊₃` orbit, computed `= 1664` matrices with max word length `N₃ = 9` by
`scripts/kmm_n3_bfs.py`) is the interpretation of some `≤ 9`-gate word.

  * `baseFinder9 M` — a `≤ 9`-gate word for `M` when one exists (`Classical.choose`),
    else `[]`. Length `≤ 9` unconditionally (`baseFinder9_length`); correct exactly
    when the coverage applies (`baseFinder9_correct`).
  * `kmmReduction_of_coverage` — **`coverage ⟹ Nonempty KMMReduction`**: the
    concrete instance `reduce M := kmmReduceMu baseFinder9 (μ(M)) M`, with `correct`
    from `interp_kmmReduceMu` (the recursion bottoms at `μ ≤ 3`, where `baseFinder9`
    is correct) and `length_bound` `≤ 9 + 4·μ(M) = N₃ + 4·sde(|z₀₀|²)` (KMM Cor 1)
    from `length_kmmReduceMu`.

This reduces Phase 6x orphan #2 (at the deterministic-branch level) to the single
`𝕊₃`-coverage fact — **no axiom is introduced** (Inv #15): the coverage is a
*hypothesis* of `kmmReduction_of_coverage`, to be discharged by a Lean proof of the
finite base-case orbit (the remaining work), NOT asserted. Once `coverage` is
proven, `Nonempty KMMReduction` is unconditional and the `[Nonempty KMMReduction]`
gating in `KMM.lean` (kmmReduce / Item G headline) is discharged.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected — `coverage` is a hypothesis,
  not an `axiom`. `kmmReduction_of_coverage` inherits the tracked `native_decide`
  (via `mu_decrease`) only.

-/

import SKEFTHawking.FKLW.RossSelinger.KMMReduceMu

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Classical

/-- **The KMM 𝕊₃ base finder**: a `≤ 9`-gate word for `M` when one exists, else `[]`.
Noncomputable (`Classical.choose`); the algorithm's base case (`μ ≤ 3`). -/
noncomputable def baseFinder9 (M : Mat2) : List CliffordTGate :=
  if h : ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 9 then Classical.choose h else []

/-- **`baseFinder9` emits words of length `≤ 9`** (unconditionally — the `N₃` bound). -/
theorem baseFinder9_length (M : Mat2) : (baseFinder9 M).length ≤ 9 := by
  unfold baseFinder9
  split
  · next h => exact (Classical.choose_spec h).2
  · simp

/-- **`baseFinder9` is correct on the `𝕊₃` orbit** (given the coverage): for
realizable `M` with `μ(M) ≤ 3`, `interp (baseFinder9 M) = M`. -/
theorem baseFinder9_correct
    (coverage : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 →
      ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 9)
    (M : Mat2) (hM : IsCliffordTRealizable M) (hμ : muMeasure M ≤ 3) :
    interp (baseFinder9 M) = M := by
  have h := coverage M hM hμ
  unfold baseFinder9
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

/-- **Conditional discharge of `Nonempty KMMReduction`**: the `𝕊₃` base coverage
yields a concrete KMM exact-synthesis algorithm. `reduce M := kmmReduceMu
baseFinder9 (μ(M)) M`; `correct` from `interp_kmmReduceMu` (recursion bottoms at
`μ ≤ 3`, where `baseFinder9` is correct); `N₃ = 9`; `length_bound` `≤ 9 + 4·μ(M)
= N₃ + 4·sde(|z₀₀|²)` (KMM Corollary 1) from `length_kmmReduceMu`.

The coverage is a *hypothesis*, not an axiom (Inv #15) — discharging it (the finite
`𝕊₃` orbit proof) makes `Nonempty KMMReduction` unconditional. -/
theorem kmmReduction_of_coverage
    (coverage : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 →
      ∃ gs : List CliffordTGate, interp gs = M ∧ gs.length ≤ 9) :
    Nonempty KMMReduction :=
  ⟨{ reduce := fun M => kmmReduceMu baseFinder9 (muMeasure M) M
     N₃ := 9
     correct := fun M hM => interp_kmmReduceMu baseFinder9
       (fun M' hM' hμ' => baseFinder9_correct coverage M' hM' hμ') (muMeasure M) M hM (le_refl _)
     length_bound := fun M _ => length_kmmReduceMu baseFinder9 9 baseFinder9_length (muMeasure M) M }⟩

end KMM

end SKEFTHawking.RossSelinger
