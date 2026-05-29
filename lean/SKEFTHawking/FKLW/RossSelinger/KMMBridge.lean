/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the `μ ≤ 3 ⟹ kSO3 ≤ 3` bridge (native_decide core)

The MA coverage recursion (`MACoverage.lean`) consumes the bridge

  `bridge : ∀ M, IsCliffordTRealizable M → muMeasure M ≤ 3 → kSO3 M ≤ 3`

— the quantitative `sde ↔ k_SO3` relationship of Giles-Selinger Cor 7.11 — as
one of its two remaining hypotheses (the other is the Clifford base). This file
ships the finite computational core of the bridge.

## The M-structure reduction

By `column0_cleared_bounded`, a `μ(M) ≤ 3` unitary clears column 0 at exponent
`2`: `√2²·M₀₀ = of x`, `√2²·M₁₀ = of y` with `(|x|²).d ≤ 4`, `(|y|²).d ≤ 4`
(so each `ℤ[ω]` coordinate of `x, y` is bounded by `2`). By `realizable_col1`,
column 1 is determined: `M₀₁ = -(ωᵏ·conj M₁₀)`, `M₁₁ = ωᵏ·conj M₀₀`. Hence

  `M = reconstruct x y k = !![mk x 2, -(ωᵏ·conj (mk y 2)); mk y 2, ωᵏ·conj (mk x 2)]`.

So `kSO3 M = kSO3 (reconstruct x y k)`, a function of the *bounded integer data*
`(x, y, k)`. The unitarity forces `|x|² + |y|² = 2² = ⟨0,0,0,4⟩` (column-0 norm,
scaled by `√2⁴`), and `μ ≤ 3` is exactly `√2 ∣ |x|²` (`= gde(|x|²) ≥ 1`, since
`μ = denExp(|M₀₀|²) = 4 − gde(|x|²)`).

## The finite check

`bridgeBoxOk` ranges `(x, y)` over the explicit `5⁴`-coordinate box `[-2,2]⁴`,
filters to the necessary conditions `|x|² + |y|² = ⟨0,0,0,4⟩` and
`dividesSqrt2 |x|²`, and over `k ∈ {0,…,7}` checks `kSO3 (reconstruct x y k) ≤ 3`.

  * **Validated** (`scripts/bridge_superset_validation.py`, 2026-05-29): the
    filtered box is *exactly* the `1664` realizable `μ ≤ 3` matrices (208 `(x,y)`
    pairs × 8 phases); `max kSO3 = 3`; `0` failures. (Without the `dividesSqrt2`
    filter the superset leaks 512 `μ = 4` tuples with `kSO3 = 4` — the filter is
    the exact `μ ≤ 3` condition, not slack.)

`bridge_box_core : bridgeBoxOk = true` is `native_decide` (the `1664`-tuple
check; the unfiltered `5⁴ × 5⁴` pairs are cheap, `kSO3` runs only on the `1664`
that pass). The connecting lemmas (`M = reconstruct x y k`, coordinate bounds,
`List.all` extraction) and the abstract `bridge` theorem follow in a companion
increment, mirroring the `ma_step` core → `ma_step_exists` split.

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — Cor 7.11 (`sde ↔ k_SO3`).
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) — Theorem 1 (column structure).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `native_decide`).
- **#15** (no new project-local axioms): respected (`native_decide` carries the
  tracked `Lean.ofReduceBool` axiom, allowed alongside the kernel three).

-/

import SKEFTHawking.FKLW.RossSelinger.BlochMap
import SKEFTHawking.FKLW.RossSelinger.KMMForm
import SKEFTHawking.FKLW.RossSelinger.NormSqGde
import SKEFTHawking.FKLW.RossSelinger.GdeSqrt2

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Matrix

/-- **The KMM Theorem 1 reconstruction** of a realizable `μ ≤ 3` matrix from its
column-0 `ℤ[ω]` numerators `x, y` (cleared at exponent `2`) and the global phase
`k`: column 1 is `column-0`-determined (`realizable_col1`). -/
def reconstruct (x y : ZOmega) (k : ℕ) : Mat2 :=
  !![mk x 2, -(ωS ^ k * conj (mk y 2)); mk y 2, ωS ^ k * conj (mk x 2)]

/-- The explicit coordinate range `[-2, 2]` for each `ℤ[ω]` component (the
`(|x|²).d ≤ 4` sum-of-squares bound forces `|coord| ≤ 2`). -/
def intBox : List ℤ := [-2, -1, 0, 1, 2]

/-- The explicit `5⁴ = 625`-element `ℤ[ω]` box `[-2, 2]⁴`. -/
def zomBox : List ZOmega :=
  intBox.flatMap (fun a => intBox.flatMap (fun b =>
    intBox.flatMap (fun c => intBox.map (fun d => ⟨a, b, c, d⟩))))

/-- **The finite bridge check**: over the `ℤ[ω]` box, for every `(x, y)` meeting
the unitarity necessary condition `|x|² + |y|² = ⟨0,0,0,4⟩` and the `μ ≤ 3`
condition `√2 ∣ |x|²`, and every phase `k ∈ {0,…,7}`, the reconstructed matrix
has `kSO3 ≤ 3`. -/
def bridgeBoxOk : Bool :=
  zomBox.all (fun x => zomBox.all (fun y =>
    if ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega)
        ∧ ZOmega.dividesSqrt2 (ZOmega.normSq x)
    then (List.range 8).all (fun k => kSO3 (reconstruct x y k) ≤ 3)
    else true))

set_option maxRecDepth 8000 in
/-- **The bridge native_decide core**: the `1664`-tuple finite check passes.
`kSO3 (reconstruct x y k) ≤ 3` for every `(x, y, k)` in the filtered box (= the
`μ ≤ 3` realizable matrices). Validated `0`-failure in
`scripts/bridge_superset_validation.py`. -/
theorem bridge_box_core : bridgeBoxOk = true := by native_decide

end KMM

end SKEFTHawking.RossSelinger
