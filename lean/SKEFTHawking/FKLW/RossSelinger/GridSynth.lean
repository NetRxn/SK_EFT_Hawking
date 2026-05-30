/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Items G/H — the Ross-Selinger grid-problem solver (foundation)

The Ross-Selinger constructive synthesis (arXiv:1403.2975 §5) decomposes as:
  (a) `epsilonRegion θ ε` — the convex target region in `ℂ`;
  (b) `gridSolutions A B k` — enumerate `u ∈ ℤ[ω][1/√2]` with `u ∈ A`, Galois `u• ∈ B`;
  (c) `diophantine u k` — solve `t·t* = √2^{2k} − u·u*` in `ℤ[ω]`;
  (d) `assembleUnitary u t k` — `M = [[u, −t*],[t, u*]]/√2^k` (this file);
  (e) `kmmReduce` — the exact Clifford+T word (SHIPPED, `KMM.lean` / `CliffordBase.lean`).

This file ships step (d) (the assembly) and the `normSq (mk z k)` helper. Steps (a)–(c)
— the convex-geometry ε-region and the `ℤ[ω]` prime-factorization Diophantine, the
analytic core of the solver — are the next increment (deterministic branch only; NO §4
factoring fast-path). Validated end-to-end in `scripts/grid_stub_validation.py`: the
(c)+(d) core yields an exactly realizable `det`-1 `SU(2)` matrix for every sample target.

## Headline results

  * `ZOmegaSqrt2.normSq_mk : normSq (mk z k) = mk (ZOmega.normSq z) (2*k)`.
  * `assembleUnitary u t k = !![mk u k, −conj (mk t k); mk t k, conj (mk u k)]`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.UnitaryT
import SKEFTHawking.FKLW.RossSelinger.Conj
import SKEFTHawking.FKLW.RossSelinger.NormSqGde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmegaSqrt2

/-- **Squared modulus of a cleared element**: `normSq (mk z k) = mk (|z|²_{ℤ[ω]}) (2k)`
— the `ZOmegaSqrt2` squared-modulus of `z/√2^k` is the `ℤ[ω]` squared-modulus of `z` over
`√2^{2k}`. (`conj_mk` + `mk_mul`; `ZOmega.normSq z = z·conj z`.) -/
theorem normSq_mk (z : ZOmega) (k : ℕ) : normSq (mk z k) = mk (ZOmega.normSq z) (2 * k) := by
  rw [normSq, conj_mk, mk_mul, ZOmega.normSq, two_mul]

end ZOmegaSqrt2

namespace KMM

open ZOmegaSqrt2
open scoped Matrix

/-- **(d) Assemble** the Ross-Selinger unitary from a solved `(u, t)` pair at denominator
exponent `k`: `M = [[u, −t*], [t, u*]] / √2^k` over `ZOmegaSqrt2`. When `u·u* + t·t* =
√2^{2k}` (the Diophantine constraint) this is special unitary (`det = 1`, columns
orthonormal) — validated in `scripts/grid_stub_validation.py`; the Lean `IsUnitaryT`
proof (via `normSq_mk` + the column identities) is the next increment. -/
noncomputable def assembleUnitary (u t : ZOmega) (k : ℕ) : Mat2 :=
  !![mk u k, -(conj (mk t k)); mk t k, conj (mk u k)]

@[simp] theorem assembleUnitary_apply_zero_zero (u t : ZOmega) (k : ℕ) :
    assembleUnitary u t k 0 0 = mk u k := rfl
@[simp] theorem assembleUnitary_apply_one_zero (u t : ZOmega) (k : ℕ) :
    assembleUnitary u t k 1 0 = mk t k := rfl

end KMM

end SKEFTHawking.RossSelinger
