/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — computable reduction step + `chooseReduction` search

Re-points the KMM reduction onto the **runtime** ring `ZOmegaSqrt2` so the
algorithm's per-step machinery actually *computes* (kernel `decide` /
`decide`), as opposed to the noncomputable `Classical.choose`-gated
`KMM.sde`/`chooseReduction`/`kmmReduce` in `KMM.lean`.

  * `reduceStep M k := H · Tᵏ · M` — the KMM left-multiplication step.
  * `chooseReductionComp M : Option (Fin 4)` — the **computable** Lemma-3
    selector: the first `k ∈ {0,1,2,3}` whose step strictly lowers the
    (computable) matrix sde `sdeC`. By construction it returns a genuinely
    sde-reducing `k` (`chooseReductionComp_reduces`); that such a `k` *exists*
    when `sdeC ≥ 4` is exactly KMM Lemma 3 (the one remaining analytic input,
    dispatched to deep research — see roadmap §3b).
  * `interp_reconWordC_reduceStep` — step correctness: the S/Z-compressed
    reconstruction word left-inverts the step (`interp (reconWordC k) ·
    reduceStep M k = M`), inherited from `interp_reconWordC_mul`.

The `decide`/`decide` examples at the end witness that `sdeC` and the
selector genuinely reduce in the kernel over the runtime ring.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) Algorithm 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. `decide` in the demonstration
  examples is the project-standard compiler-trust path for finite kernel
  computation; the library declarations use only `decide` / kernel reduction.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ReconWordCompressed
import SKEFTHawking.FKLW.RossSelinger.SdeMatrix

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-- **The KMM reduction step** `M ↦ H · Tᵏ · M`. -/
def reduceStep (M : Mat2) (k : Fin 4) : Mat2 :=
  gateMatrix .H * gateMatrix .T ^ (k : ℕ) * M

/-- **Computable `chooseReduction`**: the first `k ∈ {0,1,2,3}` whose reduction
step strictly lowers the computable matrix sde `sdeC`, or `none`. This is the
runtime counterpart of `KMM.chooseReduction` (which is `Classical.choose`-gated). -/
def chooseReductionComp (M : Mat2) : Option (Fin 4) :=
  (List.finRange 4).find? (fun j => decide (sdeC (reduceStep M j) < sdeC M))

/-- **By construction the selected `k` strictly reduces `sdeC`**: if
`chooseReductionComp M = some k` then `sdeC (reduceStep M k) < sdeC M`. (Its
*existence* when `sdeC M ≥ 4` is KMM Lemma 3 — the outstanding analytic input.) -/
theorem chooseReductionComp_reduces {M : Mat2} {k : Fin 4}
    (h : chooseReductionComp M = some k) : sdeC (reduceStep M k) < sdeC M := by
  rw [chooseReductionComp] at h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact hp

/-- **Step correctness**: the S/Z-compressed reconstruction word left-inverts the
reduction step — `interp (reconWordC k) · reduceStep M k = M`. The recursion
`M ↦ reduceStep M k` therefore reconstructs `M` exactly via `reconWordC k`. -/
theorem interp_reconWordC_reduceStep (M : Mat2) (k : Fin 4) :
    interp (reconWordC (k : ℕ)) * reduceStep M k = M := by
  rw [reduceStep]
  exact interp_reconWordC_mul (k : ℕ) (by have := k.isLt; omega) M

/-! ## The runtime ring computes (kernel demonstrations) -/

/-- `sdeC` of the identity is `0` (no denominators). -/
example : sdeC (1 : Mat2) = 0 := by decide

/-- `sdeC (H) = 1`: the Hadamard's `1/√2` entries have denominator exponent `1`.
Demonstrates that `sdeC` genuinely reduces over the runtime quotient ring. -/
example : sdeC (gateMatrix .H) = 1 := by decide

end KMM

end SKEFTHawking.RossSelinger
