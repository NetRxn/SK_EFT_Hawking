/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the `kSO3`-decrease of a syllable strip (mod-2 condition)

The `ma_step` crux: for a realizable `M` with `kSO3 M = n ≥ 1`, the residue-selected
syllable strip lowers `kSO3` by 1. By `bloch_stripMat`,
`R(stripMat s M) = R((sylMat s)†)·R(M)`, so — writing `n = kSO3 M`,
`bᵢⱼ := √2ⁿ·R(M)ᵢⱼ` (cleared Bloch numerators) and `c^s := √2·R((sylMat s)†)`
(CONCRETE, cleared, since each syllable has `kSO3 = 1`) — one computes

  `√2^(n-1) · R(stripMat s M)ᵢⱼ = (∑ₖ c^s_ik · b_kj) / 2`,

so the decrease is governed by the clean **mod-2 condition**
`∀ i,j: ∑ₖ c^s_ik · b_kj ≡ 0 (mod 2)` on the (15-class) Bloch parity residue of `M`
(`scripts/kmm_ma_step_residue.py`).

This file ships the concrete `c^s` constants (`sylBlochNum`) and the clearing
identity `of (c^s_ik) = √2 · R((sylMat s)†)ᵢₖ` — the foundation of the decrease.
The full decrease lemma + the 15-class `native_decide` build on top.

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — the SO(3)/Bloch picture of MA reduction.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `decide`).
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.MAStep

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-- **The cleared syllable rotation** `c^s := √2 · R((sylMat s)†)` as a `ZOmega`
`3×3` matrix (each syllable has `kSO3 = 1`, so `√2·R((sylMat s)†)` is `ZOmega`-valued).
Values computed + cross-checked in `scripts/kmm_ma_step_residue.py`. -/
def sylBlochNum : Syllable → Matrix (Fin 3) (Fin 3) ZOmega
  | .T   => !![1, 1, 0; -1, 1, 0; 0, 0, ZOmega.sqrt2]
  | .HT  => !![0, -1, 1; 0, -1, -1; ZOmega.sqrt2, 0, 0]
  | .SHT => !![1, 0, 1; 1, 0, -1; 0, ZOmega.sqrt2, 0]

set_option maxRecDepth 8000 in
/-- **Clearing identity** `of (c^s_ik) = √2 · R((sylMat s)†)ᵢₖ`: the concrete
`sylBlochNum` equals `√2` times the SO(3) Bloch image of the syllable's adjoint.
Kernel-checked (`decide`). -/
theorem sylBlochNum_clearing (s : Syllable) :
    ∀ i k : Fin 3,
      ZOmegaSqrt2.of (sylBlochNum s i k)
        = sqrt2 * blochEntry (ZOmegaSqrt2.adjoint (sylMat s)) i k := by
  cases s <;> decide

end KMM

end SKEFTHawking.RossSelinger
