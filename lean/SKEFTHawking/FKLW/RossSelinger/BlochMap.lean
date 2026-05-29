/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the Bloch / SO(3) map and the `kSO3` T-count measure

The 𝕊₃ base-case coverage (the sole remaining input to an *unconditional*
`Nonempty KMMReduction`) is proved via the **Matsumoto-Amano normal-form route**
(Giles-Selinger arXiv:1312.6584), per deep research
(`Lit-Search/Phase-6x/"Phase 6x Tier-2 Item F — DR- formalizing the 𝕊₃ base-case
COVERAGE in Lean 4.md"`). The BFS route is *strictly dominated*: it needs the
connectivity-closure lemma KMM never prove; MA gives `coverage` by structural
recursion with no connectivity assumption.

The recursion measure is the **least denominator exponent of the SO(3) Bloch
image** `R(U)_{ij} = ½·Tr(σ_i U σ_j U†)`. Giles-Selinger Lemma 4.10 identifies it
with the Matsumoto-Amano T-count. This file ships the *computable* measure
`kSO3 : Mat2 → ℕ`; the MA recursion (`MAStep.lean`, `MACoverage.lean`) consumes it.

## Validated computationally (`scripts/kmm_ma_coverage_validation.py`)

Over the entire `𝕊₃` orbit (μ = `sde(|z₀₀|²)` ≤ 3, the 1664 matrices):

  * `kSO3 M = T-count M`           (= Giles-Selinger Lemma 4.10, confirmed)
  * `kSO3 M = 0 ⟺ M is a Clifford` (the 192 single-qubit Cliffords)
  * the unique MA syllable strip `s ∈ {T, HT, SHT}` lowers `kSO3` by exactly 1
  * `μ M ≤ 3 ⟹ kSO3 M ≤ 3`        (the bridge)

## Headline definitions

  * `madjoint` — conjugate-transpose (Hermitian adjoint) of a `Mat2`.
  * `pauliMat` — the three Pauli matrices `σ₁=X, σ₂=Y, σ₃=Z` as `Mat2`.
  * `blochEntry M i j = ½·Tr(σ_i M σ_j M†)` — the SO(3) Bloch image entry.
  * `kSO3 M = sup_{i,j} denExp (blochEntry M i j)` — the SO(3) least-denominator
    exponent = Matsumoto-Amano T-count.

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — MA normal form; Lemma 4.10
    (T-count = SO(3) lde); Cor 7.11 (the `sde ↔ k_SO3` bridge).
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) — `sde(|z₀₀|²)` framework.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.KMM
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-- **Hermitian adjoint** (conjugate-transpose) of a `2×2` matrix over
`ZOmegaSqrt2`: `(madjoint M) i j = conj (M j i)`. For a Clifford+T-realizable
(hence unitary) `M`, `M * madjoint M = 1`. -/
def madjoint (M : Mat2) : Mat2 := fun i j => ZOmegaSqrt2.conj (M j i)

/-- **The three Pauli matrices** `σ₁ = X`, `σ₂ = Y`, `σ₃ = Z`, reusing the
Clifford+T gate matrices. -/
def pauliMat : Fin 3 → Mat2
  | 0 => gateMatrix .X
  | 1 => gateMatrix .Y
  | 2 => gateMatrix .Z

/-- **One-half** `= 1/√2²` in `ZOmegaSqrt2`. -/
def half : ZOmegaSqrt2 := mk 1 2

/-- **Bloch / SO(3) image entry** `R(M)_{ij} = ½·Tr(σ_i · M · σ_j · M†)`.

For a unitary `M`, `R(M) ∈ SO(3)` has real entries in `ℤ[1/√2]`. The map
`M ↦ R(M)` is the (2-to-1) covering homomorphism `SU(2) → SO(3)`. -/
def blochEntry (M : Mat2) (i j : Fin 3) : ZOmegaSqrt2 :=
  half * Matrix.trace (pauliMat i * M * pauliMat j * madjoint M)

/-- **The Matsumoto-Amano T-count measure** `k_SO3` = the least-denominator
exponent of the SO(3) Bloch image (`= max_{i,j} denExp R(M)_{ij}`).

Giles-Selinger Lemma 4.10: this equals the Matsumoto-Amano T-count of `M`.
Computable (`denExp` is a computable `Quotient.lift`). The MA base-coverage
recursion descends on this measure: each syllable strip lowers it by 1, and
`kSO3 M = 0` exactly for the 192 single-qubit Cliffords. -/
def kSO3 (M : Mat2) : ℕ :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).sup
    (fun p => denExp (blochEntry M p.1 p.2))

/-! ## Sanity (kernel-checked: `kSO3 = T-count` on small examples)

These confirm the `kSO3` definition agrees with the validated Python oracle
(`scripts/kmm_ma_coverage_validation.py`): `kSO3` equals the Matsumoto-Amano
T-count. All `decide` — kernel-pure (standard three axioms only), no
`native_decide`. -/

/-- `kSO3 I = 0` (identity is a Clifford). -/
theorem kSO3_one : kSO3 (1 : Mat2) = 0 := by decide

/-- `kSO3 T = 1` (the `T` gate has T-count 1). -/
theorem kSO3_T : kSO3 (gateMatrix .T) = 1 := by decide

/-- `kSO3 H = 0` (Hadamard is a Clifford). -/
theorem kSO3_H : kSO3 (gateMatrix .H) = 0 := by decide

/-- `kSO3 S = 0` (the phase gate is a Clifford). -/
theorem kSO3_S : kSO3 (gateMatrix .S) = 0 := by decide

/-- `kSO3 X = 0` (Pauli-`X` is a Clifford). -/
theorem kSO3_X : kSO3 (gateMatrix .X) = 0 := by decide

/-- `kSO3 (T·T) = 0` (`T² = S` is a Clifford — kSO3 sees the operator, not the
gate string). -/
theorem kSO3_TT : kSO3 (gateMatrix .T * gateMatrix .T) = 0 := by decide

set_option maxRecDepth 4000 in
/-- `kSO3 (T·H·T) = 2` (T-count 2). `maxRecDepth` (not `maxHeartbeats`; Inv #10
permits it for finite `decide`) is bumped for the deeper kernel reduction. -/
theorem kSO3_THT :
    kSO3 (gateMatrix .T * gateMatrix .H * gateMatrix .T) = 2 := by decide

end KMM

end SKEFTHawking.RossSelinger
