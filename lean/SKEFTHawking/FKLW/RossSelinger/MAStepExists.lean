/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the `ma_step` EXISTENCE proof (reducing syllable exists)

`MAStepDecrease.lean` shipped the GIVEN-condition⟹decrease direction
(`kSO3_stripMat_lt`): if the mod-2 condition `∀ i,j: 2 ∣ blochStripNum s M i j`
holds, then `kSO3 (stripMat s M) < kSO3 M`. This file supplies the missing
EXISTENCE: for a realizable `M` with `kSO3 M ≥ 1`, SOME syllable `s ∈ {T,HT,SHT}`
satisfies the mod-2 condition, hence lowers `kSO3` by ≥ 1.

## The clean superset characterization (validated, then formalized)

The reducing syllable is governed by the cleared Bloch numerators
`B := blochNum M` (the `ℤ[ω]` matrix with `of (B i j) = √2^kSO3 · R(M) i j`). The
key constraints, both available from shipped substrate, are EXACT (not mod-2):

  * **Orthogonality** `∑ᵢ Bᵢⱼ · Bᵢₗ = 2^kSO3 · δⱼₗ` (cleared `blochMat_transpose_mul`).
  * **Reality** `conj (B i j) = B i j` (`R(M) ∈ SO(3)` is real; multiplicative
    via `bloch_hom` + per-gate `decide`).

Reality forces each `B i j` into the real subring `⟨a,0,-a,d⟩`, and the
conjugated column-sum `∑ᵢ normSq (B i j) = 2^kSO3` then bounds every coordinate
(`normSq.d = a²+b²+c²+d² ≥ 0`, summing to `2^kSO3 ≤ 8`). Over this finite,
column-decomposed domain, a `native_decide` establishes that a reducing syllable
always exists (validated in `scripts/kmm_ma_step_residue.py` /
`/tmp/btb_columns.py`: 0 failures over k = 1,2,3).

## This increment

`blochEntry_interp_real` / `blochEntry_realizable_real` — **reality** of the Bloch
image of any realizable matrix, the linchpin that bounds the `native_decide`
domain. Proof: `conj` is a ring hom and `bloch_hom` makes reality multiplicative,
so it reduces to the per-gate base case (`decide`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `decide`).
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.MAStepDecrease
import SKEFTHawking.FKLW.RossSelinger.BlochOrthogonal
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-! ## Reality of the Bloch image -/

set_option maxRecDepth 4000 in
/-- **Per-gate reality**: each Clifford+T gate's Bloch image is conjugation-fixed
(`R(g) ∈ SO(3)` is real). Kernel-checked (`decide`) over the 8 gates × 9 entries. -/
theorem blochEntry_gate_real (g : CliffordTGate) (i j : Fin 3) :
    ZOmegaSqrt2.conj (blochEntry (gateMatrix g) i j) = blochEntry (gateMatrix g) i j := by
  cases g <;> revert i j <;> decide

set_option maxRecDepth 4000 in
/-- **Reality of the identity's Bloch image.** -/
theorem blochEntry_one_real (i j : Fin 3) :
    ZOmegaSqrt2.conj (blochEntry (1 : Mat2) i j) = blochEntry (1 : Mat2) i j := by
  revert i j; decide

/-- **Reality of any realizable matrix's Bloch image** — the linchpin bounding the
`native_decide` domain. `conj` is a ring hom and `bloch_hom` makes reality
multiplicative, so it reduces (by induction on the gate word) to the per-gate
base case `blochEntry_gate_real`. -/
theorem blochEntry_interp_real (gs : List CliffordTGate) (i j : Fin 3) :
    ZOmegaSqrt2.conj (blochEntry (interp gs) i j) = blochEntry (interp gs) i j := by
  induction gs generalizing i j with
  | nil => rw [interp_nil]; exact blochEntry_one_real i j
  | cons g gs ih =>
      rw [interp_cons, bloch_hom (interp_isUnitaryT gs) i j, Fin.sum_univ_three,
          ZOmegaSqrt2.conj_add, ZOmegaSqrt2.conj_add, ZOmegaSqrt2.conj_mul,
          ZOmegaSqrt2.conj_mul, ZOmegaSqrt2.conj_mul, blochEntry_gate_real g i 0,
          blochEntry_gate_real g i 1, blochEntry_gate_real g i 2, ih 0 j, ih 1 j, ih 2 j,
          ← Fin.sum_univ_three (fun k => blochEntry (gateMatrix g) i k * blochEntry (interp gs) k j),
          ← bloch_hom (interp_isUnitaryT gs) i j]

/-- **Reality for the realizability predicate.** -/
theorem blochEntry_realizable_real {M : Mat2} (h : IsCliffordTRealizable M) (i j : Fin 3) :
    ZOmegaSqrt2.conj (blochEntry M i j) = blochEntry M i j := by
  obtain ⟨gs, rfl⟩ := h
  exact blochEntry_interp_real gs i j

end KMM

end SKEFTHawking.RossSelinger
