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

/-! ## Orthogonality of the cleared Bloch numerators -/

/-- **`of` is injective** (`ZOmega ↪ ZOmegaSqrt2`). -/
theorem of_injective : Function.Injective (ZOmegaSqrt2.of) := by
  intro z w h
  have := ZOmegaSqrt2.mk_eq_mk_iff.mp h
  simpa using this

/-- **Orthogonality of the cleared Bloch numerators**: `∑ᵢ Bᵢⱼ · Bᵢₗ = 2^kSO3 · δⱼₗ`
in `ZOmega` (the non-conjugated `RᵀR = I` of `blochMat_transpose_mul`, cleared by
`√2^(2·kSO3)` via `blochNum_spec`). Gives the per-column norm (`j = l`) and the
pairwise orthogonality (`j ≠ l`) the `ma_step` `native_decide` consumes. -/
theorem blochNum_orthogonal {M : Mat2} (hu : ZOmegaSqrt2.IsUnitaryT M) (j l : Fin 3) :
    ∑ i, blochNum M i j * blochNum M i l
      = if j = l then ((2 : ZOmega) ^ kSO3 M) else 0 := by
  apply of_injective
  have hδ : ∑ i, blochEntry M i j * blochEntry M i l = if j = l then (1 : ZOmegaSqrt2) else 0 := by
    have h := blochMat_transpose_mul hu
    have := congrFun (congrFun h j) l
    simpa [blochMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.one_apply] using this
  have hsq : (sqrt2 : ZOmegaSqrt2) ^ kSO3 M * sqrt2 ^ kSO3 M = ZOmegaSqrt2.of ((2 : ZOmega) ^ kSO3 M) := by
    rw [← pow_add, ← two_mul, pow_mul,
      show (sqrt2 : ZOmegaSqrt2) ^ 2 = ZOmegaSqrt2.of (2 : ZOmega) from by decide,
      ← ZOmegaSqrt2.ofRingHom_apply, ← map_pow]; rfl
  conv_lhs => rw [← ZOmegaSqrt2.ofRingHom_apply, map_sum]
  simp only [ZOmegaSqrt2.ofRingHom_apply, ZOmegaSqrt2.of_mul, ← blochNum_spec]
  rw [show (∑ i, sqrt2 ^ kSO3 M * blochEntry M i j * (sqrt2 ^ kSO3 M * blochEntry M i l))
      = sqrt2 ^ kSO3 M * sqrt2 ^ kSO3 M * ∑ i, blochEntry M i j * blochEntry M i l from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring,
    hδ, hsq]
  by_cases hjl : j = l
  · rw [if_pos hjl, if_pos hjl, mul_one]
  · rw [if_neg hjl, if_neg hjl, mul_zero, ZOmegaSqrt2.of_zero]

end KMM

end SKEFTHawking.RossSelinger
