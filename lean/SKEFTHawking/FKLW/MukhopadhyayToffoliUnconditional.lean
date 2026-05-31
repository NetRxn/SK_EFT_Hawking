/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ Phase 2 (B, then D/E/F) — toward the unconditional Toffoli bound `T^of(U) ≥ sde₂(Û)`

This file discharges the per-generator bridges of the parametric `toffoliCost_ge_measure`
(`MukhopadhyayToffoliBound.lean`) for `μ = channelSde2 = matrixSde2 ∘ channelRep`, and assembles the
**unconditional** lower bound. Increment B (here): the `hC` bridge — Cliffords leave the measure
unchanged, because each Clifford generator's channel rep is a signed permutation (Fact 3.9), and
left-multiplication by a signed permutation just permutes/sign-flips entries (so the per-entry `sde₂`
multiset, hence its max `matrixSde2`, is preserved). Increments D/E/F (CCZ row structure → `hCCZ`,
Lemma 3.10, final instantiation) follow once the CCZ channel-rep structure (C) lands.

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected. Kernel-pure.

-/

import SKEFTHawking.FKLW.MukhopadhyayMatrixSde2
import SKEFTHawking.FKLW.MukhopadhyayCliffordConverse
import SKEFTHawking.FKLW.MukhopadhyayToffoliBound
import SKEFTHawking.FKLW.MukhopadhyayCCZChannelRep
import SKEFTHawking.FKLW.MukhopadhyayHCCZ

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZ (CCZ_mat)

/-! ## B.1 — left-multiplication by a signed permutation preserves `matrixSde2` -/

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The `(r,s)` entry of `signedPermMatrix σ ε * X` is `ε(σ⁻¹ r) · X(σ⁻¹ r, s)` — one term survives
(the signed permutation has a single nonzero per row). -/
theorem signedPermMatrix_mul_apply (σ : Equiv.Perm L) (ε : L → ℂ) (X : Matrix L L ℂ) (r s : L) :
    (signedPermMatrix σ ε * X) r s = ε (σ⁻¹ r) * X (σ⁻¹ r) s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ⁻¹ r)]
  · simp [signedPermMatrix]
  · intro t _ ht
    have hne : r ≠ σ t := fun h => ht (by simp [h])
    simp only [signedPermMatrix, if_neg hne, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`hC` core**: left-multiplication by a signed permutation does not raise `matrixSde2` (it permutes
rows and multiplies by `±1`, preserving each entry's dyadic exponent). -/
theorem matrixSde2_signedPerm_mul_le {P : Matrix L L ℂ} (hP : IsSignedPerm P) (X : Matrix L L ℂ) :
    matrixSde2 (P * X) ≤ matrixSde2 X := by
  obtain ⟨σ, ε, hε, rfl⟩ := hP
  refine Finset.sup_le fun r _ => Finset.sup_le fun s _ => ?_
  rw [signedPermMatrix_mul_apply]
  rcases hε (σ⁻¹ r) with h | h
  · rw [h, one_mul]; exact sde2ℂ_le_matrixSde2 X (σ⁻¹ r) s
  · rw [h, neg_one_mul, sde2ℂ_neg]; exact sde2ℂ_le_matrixSde2 X (σ⁻¹ r) s

/-! ## B.2 — the `hC` bridge for the gate alphabet -/

/-- The Clifford gate matrices agree with the Clifford-only generating map (the first 9 generators). -/
theorem gateMatrix_clifford_eq (c : Fin 9) :
    gateMatrix (CliffordCCZGate.clifford c) = (cliffordOnlyGenMap c).val := by
  fin_cases c <;> rfl

/-- Each Clifford gate's channel rep is a signed permutation (Fact 3.9, re-based onto `gateMatrix`). -/
theorem gateMatrix_clifford_channelRep_isSignedPerm (c : Fin 9) :
    IsSignedPerm (channelRep (gateMatrix (CliffordCCZGate.clifford c))) := by
  rw [gateMatrix_clifford_eq]
  exact channelRep_cliffordOnlyGen_isSignedPerm c

/-- **`hC`**: every Clifford generator leaves the channel-rep `sde₂` measure unchanged (does not raise
it). Discharges the `hC` hypothesis of `toffoliCount_ge_measure` for `μ = channelSde2`. -/
theorem channelSde2_clifford_le (c : Fin 9) (M : Matrix (Fin 8) (Fin 8) ℂ) :
    channelSde2 (gateMatrix (CliffordCCZGate.clifford c) * M) ≤ channelSde2 M := by
  rw [channelSde2, channelSde2, channelRep_mul]
  exact matrixSde2_signedPerm_mul_le (gateMatrix_clifford_channelRep_isSignedPerm c) (channelRep M)

/-! ## E — Lemma 3.10: every Clifford+CCZ word's channel rep has rational (dyadic) entries -/

theorem isRatℂ_one : IsRatℂ 1 := ⟨1, by simp⟩

theorem isRatℂ_mul {z w : ℂ} (hz : IsRatℂ z) (hw : IsRatℂ w) : IsRatℂ (z * w) := by
  obtain ⟨p, rfl⟩ := hz; obtain ⟨q, rfl⟩ := hw
  exact ⟨p * q, by push_cast; ring⟩

/-- A signed permutation has rational (in fact `{0, ±1}`) entries. -/
theorem isSignedPerm_entry_isRat {P : Matrix L L ℂ} (hP : IsSignedPerm P) (i j : L) :
    IsRatℂ (P i j) := by
  obtain ⟨σ, ε, hε, rfl⟩ := hP
  simp only [signedPermMatrix]
  by_cases h : i = σ j
  · rw [if_pos h]; rcases hε j with hh | hh <;> rw [hh]
    · exact isRatℂ_one
    · exact ⟨-1, by push_cast; ring⟩
  · rw [if_neg h]; exact isRatℂ_zero

/-- The channel rep of `CCZ` has rational entries (half-integers). -/
theorem channelRep_CCZ_isRat (r s : Fin 4 × Fin 4 × Fin 4) :
    IsRatℂ (channelRep CCZ_mat r s) := by
  obtain ⟨a, ha⟩ := channelRep_CCZ_isHalfInt r s
  exact ⟨(a : ℚ) / 2, by rw [ha]; push_cast; ring⟩

/-- Matrix multiplication preserves rational entries. -/
theorem isRatℂ_matrix_mul {n : Type*} [Fintype n] {A B : Matrix n n ℂ}
    (hA : ∀ i j, IsRatℂ (A i j)) (hB : ∀ i j, IsRatℂ (B i j)) (i j : n) :
    IsRatℂ ((A * B) i j) := by
  rw [Matrix.mul_apply]
  exact isRatℂ_sum _ _ fun k _ => isRatℂ_mul (hA i k) (hB k j)

/-- **Lemma 3.10 (rational form)**: every Clifford+CCZ gate word's channel rep has rational entries (each
entry lies in `ℤ[1/2] ⊂ ℚ`). By induction: the identity is `{0,1}`-valued, each Clifford generator's
channel rep is a signed permutation (`{0,±1}`), `CCZ`'s is half-integer, and matrix multiplication
preserves rationality. This supplies the rationality hypothesis of `hCCZ`. -/
theorem channelRep_interp_isRat (gs : List CliffordCCZGate) (r s : Fin 4 × Fin 4 × Fin 4) :
    IsRatℂ (channelRep (interp gs) r s) := by
  induction gs generalizing r s with
  | nil =>
    rw [interp_nil, channelRep_one, Matrix.one_apply]
    by_cases h : r = s
    · rw [if_pos h]; exact isRatℂ_one
    · rw [if_neg h]; exact isRatℂ_zero
  | cons g gs ih =>
    rw [interp_cons, channelRep_mul]
    cases g with
    | clifford c =>
      exact isRatℂ_matrix_mul
        (fun i j => isSignedPerm_entry_isRat (gateMatrix_clifford_channelRep_isSignedPerm c) i j)
        (fun i j => ih i j) r s
    | ccz =>
      exact isRatℂ_matrix_mul (fun i j => channelRep_CCZ_isRat i j) (fun i j => ih i j) r s

/-! ## F — the unconditional Toffoli lower bound `T^of(U) ≥ sde₂(Û)` -/

/-- **The telescoping Toffoli bound (unconditional, threaded through Lemma 3.10).** Every Clifford+CCZ
gate word `gs` satisfies `sde₂((interp gs)̂) ≤ toffoliCount gs`: Cliffords leave `sde₂` unchanged (`hC`),
each `CCZ` raises it by at most one (`hCCZ`, whose rationality hypothesis is discharged by
`channelRep_interp_isRat`), and a Clifford base has `sde₂ = 0`. -/
theorem toffoliCount_ge_channelSde2 (gs : List CliffordCCZGate) :
    channelSde2 (interp gs) ≤ toffoliCount gs := by
  induction gs with
  | nil => rw [interp_nil, channelSde2_one]; exact Nat.zero_le _
  | cons g gs ih =>
    rw [interp_cons]
    cases g with
    | clifford c =>
      rw [toffoliCount_clifford]
      exact le_trans (channelSde2_clifford_le c (interp gs)) ih
    | ccz =>
      rw [toffoliCount_ccz, show gateMatrix CliffordCCZGate.ccz = CCZ_mat from rfl]
      exact le_trans (channelSde2_ccz_le (interp gs) (fun t s => channelRep_interp_isRat gs t s))
        (Nat.add_le_add_right ih 1)

/-- **UNCONDITIONAL Toffoli-count lower bound `T^of(U) ≥ sde₂(Û)`** (Mukhopadhyay, the discharged form of
the parametric `toffoliCost_ge_measure`): every exactly-Clifford+CCZ-representable unitary `U` requires at
least `sde₂(Û)` Toffoli (`CCZ`) gates, where `sde₂(Û) = channelSde2 U` is the dyadic smallest-denominator
exponent of the channel representation. NOT proved tight — full Toffoli minimality (no shorter circuit)
needs the intractable meet-in-the-middle search (Conjecture 4.8), the documented residual. -/
theorem channelSde2_le_toffoliCost {U : Matrix (Fin 8) (Fin 8) ℂ} (hU : IsExactlyCliffordCCZ U) :
    channelSde2 U ≤ toffoliCost U := by
  apply le_csInf
  · obtain ⟨gs, hgs⟩ := hU; exact ⟨toffoliCount gs, gs, hgs, rfl⟩
  · rintro b ⟨gs, hgs, rfl⟩
    rw [← hgs]
    exact toffoliCount_ge_channelSde2 gs

end SKEFTHawking.FKLW.MukhopadhyayCCZ
