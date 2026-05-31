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

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix

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

end SKEFTHawking.FKLW.MukhopadhyayCCZ
