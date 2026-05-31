/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ Phase 2 (C) — the channel representation of CCZ has half-integer entries (Theorem 3.8)

For the unconditional Toffoli bound, the one fact `hCCZ` needs about `Ĉ := channelRep CCZ` is that
**every entry is a half-integer** (`2·entry ∈ ℤ`): then each product entry
`(Ĉ · X)_{rs} = (1/2)·(integer combination of X entries)`, so `sde₂` rises by at most one. This is
Mukhopadhyay Theorem 3.8 (`Ĉ_CCZ` entries `∈ {0, ±1, ±1/2}`), packaged as the weaker "half-integer"
statement the `sde₂` bound consumes (no `8`-vs-`56` row count needed).

The tractable route (no `4096`-case bash): the `|111⟩` index is `7 = bitIso8 (1,1,1)`, and `kronK8`
factors entrywise over the three qubits (`kronK8_bitIso8_apply`), so
`(P_r · P_s)₇₇ = ∏ᵢ (σ_{rᵢ} σ_{sᵢ})₁₁` (`kronK8_mul_apply_77`). Since the single-qubit Paulis are
Hermitian, `(σ_b σ_a)₁₁ = conj((σ_a σ_b)₁₁)` (`pauliProd11_conj_swap`). This file ships that
entry-factorization + conjugate-swap foundation; the Gaussian-integer structure, the
`CCZ = 1 − 2|111⟩⟨111|` closed form, and the half-integer headline follow in subsequent increments.

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected. Kernel-pure.

-/

import SKEFTHawking.FKLW.MukhopadhyayCCZConjugation
import SKEFTHawking.FKLW.CliffordCCZSU8CNOTConj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZSU8
open SKEFTHawking.FKLW.TrappedIonSU4

/-! ## C.1 — entry factorization at the `|111⟩` index `7` -/

/-- **General `kronSU8` bit-entry formula** (the `kronK8_bitIso8_apply` analog for arbitrary factors). -/
theorem kronSU8_bitIso8_apply (A B C : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2 × Fin 2 × Fin 2) :
    kronSU8 A B C (bitIso8 i) (bitIso8 j) = A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2 j.2.2 := by
  unfold kronSU8 kronSU2SU4 kronSU4 bitIso8
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id_eq,
    Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

/-- The `|111⟩` computational-basis index is `bitIso8 (1,1,1) = 7`. -/
theorem bitIso8_one_one_one : bitIso8 (1, 1, 1) = 7 := by decide

/-- **`(P_v)₇₇` factors over qubits**: `(kronK8 v)₇₇ = ∏ᵢ (σ_{vᵢ})₁₁`. -/
theorem kronK8_apply_77 (v : Fin 4 × Fin 4 × Fin 4) :
    kronK8 v 7 7 = pauli4 v.1 1 1 * pauli4 v.2.1 1 1 * pauli4 v.2.2 1 1 := by
  rw [← bitIso8_one_one_one, kronK8_bitIso8_apply]

/-- **`(P_r · P_s)₇₇` factors over qubits**: `= ∏ᵢ (σ_{rᵢ} σ_{sᵢ})₁₁`. -/
theorem kronK8_mul_apply_77 (r s : Fin 4 × Fin 4 × Fin 4) :
    (kronK8 r * kronK8 s) 7 7
      = (pauli4 r.1 * pauli4 s.1) 1 1 * (pauli4 r.2.1 * pauli4 s.2.1) 1 1
          * (pauli4 r.2.2 * pauli4 s.2.2) 1 1 := by
  rw [← bitIso8_one_one_one, kronK8, kronK8, ← kronSU8_mul, kronSU8_bitIso8_apply]

/-! ## C.2 — the per-qubit product entry: conjugate-swap -/

/-- **Hermitian swap**: `(σ_b σ_a)₁₁ = conj((σ_a σ_b)₁₁)` — since the single-qubit Paulis are Hermitian,
`σ_b σ_a = (σ_a σ_b)ᴴ`, and conjugate-transpose conjugates a diagonal entry. -/
theorem pauliProd11_conj_swap (a b : Fin 4) :
    (pauli4 b * pauli4 a) 1 1 = (starRingEnd ℂ) ((pauli4 a * pauli4 b) 1 1) := by
  have h : pauli4 b * pauli4 a = (pauli4 a * pauli4 b)ᴴ := by
    rw [Matrix.conjTranspose_mul, pauli4_hermitian, pauli4_hermitian]
  rw [h, Matrix.conjTranspose_apply, starRingEnd_apply]

end SKEFTHawking.FKLW.MukhopadhyayCCZ
