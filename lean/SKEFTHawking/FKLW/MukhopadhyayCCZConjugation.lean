/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ Phase 2 (C.1) — the CCZ diagonal-conjugation identity

Mukhopadhyay 2024 (arXiv:2401.08950) Theorem 3.8 describes the channel-representation row structure of a
`CCZ`/Toffoli generator. The structural engine behind it is the fact that `CCZ` is **diagonal** in the
computational basis (`CCZ_mat = diagonal (i ↦ −1 if i = |111⟩ else +1)`), so conjugation by `CCZ` acts
**entrywise**:

  `(CCZ · M · CCZ)_{ij} = ccz_i · ccz_j · M_{ij}`     (`CCZ_mat_conj_apply`)

This is the "diagonal-entrywise route" (vs. multi-`X` Pauli-product gymnastics) for computing the channel
rep of `CCZ`. Two immediate consequences shipped here:

  * **`CCZ` commutes with every diagonal operator** (`CCZ_conj_diagonal`): `CCZ · D · CCZ = D` for
    diagonal `D` (since `ccz_i² = 1`). In particular `CCZ` fixes every *diagonal* (Z-type, i.e. `I`/`Z`
    tensor) Pauli under conjugation — these are the `2^{2n−3} = 8` rows of `Ĉ_{CCZ}` that are a single
    `+1` (Theorem 3.8.4).

## Scope (off-ramp, Phase 6x′ roadmap "Highest-risk step")

This file ships the C.1 substrate. The **full** Theorem 3.8 row structure for the *off-diagonal*
(`X`/`Y`-containing) Paulis — `Ĉ_{CCZ}` rows of four `±1/2` entries — and the downstream `hCCZ`
(`sde₂(Ĉ_{CCZ}·M) ≤ sde₂(M) + 1`), Lemma 3.10 (`ℤ[1/2]` entries), and the consequent *unconditional*
`T^of(U) ≥ sde₂(Û)` (discharging the `PARAMETRIC` hypotheses of `toffoliCost_ge_measure`) remain a
**documented residual**: they require both the 64-Pauli entry-table computation (Theorem 3.8, DR-rated
"Medium", with delicate complex-entry bookkeeping) and a total `sde₂`-valued measure on `ℂ`-matrices
(extracting dyadic exponents from arbitrary `ℂ` entries). The Phase-6x′ capstone (`cliffordOnly_not_dense`,
the 6z CCZ-essentiality converse) is the shipped headline; the unconditional `T^of` bound is a marginal
`PARAMETRIC → unconditional` upgrade on a non-tight lower bound (full minimality is out of scope per the
Mukhopadhyay dossier regardless), so it is deferred rather than ground out.

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected. Kernel-pure.

-/

import SKEFTHawking.FKLW.CliffordCCZAlphabet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZ (CCZ_mat)

/-- The diagonal of `CCZ`: `−1` at the `|111⟩` index `7`, `+1` elsewhere. -/
def cczDiag : Fin 8 → ℂ := fun i => if i = (⟨7, by decide⟩ : Fin 8) then (-1 : ℂ) else 1

/-- `CCZ_mat` is the diagonal matrix of `cczDiag` (definitional). -/
theorem CCZ_mat_eq_diagonal : CCZ_mat = Matrix.diagonal cczDiag := rfl

/-- Each `cczDiag` entry squares to `1` (it is `±1`-valued). -/
theorem cczDiag_mul_self (i : Fin 8) : cczDiag i * cczDiag i = 1 := by
  unfold cczDiag
  split <;> ring

/-- **The CCZ diagonal-conjugation identity (C.1)**: since `CCZ` is diagonal, conjugation by `CCZ` acts
entrywise — `(CCZ · M · CCZ)_{ij} = ccz_i · ccz_j · M_{ij}`. The structural engine behind Theorem 3.8's
channel-rep computation. -/
theorem CCZ_mat_conj_apply (M : Matrix (Fin 8) (Fin 8) ℂ) (i j : Fin 8) :
    (CCZ_mat * M * CCZ_mat) i j = cczDiag i * cczDiag j * M i j := by
  rw [CCZ_mat_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- **CCZ commutes with every diagonal operator**: `CCZ · D · CCZ = D` for diagonal `D` (because
`ccz_i² = 1`). In particular, conjugation by `CCZ` fixes every diagonal (`Z`-type) Pauli — the
single-`+1` rows of the CCZ channel representation (Theorem 3.8.4). -/
theorem CCZ_conj_diagonal (d : Fin 8 → ℂ) :
    CCZ_mat * Matrix.diagonal d * CCZ_mat = Matrix.diagonal d := by
  ext i j
  rw [CCZ_mat_conj_apply]
  rcases eq_or_ne i j with h | h
  · subst h
    rw [Matrix.diagonal_apply_eq, cczDiag_mul_self, one_mul]
  · rw [Matrix.diagonal_apply_ne _ h, mul_zero]

end SKEFTHawking.FKLW.MukhopadhyayCCZ
