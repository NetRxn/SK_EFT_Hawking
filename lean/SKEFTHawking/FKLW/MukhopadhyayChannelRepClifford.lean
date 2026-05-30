/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ — Fact 3.9 (⟹): the channel rep of a Clifford generator is a signed permutation (B)

Mukhopadhyay 2024 (arXiv:2401.08950) Fact 3.9: a unitary is an exactly-implementable Clifford iff its
channel representation has exactly one `±1` per row and column (a *signed permutation*). This file ships
the **⟹ direction** for the literal Clifford generators (`H_qi`, `S_qi`, `CNOT_ij`), via the shipped
Phase-6z conjugation tables (`hsu_q{1,2,3}_kronK8_conj`, `ssu_q{1,2,3}_kronK8_conj`,
`cnot{12,13,23}_kronK8_conj`): each generator conjugates every Pauli to `± a Pauli`, so its channel rep
is a signed monomial matrix.

The general bridge: if `U·P_v·Uᴴ = ε(v)·P_{σ(v)}` for all Pauli labels `v` (some label map `σ` and sign
`ε`), then `channelRep U r s = if r = σ s then ε s else 0` — a signed monomial column. With `σ` a
bijection (each generator's label map is) and `ε` valued in `{±1}`, this is a signed permutation
(Fact 3.9 ⟹). This is the substrate for: the `hC` bridge (Clifford preserves `sde₂`) of the Item-L
`T^of ≥ sde₂` bound, and the 6z CCZ-essentiality converse (Clifford-only maps into the finite
signed-permutation group, hence is not dense).

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.MukhopadhyayChannelRep
import SKEFTHawking.FKLW.CliffordCCZSU8GenLift
import SKEFTHawking.FKLW.CliffordCCZSU8CNOTConj

set_option autoImplicit false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZSU8 (kronK8 kronK8Basis kronK8_mul_trace kronK8Basis_repr_eq)
open SKEFTHawking.FKLW.CliffordCCZSU8
open SKEFTHawking.FKLW.GenericSU2 (H_SU)

/-- The Pauli-basis coordinate of a basis Pauli is the indicator: `repr (P_t) r = 𝟙[r = t]`.
(Via the HS coordinate formula + Pauli orthogonality `Tr(P_r·P_t) = 8·𝟙[r=t]`.) -/
theorem kronK8Basis_repr_self (t r : Fin 4 × Fin 4 × Fin 4) :
    kronK8Basis.repr (kronK8 t) r = if r = t then 1 else 0 := by
  rw [kronK8Basis_repr_eq, kronK8_mul_trace]
  by_cases h : r = t <;> simp [h]

/-- **Signed-monomial channel rep from a signed-permutation conjugation.** If a unitary `U` conjugates
every Pauli to `± a Pauli` — `U·P_v·Uᴴ = ε(v)·P_{σ(v)}` — then its channel representation is the signed
monomial matrix `Û_{rs} = if r = σ s then ε s else 0` (one nonzero per column). This is the matrix form
of Fact 3.9's ⟹ direction. -/
theorem channelRep_eq_signedMonomial {U : Matrix (Fin 8) (Fin 8) ℂ}
    {σ : (Fin 4 × Fin 4 × Fin 4) → (Fin 4 × Fin 4 × Fin 4)} {ε : (Fin 4 × Fin 4 × Fin 4) → ℂ}
    (hconj : ∀ v, U * kronK8 v * Uᴴ = ε v • kronK8 (σ v)) (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep U r s = if r = σ s then ε s else 0 := by
  show kronK8Basis.repr (U * kronK8 s * Uᴴ) r = _
  rw [hconj s, map_smul, Finsupp.smul_apply, kronK8Basis_repr_self, smul_eq_mul]
  by_cases h : r = σ s <;> simp [h]

/-- For `M ∈ SU(8)`, the conjugate transpose equals the inverse (`Mᴴ = M⁻¹`) — unitarity. Bridges the
shipped conjugation tables (stated with `M⁻¹`) to `channelRep`'s `Mᴴ`. -/
theorem su8val_conjTranspose_eq_inv (M : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) :
    (M : Matrix (Fin 8) (Fin 8) ℂ)ᴴ = (M : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ := by
  have hu : (M : Matrix (Fin 8) (Fin 8) ℂ) ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp M.2).1
  have h1 : (M : Matrix (Fin 8) (Fin 8) ℂ)ᴴ * (M : Matrix (Fin 8) (Fin 8) ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hu
  exact (Matrix.inv_eq_left_inv h1).symm

/-- A permutation matrix is unitary: its conjugate transpose is the permutation-matrix of the inverse
(`(permMatrix σ)ᴴ = permMatrix σ⁻¹`). Bridges the CNOT conjugation tables (stated with `permMatrix σ⁻¹`)
to `channelRep`'s `Uᴴ`. -/
theorem permMatrix_fin8_conjTranspose (σ : Equiv.Perm (Fin 8)) :
    (Equiv.Perm.permMatrix ℂ σ)ᴴ = Equiv.Perm.permMatrix ℂ σ⁻¹ := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.conjTranspose_apply,
    Equiv.toPEquiv_apply, Equiv.eq_symm_apply, eq_comm]

/-! ## Fact 3.9 (⟹) for each Clifford generator: `channelRep g` is a signed monomial

Each literal Clifford generator conjugates every Pauli to `± a Pauli`, so its channel rep is a signed
monomial matrix `Û_{rs} = if r = σ_g s then ε_g s else 0` with `ε_g ∈ {±1}` and `σ_g` the generator's
label permutation. (`onQubit hLabel/sLabel` swaps `X↔Z` / `X↔Y` on one qubit; `cnotLabel` is the CNOT
symplectic relabel.) These are the matrix realizations of Fact 3.9's ⟹ direction for `{H_qi,S_qi,CNOT_ij}`. -/

/-- **`H₁` channel rep is a signed monomial** (Fact 3.9 ⟹). -/
theorem channelRep_hsu_q1 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (qubit1Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) r s
      = if r = onQubit hLabel 0 s then hSign s.1 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [su8val_conjTranspose_eq_inv]; exact hsu_q1_kronK8_conj v) r s

/-- **`H₂` channel rep is a signed monomial**. -/
theorem channelRep_hsu_q2 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (qubit2Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) r s
      = if r = onQubit hLabel 1 s then hSign s.2.1 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [su8val_conjTranspose_eq_inv]; exact hsu_q2_kronK8_conj v) r s

/-- **`H₃` channel rep is a signed monomial**. -/
theorem channelRep_hsu_q3 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (qubit3Embed H_SU : Matrix (Fin 8) (Fin 8) ℂ) r s
      = if r = onQubit hLabel 2 s then hSign s.2.2 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [su8val_conjTranspose_eq_inv]; exact hsu_q3_kronK8_conj v) r s

/-- **`S₁` channel rep is a signed monomial**. -/
theorem channelRep_ssu_q1 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (qubit1Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) r s
      = if r = onQubit sLabel 0 s then sSign s.1 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [su8val_conjTranspose_eq_inv]; exact ssu_q1_kronK8_conj v) r s

/-- **`S₂` channel rep is a signed monomial**. -/
theorem channelRep_ssu_q2 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (qubit2Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) r s
      = if r = onQubit sLabel 1 s then sSign s.2.1 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [su8val_conjTranspose_eq_inv]; exact ssu_q2_kronK8_conj v) r s

/-- **`S₃` channel rep is a signed monomial**. -/
theorem channelRep_ssu_q3 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (qubit3Embed S_SU : Matrix (Fin 8) (Fin 8) ℂ) r s
      = if r = onQubit sLabel 2 s then sSign s.2.2 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [su8val_conjTranspose_eq_inv]; exact ssu_q3_kronK8_conj v) r s

/-- **`CNOT₁₂` channel rep is a signed monomial**. -/
theorem channelRep_cnot12 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (Equiv.Perm.permMatrix ℂ σ_cnot_12) r s
      = if r = cnotLabel 0 1 s then cnotSign s.1 s.2.1 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [permMatrix_fin8_conjTranspose]; exact cnot12_kronK8_conj v) r s

/-- **`CNOT₁₃` channel rep is a signed monomial**. -/
theorem channelRep_cnot13 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (Equiv.Perm.permMatrix ℂ σ_cnot_13) r s
      = if r = cnotLabel 0 2 s then cnotSign s.1 s.2.2 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [permMatrix_fin8_conjTranspose]; exact cnot13_kronK8_conj v) r s

/-- **`CNOT₂₃` channel rep is a signed monomial**. -/
theorem channelRep_cnot23 (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep (Equiv.Perm.permMatrix ℂ σ_cnot_23) r s
      = if r = cnotLabel 1 2 s then cnotSign s.2.1 s.2.2 else 0 :=
  channelRep_eq_signedMonomial
    (fun v => by rw [permMatrix_fin8_conjTranspose]; exact cnot23_kronK8_conj v) r s

end SKEFTHawking.FKLW.MukhopadhyayCCZ
