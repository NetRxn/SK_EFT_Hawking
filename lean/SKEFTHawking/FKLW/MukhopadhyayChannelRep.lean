/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Item L.A — Mukhopadhyay channel representation (public math layer), increment L.A.1

Mukhopadhyay 2024 (arXiv:2401.08950) synthesizes Toffoli-optimal Clifford+Toffoli circuits by working
in the **channel (Heisenberg / Pauli-conjugation) representation** of a unitary `U` rather than with
`U` itself. For an `n`-qubit unitary `U`, its channel representation `Û` is the `4ⁿ × 4ⁿ` real matrix
whose action records how `U` conjugates each Pauli `P_s` into a linear combination of Paulis `P_r`
(arXiv:2401.08950 Eq. 27):

  `U · P_s · U† = ∑_{P_r} Û_{rs} · P_r`,   with   `Û_{rs} = (1/2ⁿ) · Tr(P_r · U · P_s · U†)`.

For `n = 3` this is the `64 × 64` matrix indexed by the 64 three-qubit Paulis `kronK8 p`
(`p : Fin 4 × Fin 4 × Fin 4`), already shipped (with their Hilbert–Schmidt orthogonality
`kronK8_mul_trace`, their basis `kronK8Basis`, and the HS coordinate formula `kronK8Basis_repr_eq`)
in the Phase-6z SU(8) density layer. The channel-rep entry `Û_{rs}` is *exactly* the `r`-th
`kronK8Basis` coordinate of the conjugate `U · P_s · U†`, so the construction is a thin layer over the
shipped Pauli basis.

This increment (L.A.1) ships:

  - **`channelRep`** — the channel representation as a `(Fin 4 × Fin 4 × Fin 4)`-indexed matrix over
    `ℂ`, defined via `kronK8Basis.repr` (the HS coordinate), with `channelRep_eq_trace` recovering
    Mukhopadhyay's Eq. 27 trace form `Û_{rs} = (1/8) · Tr(P_r · U · P_s · U†)`.
  - **`channelRep_conjAction_eq`** — the resolution `U · P_s · U† = ∑_t (Û_{ts}) · P_t` (the channel
    rep IS the coordinate vector of the conjugated Pauli; Eq. 27 read as an identity).
  - **The monoid-homomorphism law** (arXiv:2401.08950 §3.3, "(UW)̂ = Û·Ŵ"): `channelRep_one`
    (`1̂ = 1`) and `channelRep_mul` (`(U·W)̂ = Û · Ŵ`). This is the algebraic backbone of the whole
    reduction: it lets the synthesis work entirely in `64 × 64` channel-rep land.

Ring picture (per the Phase-6x Mukhopadhyay dossier, Q6): the exactly-implementable `SU(8)` *matrices*
live over the shipped `ℤ[ω][1/√2] = ZOmegaSqrt2`, while the *channel rep* `Û` of a Clifford+Toffoli `U`
has entries in the dyadic ring `ℤ[1/2]` (Lemma 3.10) — no `√2`. The dyadic `sde₂` invariant
(Definition 3.13) is the `√2 → 2` analog of the shipped `√2`-`sde` T-count invariant. This file builds
the channel-rep substrate; the dyadic-entry necessary condition and the Fact 3.9 Clifford base case
are the next increments (L.A.2).

PUBLIC math layer only (per the Item-L brief): no private-repo content.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.CliffordCCZSU8TangentSpan
import SKEFTHawking.FKLW.MukhopadhyayCCZ

set_option autoImplicit false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZSU8 (kronK8 kronK8Basis kronK8_mul_trace kronK8Basis_sum_repr
  kronK8Basis_repr_eq)

/-- **The channel (Heisenberg / Pauli-conjugation) representation** of an `8×8` unitary `U`
(arXiv:2401.08950 Eq. 27), as the `64 × 64` matrix indexed by the 64 three-qubit Paulis
`kronK8 r, kronK8 s` (`r, s : Fin 4 × Fin 4 × Fin 4`). The `(r, s)` entry is the `r`-th Pauli-basis
coordinate of the conjugate `U · P_s · U†`, i.e. `Û_{rs} = (1/8) · Tr(P_r · U · P_s · U†)`
(see `channelRep_eq_trace`). -/
noncomputable def channelRep (U : Matrix (Fin 8) (Fin 8) ℂ) :
    Matrix (Fin 4 × Fin 4 × Fin 4) (Fin 4 × Fin 4 × Fin 4) ℂ :=
  fun r s => kronK8Basis.repr (U * kronK8 s * Uᴴ) r

/-- **Eq. 27 trace form**: `Û_{rs} = (1/8) · Tr(P_r · U · P_s · U†)` — the channel-rep entry as the
Hilbert–Schmidt coordinate of the conjugated Pauli. -/
theorem channelRep_eq_trace (U : Matrix (Fin 8) (Fin 8) ℂ) (r s : Fin 4 × Fin 4 × Fin 4) :
    channelRep U r s = (8⁻¹ : ℂ) * (kronK8 r * (U * kronK8 s * Uᴴ)).trace := by
  simp only [channelRep]
  exact kronK8Basis_repr_eq _ _

/-- **The resolution `U · P_s · U† = ∑_t Û_{ts} · P_t`** (Eq. 27 read as an identity): the conjugated
Pauli `U · P_s · U†` is reconstructed from its channel-rep column `t ↦ Û_{ts}` against the Pauli
basis. This is the bridge that lets the homomorphism law (`channelRep_mul`) collapse to basis
linearity. -/
theorem channelRep_conjAction_eq (U : Matrix (Fin 8) (Fin 8) ℂ) (s : Fin 4 × Fin 4 × Fin 4) :
    U * kronK8 s * Uᴴ = ∑ t, channelRep U t s • kronK8 t := by
  conv_lhs => rw [← kronK8Basis_sum_repr (U * kronK8 s * Uᴴ)]
  rfl

/-- **`1̂ = 1`**: the channel representation of the identity is the identity (arXiv:2401.08950 §3.3).
Via Eq. 27 and the Pauli orthogonality `Tr(P_r · P_s) = 8·𝟙[r = s]`. -/
theorem channelRep_one : channelRep (1 : Matrix (Fin 8) (Fin 8) ℂ) = 1 := by
  ext r s
  rw [channelRep_eq_trace]
  simp only [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, kronK8_mul_trace,
    Matrix.one_apply]
  by_cases h : r = s
  · simp [h]
  · simp [h]

/-- **The channel-representation homomorphism law `(U·W)̂ = Û · Ŵ`** (arXiv:2401.08950 §3.3): the
channel representation respects matrix multiplication. Proof: `(UW) P_s (UW)† = U (W P_s W†) U†`;
expand `W P_s W† = ∑_t Ŵ_{ts} P_t` (the resolution `channelRep_conjAction_eq`); conjugate by `U` and
read off the `r`-th coordinate by linearity of the Hilbert–Schmidt trace. -/
theorem channelRep_mul (U W : Matrix (Fin 8) (Fin 8) ℂ) :
    channelRep (U * W) = channelRep U * channelRep W := by
  ext r s
  rw [Matrix.mul_apply, channelRep_eq_trace, Matrix.conjTranspose_mul,
    show U * W * kronK8 s * (Wᴴ * Uᴴ) = U * (W * kronK8 s * Wᴴ) * Uᴴ from by
      simp only [Matrix.mul_assoc],
    channelRep_conjAction_eq W s]
  have hdist : U * (∑ t, channelRep W t s • kronK8 t) * Uᴴ
      = ∑ t, channelRep W t s • (U * kronK8 t * Uᴴ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by
      rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hdist, Finset.mul_sum, Matrix.trace_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, channelRep_eq_trace U r t]
    ring

/-! ## Channel rep of a unitary is orthogonal; the gate-word bridge (increment L.A.2a) -/

/-- **`Û · (Uᴴ)̂ = 1` for unitary `U`** (`U·Uᴴ = 1`): immediate from the homomorphism law
(`channelRep_mul`) and `channelRep_one`. Together with `channelRep_conjTranspose_mul` this says the
channel rep of a unitary is invertible with inverse `(Uᴴ)̂` — the matrix form of "`Û` is real
orthogonal" (arXiv:2401.08950 §3.3, "(U†)̂ = (Û)†, Û unitary"). -/
theorem channelRep_mul_conjTranspose (U : Matrix (Fin 8) (Fin 8) ℂ) (hU : U * Uᴴ = 1) :
    channelRep U * channelRep Uᴴ = 1 := by
  rw [← channelRep_mul, hU, channelRep_one]

/-- **`(Uᴴ)̂ · Û = 1` for unitary `U`** (`Uᴴ·U = 1`): the other inverse identity. -/
theorem channelRep_conjTranspose_mul (U : Matrix (Fin 8) (Fin 8) ℂ) (hU : Uᴴ * U = 1) :
    channelRep Uᴴ * channelRep U = 1 := by
  rw [← channelRep_mul, hU, channelRep_one]

/-- **The channel rep of a unitary is a unit** (invertible `64×64` matrix), with inverse `(Uᴴ)̂` —
the matrix form of "the channel representation `Û` is orthogonal" (arXiv:2401.08950 §3.3). -/
theorem channelRep_isUnit (U : Matrix (Fin 8) (Fin 8) ℂ) (hU1 : U * Uᴴ = 1) (hU2 : Uᴴ * U = 1) :
    IsUnit (channelRep U) :=
  ⟨⟨channelRep U, channelRep Uᴴ, channelRep_mul_conjTranspose U hU1,
      channelRep_conjTranspose_mul U hU2⟩, rfl⟩

/-- **The channel rep is multiplicative over gate-word concatenation**: `(interp (gs ++ hs))̂ =
(interp gs)̂ · (interp hs)̂`. The bridge from the Clifford+CCZ gate alphabet (`interp`,
`interp_append`) into channel-rep land — used to push the dyadic-entry (Lemma 3.10) and Fact-3.9
structure through a synthesized gate word by induction. -/
theorem channelRep_interp_append (gs hs : List CliffordCCZGate) :
    channelRep (interp (gs ++ hs)) = channelRep (interp gs) * channelRep (interp hs) := by
  rw [interp_append, channelRep_mul]

end SKEFTHawking.FKLW.MukhopadhyayCCZ
