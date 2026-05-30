/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Item L — Mukhopadhyay exact Clifford+CCZ synthesis (public math layer), increment 1

Mukhopadhyay 2024 (arXiv:2401.08950, "Synthesizing Toffoli-optimal quantum circuits for arbitrary
multi-qubit unitaries") gives a Toffoli/CS-count-optimal EXACT synthesis for the Clifford+Toffoli
gate set, which is Clifford-equivalent to Clifford+CCZ (Toffoli = `(I⊗I⊗H)·CCZ·(I⊗I⊗H)`). Its
exact-synthesis backbone (Thm 3.2) decomposes any exactly-implementable `U` as
`U = e^{iφ}·(∏_j G_{Pⱼ,Qⱼ,Rⱼ})·C₀` with `C₀` Clifford and each `G_{P,Q,R}` a *generating element*

  `G_{P,Q,R} = (3/4)·I + (1/4)·(P + Q + R − PQ − QR − RP + PQR)`        (Mukhopadhyay Eq. 12)

over a triple of pairwise-commuting non-identity Paulis with `R ≠ PQ` (Eq. 13).

This file ships (increments 1–2):

  - **Generating-element grounding** (`mukGen_Z_eq_CCZ`): the canonical diagonal generator at the
    three single-qubit `Z` Paulis equals the project's shipped `CCZ_mat`, `mukGen_Z = CCZ` (i.e.
    `G_{Z₁,Z₂,Z₃} = CCZ`) — `G` is `+1` on every computational-basis state except all-ones, where it
    is `−1`, exactly the CCZ diagonal (both sides diagonal; kernel-routine). This anchors the
    Mukhopadhyay exact-synthesis generating set in the project's CCZ gate.
  - **Gate alphabet + `interp` + exact-synthesis soundness**: the `CliffordCCZGate` ADT (the nine
    literal Clifford generators from the shipped SU(8) `cliffordCCZLiteralGenMap` + the CCZ
    generating element), `interp : List CliffordCCZGate → Matrix (Fin 8) (Fin 8) ℂ`, its composition
    soundness `interp_append`, and the **`synth_CCZ_correct` MVP at the canonical generator**:
    `mukGen_Z` is exactly Clifford+CCZ-representable, witnessed by the single-`CCZ` word
    (`interp [CCZ] = mukGen_Z`), plus the order-2 relation `interp [CCZ, CCZ] = I`.

Continuations (documented, not shipped): the general `G_{P,Q,R}` via Clifford conjugation, the
channel-representation exact-implementability test (Mukhopadhyay Fact 3.9), and the full
`synth_CCZ_correct` for an arbitrary exactly-representable `U` (Thm 3.2 decomposition +
meet-in-the-middle search).

PUBLIC math layer only (per the Item-L brief): no private-repo content.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.CliffordCCZAlphabet
import SKEFTHawking.FKLW.CliffordCCZSU8LiteralGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZSU8 (cliffordCCZLiteralGenMap)

/-- The diagonal of the single-qubit Pauli `Z` acting on qubit `a ∈ {0,1,2}` in the 3-qubit
computational basis: the `±1` sign `(-1)^{bit a of j}` at basis index `j ∈ Fin 8`. -/
def zsign (a : Fin 3) (j : Fin 8) : ℂ := if Nat.testBit j.val a.val then -1 else 1

/-- The single-qubit Pauli `Z` on qubit `a`, as an `8×8` diagonal matrix. -/
noncomputable def pauliZ (a : Fin 3) : Matrix (Fin 8) (Fin 8) ℂ := Matrix.diagonal (zsign a)

/-- **The Mukhopadhyay generating element `G_{Z₁,Z₂,Z₃}`** (Eq. 12 at the three single-qubit `Z`
Paulis): `(3/4)·I + (1/4)·(Z₁+Z₂+Z₃ − Z₁Z₂−Z₂Z₃−Z₃Z₁ + Z₁Z₂Z₃)`. -/
noncomputable def mukGen_Z : Matrix (Fin 8) (Fin 8) ℂ :=
  (3 / 4 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) +
    (1 / 4 : ℂ) • (pauliZ 0 + pauliZ 1 + pauliZ 2
      - pauliZ 0 * pauliZ 1 - pauliZ 1 * pauliZ 2 - pauliZ 2 * pauliZ 0
      + pauliZ 0 * pauliZ 1 * pauliZ 2)

/-- **The generating-element grounding (Item L anchor): `G_{Z₁,Z₂,Z₃} = CCZ`.** The Mukhopadhyay
generator at the three single-qubit `Z` Paulis is exactly the project's doubly-controlled-`Z` gate:
its diagonal entry `(3/4) + (1/4)(z₀+z₁+z₂ − z₀z₁−z₁z₂−z₂z₀ + z₀z₁z₂)` (in the qubit `Z`-signs
`zₐ = zsign a j`) evaluates to `+1` on every computational-basis state except all-ones (`j = 7`),
where it is `−1` — exactly the `CCZ` diagonal. This anchors the Mukhopadhyay exact-synthesis
generating set in the project's `CCZ_mat`. Both sides are diagonal, so the identity reduces to the
eight per-index `ℂ` evaluations (off-diagonal entries vanish on both sides). -/
theorem mukGen_Z_eq_CCZ : mukGen_Z = SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat := by
  simp only [mukGen_Z, pauliZ, Matrix.diagonal_mul_diagonal]
  rw [SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat]
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;>
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        Matrix.diagonal_apply_eq, smul_eq_mul, zsign] <;>
      norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
  · simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
      Matrix.diagonal_apply_ne _ hij, smul_eq_mul, mul_zero, add_zero, sub_zero]

/-! ## The Clifford+CCZ gate alphabet, `interp`, and exact-synthesis soundness (increment 2) -/

/-- **The Clifford+CCZ gate alphabet.** `clifford g` (`g : Fin 9`) is one of the nine literal
Clifford generators of the shipped SU(8) generating set (`H_q1,H_q2,H_q3, S_q1,S_q2,S_q3,
CNOT_12,CNOT_13,CNOT_23` — `cliffordCCZLiteralGenMap`); `ccz` is the Mukhopadhyay CCZ generating
element `G_{Z₁,Z₂,Z₃} = CCZ`. -/
inductive CliffordCCZGate where
  | clifford (g : Fin 9)
  | ccz
  deriving DecidableEq, Repr

/-- The `8×8` matrix of a Clifford+CCZ gate: the nine Cliffords from the shipped literal SU(8)
generating set `cliffordCCZLiteralGenMap`, and `ccz` from the project's `CCZ_mat` (= the
Mukhopadhyay generating element `mukGen_Z`). -/
noncomputable def gateMatrix : CliffordCCZGate → Matrix (Fin 8) (Fin 8) ℂ
  | .clifford g => ((cliffordCCZLiteralGenMap ⟨g.val, by have := g.isLt; omega⟩ :
        ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) : Matrix (Fin 8) (Fin 8) ℂ)
  | .ccz => SKEFTHawking.FKLW.CliffordCCZ.CCZ_mat

/-- **Interpret a Clifford+CCZ gate word** as the ordered product of its gate matrices. -/
noncomputable def interp : List CliffordCCZGate → Matrix (Fin 8) (Fin 8) ℂ
  | [] => 1
  | g :: gs => gateMatrix g * interp gs

@[simp] theorem interp_nil : interp [] = 1 := rfl
@[simp] theorem interp_cons (g : CliffordCCZGate) (gs : List CliffordCCZGate) :
    interp (g :: gs) = gateMatrix g * interp gs := rfl

/-- **Exact-synthesis composition soundness**: `interp` is multiplicative over word concatenation
(`interp (gs ++ hs) = interp gs * interp hs`). The backbone for composing synthesized sub-words. -/
theorem interp_append (gs hs : List CliffordCCZGate) :
    interp (gs ++ hs) = interp gs * interp hs := by
  induction gs with
  | nil => simp
  | cons g gs ih => rw [List.cons_append, interp_cons, interp_cons, ih, Matrix.mul_assoc]

/-- **Exact synthesis of the canonical Mukhopadhyay generating element**: the single-`CCZ` gate word
interprets exactly to `G_{Z₁,Z₂,Z₃} = CCZ = mukGen_Z`. (`interp_ccz` ∘ `mukGen_Z_eq_CCZ`.) -/
theorem interp_ccz : interp [CliffordCCZGate.ccz] = mukGen_Z := by
  rw [interp_cons, interp_nil, Matrix.mul_one, mukGen_Z_eq_CCZ]
  rfl

/-- A unitary `U` is **exactly Clifford+CCZ-representable** iff some Clifford+CCZ gate word
interprets to it. (The Mukhopadhyay exactly-implementable class, for the literal `{H,S,CNOT,CCZ}`
generators; the channel-representation membership test (Fact 3.9) is the documented continuation.) -/
def IsExactlyCliffordCCZ (U : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  ∃ gs : List CliffordCCZGate, interp gs = U

/-- **`synth_CCZ_correct` MVP (canonical generator).** The Mukhopadhyay generating element
`G_{Z₁,Z₂,Z₃} = mukGen_Z = CCZ` is exactly Clifford+CCZ-representable, witnessed by the single-`CCZ`
gate word: `interp (synth) = mukGen_Z`. The exact-synthesis SOUNDNESS (interp of any gate word is its
matrix product, `interp_append`) is the composition backbone; the general decomposition of an
arbitrary exactly-representable `U` (Mukhopadhyay Thm 3.2 via the meet-in-the-middle search +
channel-representation test) is the documented continuation. -/
theorem mukGen_Z_isExactlyCliffordCCZ : IsExactlyCliffordCCZ mukGen_Z :=
  ⟨[CliffordCCZGate.ccz], interp_ccz⟩

/-- **CCZ is an order-2 (self-inverse) generating element**: `interp [CCZ, CCZ] = I` (`CCZ² = I`).
The shortest non-trivial exact-synthesis relation in the alphabet. -/
theorem interp_ccz_ccz : interp [CliffordCCZGate.ccz, CliffordCCZGate.ccz] = 1 := by
  rw [interp_cons, interp_cons, interp_nil, Matrix.mul_one]
  exact SKEFTHawking.FKLW.CCZSUExtension.CCZ_mat_sq_eq_one

end SKEFTHawking.FKLW.MukhopadhyayCCZ
