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

This file ships (increments 1–3):

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
  - **The general generating element + reflection structure** (`mukGen`, `mukGen_sq`): for ANY three
    pairwise-commuting involutions `p, q, r`, `G_{P,Q,R} = (3/4)I+(1/4)(p+q+r−pq−qr−rp+pqr)` is a
    reflection (`G² = I`) — the structural defining property of Mukhopadhyay's generating set (Eq. 12
    / Eq. 13). Instantiated at the `Z`-Paulis (`mukGen_Z_sq`: `CCZ² = I` via the generating-element
    structure).

Continuations (documented, not shipped): the general `G_{P,Q,R}` realized as a Clifford CONJUGATE of
CCZ (so each generator is a gate word), the channel-representation exact-implementability test
(Mukhopadhyay Fact 3.9), and the full `synth_CCZ_correct` for an arbitrary exactly-representable `U`
(Thm 3.2 decomposition + meet-in-the-middle search).

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

/-- **The general Mukhopadhyay generating element** `G_{P,Q,R}` (arXiv:2401.08950 Eq. 12) for any
three operators `p, q, r`: `(3/4)·I + (1/4)·(p+q+r − pq−qr−rp + pqr)`. When `p, q, r` are pairwise
commuting involutions (Paulis, the intended case) this is a reflection (`mukGen_sq`: `G² = I`) — the
structural defining property of Mukhopadhyay's generating set. -/
noncomputable def mukGen (p q r : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  (3 / 4 : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) +
    (1 / 4 : ℂ) • (p + q + r - p * q - q * r - r * p + p * q * r)

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

/-! ## The general generating element is a reflection: `G_{P,Q,R}² = I` (increment 3)

For pairwise-commuting involutions `p, q, r` the Mukhopadhyay generator `G_{P,Q,R}` is a reflection
(`G² = I`) — the structural defining property of the generating set (its eigenvalues are `±1`, with
`−1` precisely on the joint `(−1,−1,−1)`-eigenspace). Slick proof: with `Y := (1−p)(1−q)(1−r)`,
each `(1−x)² = 2(1−x)` and they commute, so `Y² = 8Y`; and `G = 1 − (1/4)·Y`, whence `G² = 1`. -/

/-- **The general generating element is a reflection.** For pairwise-commuting involutions `p, q, r`
(`p² = q² = r² = 1`, `pq = qp`, `qr = rq`, `pr = rp`), the Mukhopadhyay generator squares to the
identity: `G_{P,Q,R}² = I`. -/
theorem mukGen_sq (p q r : Matrix (Fin 8) (Fin 8) ℂ)
    (hp : p * p = 1) (hq : q * q = 1) (hr : r * r = 1)
    (hpq : p * q = q * p) (hqr : q * r = r * q) (hpr : p * r = r * p) :
    mukGen p q r * mukGen p q r = 1 := by
  set A := (1 - p) with hA; set B := (1 - q) with hB; set C := (1 - r) with hC
  have cAB : A * B = B * A := by
    rw [hA, hB, show (1 - p) * (1 - q) = 1 - q - p + p * q from by noncomm_ring,
        show (1 - q) * (1 - p) = 1 - p - q + q * p from by noncomm_ring, hpq]; abel
  have cBC : B * C = C * B := by
    rw [hB, hC, show (1 - q) * (1 - r) = 1 - r - q + q * r from by noncomm_ring,
        show (1 - r) * (1 - q) = 1 - q - r + r * q from by noncomm_ring, hqr]; abel
  have cAC : A * C = C * A := by
    rw [hA, hC, show (1 - p) * (1 - r) = 1 - r - p + p * r from by noncomm_ring,
        show (1 - r) * (1 - p) = 1 - p - r + r * p from by noncomm_ring, hpr]; abel
  have hA2 : A * A = (2 : ℂ) • A := by
    rw [hA, show (1 - p) * (1 - p) = 1 - p - p + p * p from by noncomm_ring, hp, two_smul]; abel
  have hB2 : B * B = (2 : ℂ) • B := by
    rw [hB, show (1 - q) * (1 - q) = 1 - q - q + q * q from by noncomm_ring, hq, two_smul]; abel
  have hC2 : C * C = (2 : ℂ) • C := by
    rw [hC, show (1 - r) * (1 - r) = 1 - r - r + r * r from by noncomm_ring, hr, two_smul]; abel
  -- Y² = 8•Y  via reorder (commuting) to A*A*(B*B)*(C*C) + the three idempotent-scalings
  have hY2 : A * B * C * (A * B * C) = (8 : ℂ) • (A * B * C) := by
    have reorder : A * B * C * (A * B * C) = A * A * (B * B) * (C * C) := by
      calc A * B * C * (A * B * C)
          = A * B * (C * A) * (B * C) := by noncomm_ring
        _ = A * B * (A * C) * (B * C) := by rw [← cAC]
        _ = A * (B * A) * C * (B * C) := by noncomm_ring
        _ = A * (A * B) * C * (B * C) := by rw [← cAB]
        _ = A * A * B * (C * B) * C := by noncomm_ring
        _ = A * A * B * (B * C) * C := by rw [← cBC]
        _ = A * A * (B * B) * (C * C) := by noncomm_ring
    rw [reorder, hA2, hB2, hC2]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]; norm_num
  -- G = 1 − (1/4)•Y
  have hGY : mukGen p q r = 1 - (1 / 4 : ℂ) • (A * B * C) := by
    have hXY : p + q + r - p * q - q * r - r * p + p * q * r = 1 - A * B * C := by
      rw [hA, hB, hC, ← hpr]; noncomm_ring
    rw [mukGen, hXY]; module
  -- assemble: (1 − (1/4)•Y)² = 1  (abstract Y so the outer subtraction is the only one `sub_mul` hits)
  set Y := A * B * C with hYdef
  rw [hGY, mul_sub, mul_one, sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hY2,
    smul_smul]
  module

/-- The single-qubit `Z`-Paulis are involutions: `Zₐ² = I` (diagonal `±1`). -/
theorem pauliZ_mul_self (a : Fin 3) : pauliZ a * pauliZ a = 1 := by
  rw [pauliZ, Matrix.diagonal_mul_diagonal]
  have h1 : (fun i => zsign a i * zsign a i) = (1 : Fin 8 → ℂ) := by
    funext j; simp only [Pi.one_apply, zsign]; by_cases h : Nat.testBit j.val a.val <;> simp [h]
  rw [h1]; exact Matrix.diagonal_one

/-- The single-qubit `Z`-Paulis pairwise commute (diagonal). -/
theorem pauliZ_comm (a b : Fin 3) : pauliZ a * pauliZ b = pauliZ b * pauliZ a := by
  rw [pauliZ, pauliZ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext j; ring

/-- The canonical generator is the general `mukGen` at the three `Z`-Paulis (definitional). -/
theorem mukGen_Z_eq_mukGen : mukGen_Z = mukGen (pauliZ 0) (pauliZ 1) (pauliZ 2) := rfl

/-- **`G_{Z₁,Z₂,Z₃} = CCZ` is a reflection**: `CCZ² = I`, obtained as the canonical instance of the
general `mukGen_sq` (the `Z`-Paulis being commuting involutions). Consistent with the shipped
`CCZ_mat_sq_eq_one`, here derived through the Mukhopadhyay generating-element structure. -/
theorem mukGen_Z_sq : mukGen_Z * mukGen_Z = 1 := by
  rw [mukGen_Z_eq_mukGen]
  exact mukGen_sq _ _ _ (pauliZ_mul_self 0) (pauliZ_mul_self 1) (pauliZ_mul_self 2)
    (pauliZ_comm 0 1) (pauliZ_comm 1 2) (pauliZ_comm 0 2)

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
