/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 29) — the controlled-gate block algebra + det-balanced row-op gadget

This file resolves the inc-28 open design question: **how to realize the Giles–Selinger Lemma-4 row
operation on a single column index-pair as a realizable `Mat4`** (an *embedded* `H·Tᵐ` acts on both
qubit blocks at once, so a single matched pair needs a genuinely controlled operation).

## The determinant obstruction (why the naive two-level operator fails)

Every `Gate2` generator has determinant in `⟨ω²⟩ = {1, i, -1, -i}` (embedded single-qubit gates have
`det (A ⊗ I) = (det A)²`; the cnots have `det = -1`), so **every `Gate2` word** has determinant in
`⟨ω²⟩`. The bare two-level `H·Tᵐ` at a pair has determinant `-ωᵐ` — for odd `m` an odd `ω`-power,
hence **not realizable by any two-qubit Clifford+T word**. (This elementary invariant is the content
behind Giles–Selinger's one-ancilla clause; in particular a controlled-`T` is impossible at dim 4.)

## The fix: balance the determinant with an unconditional phase

`blockdiag(Tᵐ, H·Tᵐ) = Λ₁(H) · (I ⊗ Tᵐ)` — apply `Tᵐ` to the target qubit *unconditionally* (the
spectator pair only picks up a harmless unit phase `ωᵐ` on one entry, preserving `denExp`, `normSq`
and the unit-column sum), then apply **one fixed controlled gate, `CH = Λ₁(H)`**. The determinant is
`-ω²ᵐ ∈ ⟨ω²⟩` for **all** `m`, and the gadget's column action at the `fst = 1` pair is verbatim the
shipped pair-level Lemma-4 lemmas (`core_step` / `lemma4_1010` / `cross_orbit_drop`):
`(v₁₀ ± ωᵐ·v₁₁)/√2`.

## Headline definitions

  * `ctrl P Q : Mat4` — the first-qubit-controlled block matrix (`P` on the `fst = 0` block, `Q` on
    the `fst = 1` block). `ctrl_mul : ctrl P Q * ctrl R S = ctrl (P*R) (Q*S)` is the block algebra;
    `cnot01 = ctrl 1 X` and `embedSnd A = ctrl A A` express the generators in it.
  * `chMat = ctrl 1 H` — **controlled-H**, realized exactly by the 18-gate word `chWord` via the
    conjugator `V = S·H·T·H·S†·H` with `V·X·V⁻¹ = H` (so `CH = (I⊗V)·CNOT·(I⊗V⁻¹)`). The two dim-2
    conjugator facts are `decide +kernel` — pure kernel reduction, the same trust base as `decide`
    (no compiler, no `native_decide`), bypassing the elaborator's whnf budget on the 17-fold matrix
    product.
  * `rowOpGadget m = ctrl Tᵐ (H·Tᵐ) = chMat * embedSnd Tᵐ` — the det-balanced Lemma-4 row-op gadget,
    realizable within `18 + m`; `rowOpGadgetInv m` is its inverse word (`CH² = 1`, `T⁸ = 1`).

## Headline theorems

  * `interp2_chWord` — `CH` is exactly a `Gate2` word (kernel-pure, no ancilla).
  * `rowOpGadget_mulVec_*` — the gadget's exact column action: spectators `(v₀₀, ωᵐ·v₀₁)`, pair
    `((v₁₀ + ωᵐ·v₁₁)/√2, (v₁₀ - ωᵐ·v₁₁)/√2)` — the Giles–Selinger row operation on the `fst = 1` pair.
  * `rowOpGadgetInv_mul_rowOpGadget` — the inverse identity (for the `ReductionStep` factorization
    `v = g · v'`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` — the dim-2 conjugation facts are kernel reduction (`decide +kernel`).

## References

  * Giles–Selinger, "Exact synthesis of multiqubit Clifford+T circuits", arXiv:1212.0506 (Lemma 4 row
    operation; the one-ancilla clause this file's det-balancing makes unnecessary at dim 4).
  * Kliuchnikov–Maslov–Mosca, PRL 110:190502, arXiv:1212.0822 (circuit C consumes the column lemma).
  * `Lit-Search/Phase-6AO/GilesSelinger-1212.0506-column-lemma-mechanism-websearch.md`.
-/

import SKEFTHawking.FKLW.RossSelinger.ColumnSynthesis
import SKEFTHawking.FKLW.RossSelinger.ReduceStepColumn
import SKEFTHawking.FKLW.RossSelinger.KMMReduce

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace Gate2

open ZOmegaSqrt2

/-! ### The first-qubit-controlled block constructor and its algebra -/

/-- **First-qubit-controlled block matrix**: `P` acts on the second qubit within the `fst = 0`
block, `Q` within the `fst = 1` block — `ctrl P Q = blockdiag(P, Q)` in first-qubit blocks. -/
def ctrl (P Q : Mat2') : Mat4 :=
  Matrix.of fun o i => if o.1 = i.1 then (if o.1 = 0 then P o.2 i.2 else Q o.2 i.2) else 0

/-- Entry formula for `ctrl` (definitional; keeps `0`/`1` syntactic for `simp`). -/
@[simp] theorem ctrl_apply (P Q : Mat2') (o i : Fin 2 × Fin 2) :
    ctrl P Q o i = if o.1 = i.1 then (if o.1 = 0 then P o.2 i.2 else Q o.2 i.2) else 0 := rfl

/-- `ctrl 1 1 = 1`. -/
theorem ctrl_one_one : ctrl 1 1 = 1 := by decide

/-- **The block algebra**: `ctrl` is multiplicative blockwise. The workhorse that turns gate-word
concatenation into block-level matrix products. -/
theorem ctrl_mul (P Q R S : Mat2') : ctrl P Q * ctrl R S = ctrl (P * R) (Q * S) := by
  ext ⟨o₁, o₂⟩ ⟨i₁, i₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single_of_mem o₁ (Finset.mem_univ o₁)
      (fun k₁ _ hk₁ => Finset.sum_eq_zero fun k₂ _ => by
        show ctrl P Q (o₁, o₂) (k₁, k₂) * ctrl R S (k₁, k₂) (i₁, i₂) = 0
        rw [show ctrl P Q (o₁, o₂) (k₁, k₂) = 0 from if_neg fun h => hk₁ h.symm, zero_mul])]
  by_cases hoi : o₁ = i₁
  · subst hoi
    rw [show ctrl (P * R) (Q * S) (o₁, o₂) (o₁, i₂)
        = if o₁ = 0 then (P * R) o₂ i₂ else (Q * S) o₂ i₂ from if_pos rfl]
    by_cases h0 : o₁ = 0
    · subst h0
      rw [if_pos rfl, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k₂ _ => ?_
      show ctrl P Q (0, o₂) (0, k₂) * ctrl R S (0, k₂) (0, i₂) = P o₂ k₂ * R k₂ i₂
      rw [show ctrl P Q (0, o₂) (0, k₂) = P o₂ k₂ from by simp,
        show ctrl R S (0, k₂) (0, i₂) = R k₂ i₂ from by simp]
    · rw [if_neg h0, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k₂ _ => ?_
      show ctrl P Q (o₁, o₂) (o₁, k₂) * ctrl R S (o₁, k₂) (o₁, i₂) = Q o₂ k₂ * S k₂ i₂
      rw [show ctrl P Q (o₁, o₂) (o₁, k₂) = Q o₂ k₂ from by
            show (if o₁ = o₁ then (if o₁ = 0 then P o₂ k₂ else Q o₂ k₂) else 0) = Q o₂ k₂
            rw [if_pos rfl, if_neg h0],
        show ctrl R S (o₁, k₂) (o₁, i₂) = S k₂ i₂ from by
            show (if o₁ = o₁ then (if o₁ = 0 then R k₂ i₂ else S k₂ i₂) else 0) = S k₂ i₂
            rw [if_pos rfl, if_neg h0]]
  · rw [show ctrl (P * R) (Q * S) (o₁, o₂) (i₁, i₂) = 0 from if_neg hoi]
    exact Finset.sum_eq_zero fun k₂ _ => by
      show ctrl P Q (o₁, o₂) (o₁, k₂) * ctrl R S (o₁, k₂) (i₁, i₂) = 0
      rw [show ctrl R S (o₁, k₂) (i₁, i₂) = 0 from if_neg hoi, mul_zero]

/-- `embedSnd A` is the block-diagonal `ctrl A A` (the same gate in both blocks). -/
theorem embedSnd_eq_ctrl (A : Mat2') : embedSnd A = ctrl A A := by
  ext ⟨o₁, o₂⟩ ⟨i₁, i₂⟩
  rw [embedSnd, Matrix.kroneckerMap_apply]
  show (1 : Mat2') o₁ i₁ * A o₂ i₂ = ctrl A A (o₁, o₂) (i₁, i₂)
  by_cases h : o₁ = i₁
  · subst h
    rw [Matrix.one_apply_eq, one_mul]
    show A o₂ i₂ = if o₁ = o₁ then (if o₁ = 0 then A o₂ i₂ else A o₂ i₂) else 0
    rw [if_pos rfl, ite_self]
  · rw [Matrix.one_apply_ne h, zero_mul]
    show (0 : ZOmegaSqrt2) = if o₁ = i₁ then (if o₁ = 0 then A o₂ i₂ else A o₂ i₂) else 0
    rw [if_neg h]

/-- `cnot01` is the controlled-`X`: `ctrl 1 X`. -/
theorem cnot01_eq_ctrl : cnot01 = ctrl 1 (CliffordTGate.gateMatrix .X) := by decide

/-- `ctrl` action on a column, `fst = 0` block: `P` combines the second-qubit pair. -/
theorem ctrl_mulVec_zero (P Q : Mat2') (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (j : Fin 2) :
    (ctrl P Q).mulVec v (0, j) = ∑ j' : Fin 2, P j j' * v (0, j') := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)
      (fun i' _ hi' => Finset.sum_eq_zero fun j' _ => by
        show ctrl P Q (0, j) (i', j') * v (i', j') = 0
        rw [show ctrl P Q (0, j) (i', j') = 0 from if_neg fun h => hi' h.symm, zero_mul])]
  refine Finset.sum_congr rfl fun j' _ => ?_
  show ctrl P Q (0, j) (0, j') * v (0, j') = P j j' * v (0, j')
  rw [show ctrl P Q (0, j) (0, j') = P j j' from by simp]

/-- `ctrl` action on a column, `fst = 1` block: `Q` combines the second-qubit pair. -/
theorem ctrl_mulVec_one (P Q : Mat2') (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (j : Fin 2) :
    (ctrl P Q).mulVec v (1, j) = ∑ j' : Fin 2, Q j j' * v (1, j') := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.sum_eq_single_of_mem 1 (Finset.mem_univ 1)
      (fun i' _ hi' => Finset.sum_eq_zero fun j' _ => by
        show ctrl P Q (1, j) (i', j') * v (i', j') = 0
        rw [show ctrl P Q (1, j) (i', j') = 0 from if_neg fun h => hi' h.symm, zero_mul])]
  refine Finset.sum_congr rfl fun j' _ => ?_
  show ctrl P Q (1, j) (1, j') * v (1, j') = Q j j' * v (1, j')
  rw [show ctrl P Q (1, j) (1, j') = Q j j' from by simp]

/-! ### The controlled-H brick

`CH = ctrl 1 H` is realized by conjugating the controlled-`X` (`cnot01`) on the target line:
`CH = (I⊗V) · CNOT · (I⊗V⁻¹)` for any `V` with `V·X·V⁻¹ = H`. The conjugator is
`V = B·H` with `B = S·H·T·H·S†` (a `π/4` Y-rotation in Clifford+T: `B·Z·B† = H`, hence
`V·X·V⁻¹ = B·(H·X·H)·B⁻¹ = B·Z·B† = H`). Both dim-2 facts are `decide +kernel` (pure kernel
reduction — same trust base as `decide`, no elaborator whnf budget). -/

/-- The CH conjugator word: `V = S·H·T·H·S†·H` (with `S† = S·Z`), satisfying `V·X·V⁻¹ = H`. -/
def chConjWord : List CliffordTGate := [.S, .H, .T, .H, .S, .Z, .H]

/-- The inverse conjugator word: `V⁻¹ = H·S·H·T†·H·S†` (with `T† = T³·Z`, `S† = S·Z`). -/
def chConjInvWord : List CliffordTGate := [.H, .S, .H, .T, .T, .T, .Z, .H, .S, .Z]

/-- The conjugator words are mutually inverse (kernel reduction). -/
theorem chConj_mul_inv :
    CliffordTGate.interp chConjWord * CliffordTGate.interp chConjInvWord = 1 := by decide +kernel

/-- **The conjugation fact**: `V·(X·V⁻¹) = H` — `V` conjugates `X` to `H` (kernel reduction). -/
theorem chConj_conj_X :
    CliffordTGate.interp chConjWord *
      (CliffordTGate.gateMatrix .X * CliffordTGate.interp chConjInvWord) =
      CliffordTGate.gateMatrix .H := by decide +kernel

/-- **Controlled-H** as a `Mat4`: identity on the `fst = 0` block, `H` on the `fst = 1` block. -/
def chMat : Mat4 := ctrl 1 (CliffordTGate.gateMatrix .H)

/-- The 18-gate `Gate2` word realizing `CH`: `(I⊗V) · CNOT · (I⊗V⁻¹)`. -/
def chWord : List Gate2 := chConjWord.map .onSnd ++ .cx01 :: chConjInvWord.map .onSnd

/-- **`CH` is exactly a `Gate2` word** — the block algebra collapses the conjugated cnot:
`(I⊗V)·CNOT·(I⊗V⁻¹) = ctrl (V·V⁻¹) (V·X·V⁻¹) = ctrl 1 H`. Kernel-pure, no ancilla. -/
theorem interp2_chWord : interp2 chWord = chMat := by
  rw [chWord, interp2_append, interp2_cons,
    show gateMatrix2 .cx01 = cnot01 from rfl,
    ← embedSnd_interp, ← embedSnd_interp,
    embedSnd_eq_ctrl, embedSnd_eq_ctrl, cnot01_eq_ctrl, ctrl_mul, ctrl_mul,
    show (1 : Mat2') * CliffordTGate.interp chConjInvWord = CliffordTGate.interp chConjInvWord
      from one_mul _,
    chConj_mul_inv, chConj_conj_X, chMat]

@[simp] theorem chWord_length : chWord.length = 18 := rfl

/-- `CH` is realizable within 18 gates. -/
theorem chMat_realizableWithin : IsRealizableWithin chMat 18 :=
  ⟨chWord, interp2_chWord, chWord_length.le⟩

/-- `CH` is an involution (`H² = 1` blockwise). -/
theorem chMat_mul_chMat : chMat * chMat = 1 := by
  rw [chMat, ctrl_mul, show (1 : Mat2') * 1 = 1 from one_mul _, CliffordTGate.H_mul_H,
    ctrl_one_one]

/-! ### The det-balanced row-op gadget `ctrl Tᵐ (H·Tᵐ)` -/

/-- **The Lemma-4 row-op gadget**: `Tᵐ` on the `fst = 0` block (spectator unit phase), `H·Tᵐ` on the
`fst = 1` block (the Giles–Selinger row operation). Determinant `-ω²ᵐ ∈ ⟨ω²⟩` for all `m` — the
det-balanced form that IS realizable (unlike the bare two-level `H·Tᵐ`, odd `m`). -/
def rowOpGadget (m : ℕ) : Mat4 :=
  ctrl (CliffordTGate.gateMatrix .T ^ m)
    (CliffordTGate.gateMatrix .H * CliffordTGate.gateMatrix .T ^ m)

/-- The gadget factors as `CH · (I ⊗ Tᵐ)` — one fixed controlled gate plus an unconditional phase. -/
theorem rowOpGadget_eq (m : ℕ) :
    rowOpGadget m = chMat * embedSnd (CliffordTGate.gateMatrix .T ^ m) := by
  rw [rowOpGadget, chMat, embedSnd_eq_ctrl, ctrl_mul,
    show (1 : Mat2') * CliffordTGate.gateMatrix .T ^ m = CliffordTGate.gateMatrix .T ^ m
      from one_mul _]

/-- **The gadget is realizable within `18 + m` gates** (`chWord` plus `m` copies of `I⊗T`). -/
theorem rowOpGadget_realizableWithin (m : ℕ) : IsRealizableWithin (rowOpGadget m) (18 + m) := by
  rw [rowOpGadget_eq]
  refine chMat_realizableWithin.mul ?_
  have h := embedSnd_realizableWithin (List.replicate m CliffordTGate.T)
  rwa [interp_replicate, List.length_replicate] at h

/-- The inverse gadget `(I ⊗ T^(8-m)) · CH`. -/
def rowOpGadgetInv (m : ℕ) : Mat4 :=
  embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) * chMat

/-- **The inverse identity**: `rowOpGadgetInv m · rowOpGadget m = 1` (via `CH² = 1`, `T⁸ = 1`).
This provides the `g` with `v = g · v'` in the `ReductionStep` factorization. Matrix `*` is the
heterogeneous `Matrix.instHMul`, so the algebra is term-justified (`congrArg` + `Matrix.mul_assoc`),
as in `KMMReduce.reconWord_inv`. -/
theorem rowOpGadgetInv_mul_rowOpGadget (m : ℕ) (hm : m ≤ 8) :
    rowOpGadgetInv m * rowOpGadget m = 1 := by
  rw [rowOpGadgetInv, rowOpGadget_eq]
  calc embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) * chMat *
        (chMat * embedSnd (CliffordTGate.gateMatrix .T ^ m))
      = embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) *
          (chMat * (chMat * embedSnd (CliffordTGate.gateMatrix .T ^ m))) := Matrix.mul_assoc _ _ _
    _ = embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) *
          (chMat * chMat * embedSnd (CliffordTGate.gateMatrix .T ^ m)) :=
        congrArg (embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) * ·)
          (Matrix.mul_assoc _ _ _).symm
    _ = embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) *
          ((1 : Mat4) * embedSnd (CliffordTGate.gateMatrix .T ^ m)) :=
        congrArg (embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) * ·)
          (congrArg (· * embedSnd (CliffordTGate.gateMatrix .T ^ m)) chMat_mul_chMat)
    _ = embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) *
          embedSnd (CliffordTGate.gateMatrix .T ^ m) :=
        congrArg (embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m)) * ·) (one_mul _)
    _ = embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m) * CliffordTGate.gateMatrix .T ^ m) :=
        (embedSnd_mul _ _).symm
    _ = embedSnd (CliffordTGate.gateMatrix .T ^ (8 - m + m)) :=
        congrArg embedSnd (pow_add _ _ _).symm
    _ = embedSnd (CliffordTGate.gateMatrix .T ^ 8) := by rw [Nat.sub_add_cancel hm]
    _ = embedSnd 1 := congrArg embedSnd KMM.gateMatrix_T_pow_eight
    _ = 1 := embedSnd_one

/-- The inverse gadget is realizable within `(8 - m) + 18` gates. -/
theorem rowOpGadgetInv_realizableWithin (m : ℕ) :
    IsRealizableWithin (rowOpGadgetInv m) (8 - m + 18) := by
  rw [rowOpGadgetInv]
  refine IsRealizableWithin.mul ?_ chMat_realizableWithin
  have h := embedSnd_realizableWithin (List.replicate (8 - m) CliffordTGate.T)
  rwa [interp_replicate, List.length_replicate] at h

/-! ### The gadget's exact column action

Spectator block (`fst = 0`): `(v₀₀, ωᵐ·v₀₁)` — a unit phase on one entry, `denExp`/`normSq`
invariant. Active block (`fst = 1`): `((v₁₀ + ωᵐ·v₁₁)/√2, (v₁₀ - ωᵐ·v₁₁)/√2)` — verbatim the
shipped pair-level Lemma-4 shapes (`core_step` / `lemma4_1010` / `cross_orbit_drop`). -/

/-- Spectator entry `(0,0)`: untouched. -/
theorem rowOpGadget_mulVec_zero_zero (m : ℕ) (v : Fin 2 × Fin 2 → ZOmegaSqrt2) :
    (rowOpGadget m).mulVec v (0, 0) = v (0, 0) := by
  have hd00 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 0 0 = 1 := by
    rw [Matrix.diagonal_apply_eq]; rfl
  have hd01 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 0 1 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  rw [rowOpGadget, ctrl_mulVec_zero, Fin.sum_univ_two, KMM.T_pow_diag]
  rw [hd00, hd01, one_mul, zero_mul, add_zero]

/-- Spectator entry `(0,1)`: the unit phase `ωᵐ` (denExp/normSq-preserving). -/
theorem rowOpGadget_mulVec_zero_one (m : ℕ) (v : Fin 2 × Fin 2 → ZOmegaSqrt2) :
    (rowOpGadget m).mulVec v (0, 1) = CliffordTGate.ωS ^ m * v (0, 1) := by
  have hd10 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 1 0 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd11 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 1 1 = CliffordTGate.ωS ^ m := by
    rw [Matrix.diagonal_apply_eq]; rfl
  rw [rowOpGadget, ctrl_mulVec_zero, Fin.sum_univ_two, KMM.T_pow_diag]
  rw [hd10, hd11, zero_mul, zero_add]

/-- Pair entry `(1,0)`: the Lemma-4 `+`-combination `(v₁₀ + ωᵐ·v₁₁)/√2`. -/
theorem rowOpGadget_mulVec_one_zero (m : ℕ) (v : Fin 2 × Fin 2 → ZOmegaSqrt2) :
    (rowOpGadget m).mulVec v (1, 0) =
      invSqrt2 * (v (1, 0) + CliffordTGate.ωS ^ m * v (1, 1)) := by
  have hd00 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 0 0 = 1 := by
    rw [Matrix.diagonal_apply_eq]; rfl
  have hd01 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 0 1 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd10 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 1 0 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd11 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 1 1 = CliffordTGate.ωS ^ m := by
    rw [Matrix.diagonal_apply_eq]; rfl
  rw [rowOpGadget, ctrl_mulVec_one, Fin.sum_univ_two, KMM.T_pow_diag]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, CliffordTGate.gateMatrix, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, hd00, hd01, hd10, hd11]
  ring

/-- Pair entry `(1,1)`: the Lemma-4 `-`-combination `(v₁₀ - ωᵐ·v₁₁)/√2`. -/
theorem rowOpGadget_mulVec_one_one (m : ℕ) (v : Fin 2 × Fin 2 → ZOmegaSqrt2) :
    (rowOpGadget m).mulVec v (1, 1) =
      invSqrt2 * (v (1, 0) - CliffordTGate.ωS ^ m * v (1, 1)) := by
  have hd00 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 0 0 = 1 := by
    rw [Matrix.diagonal_apply_eq]; rfl
  have hd01 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 0 1 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd10 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 1 0 = 0 :=
    Matrix.diagonal_apply_ne _ (by decide)
  have hd11 : (Matrix.diagonal ![1, CliffordTGate.ωS ^ m]) 1 1 = CliffordTGate.ωS ^ m := by
    rw [Matrix.diagonal_apply_eq]; rfl
  rw [rowOpGadget, ctrl_mulVec_one, Fin.sum_univ_two, KMM.T_pow_diag]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, CliffordTGate.gateMatrix, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, hd00, hd01, hd10, hd11]
  ring

end Gate2
end SKEFTHawking.RossSelinger
