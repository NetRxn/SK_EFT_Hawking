/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 35) — the system-controlled lift of two-qubit words

KMM's `W` is **controlled-`C`**: the column-lemma word `C` (inc 32–33) prepares `|v⟩` on the two
ancillas, controlled on the system qubit. This file realizes the controlled lift as exact
three-qubit Clifford+T words, by the per-gate rule that falls out of the determinant analysis
(inc 29's `⟨ω²⟩` argument lifts to `⟨ω⁴⟩` at three qubits):

  * **target-diagonal gates (`T`, `S`, `Z`, `id`) lift uncontrolled** — their `s = 0` block is a
    `|00⟩`-fixing diagonal, harmless on the initialized ancillas. (This sidesteps the
    determinant-impossible controlled-`T` entirely.)
  * `X` lifts to the system-controlled cnot; `Y` to its `S`-conjugate; `H` to the inc-29
    conjugation `(I⊗V)·CX·(I⊗V⁻¹)` lifted on the controlled cnot.
  * the cnots lift to **Toffoli**, realized via the CCZ phase-polynomial word
    `4xyz = x+y+z−(x⊕y)−(a⊕b)−(s⊕b)+(s⊕a⊕b) (mod 8)` (kernel-verified).
  * the scalar `ω` lifts to `T` on the **system** line (`Λ(ω·I₄) = T_s ⊗ I₄`).

## Headline

  * `ctrl8 P Q : Mat8` — the system-controlled block constructor and its algebra.
  * `ctrlLift : Gate2 → List Gate3` + `ctrlLift_word_spec` — **every two-qubit word `w` has a
    controlled lift**: a `Gate3` word of length `≤ 30·|w|` interpreting to `ctrl8 D (interp2 w)`
    with `D` fixing `|00⟩` (`FixesE00`). Applied to the column-lemma word this is controlled-`C`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` — concrete identities are kernel `decide` / `decide +kernel`.
-/

import SKEFTHawking.FKLW.RossSelinger.CliffordTGate3
import SKEFTHawking.FKLW.RossSelinger.Gate2Control

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace Gate3

open ZOmegaSqrt2

/-! ### The system-controlled block constructor -/

/-- **System-controlled block matrix**: `P` on the `s = 0` block, `Q` on the `s = 1` block. -/
def ctrl8 (P Q : Mat4) : Mat8 :=
  Matrix.of fun o i => if o.1 = i.1 then (if o.1 = 0 then P o.2 i.2 else Q o.2 i.2) else 0

/-- Entry formula (definitional). -/
@[simp] theorem ctrl8_apply (P Q : Mat4) (o i : Fin 2 × Fin 2 × Fin 2) :
    ctrl8 P Q o i = if o.1 = i.1 then (if o.1 = 0 then P o.2 i.2 else Q o.2 i.2) else 0 := rfl

/-- `ctrl8 1 1 = 1`. -/
theorem ctrl8_one_one : ctrl8 1 1 = 1 := by decide

/-- **The block algebra at dim 8**: `ctrl8` is multiplicative blockwise. -/
theorem ctrl8_mul (P Q R S : Mat4) : ctrl8 P Q * ctrl8 R S = ctrl8 (P * R) (Q * S) := by
  ext ⟨o₁, o₂⟩ ⟨i₁, i₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single_of_mem o₁ (Finset.mem_univ o₁)
      (fun k₁ _ hk₁ => Finset.sum_eq_zero fun k₂ _ => by
        show ctrl8 P Q (o₁, o₂) (k₁, k₂) * ctrl8 R S (k₁, k₂) (i₁, i₂) = 0
        rw [show ctrl8 P Q (o₁, o₂) (k₁, k₂) = 0 from if_neg fun h => hk₁ h.symm, zero_mul])]
  by_cases hoi : o₁ = i₁
  · subst hoi
    rw [show ctrl8 (P * R) (Q * S) (o₁, o₂) (o₁, i₂)
        = if o₁ = 0 then (P * R) o₂ i₂ else (Q * S) o₂ i₂ from if_pos rfl]
    by_cases h0 : o₁ = 0
    · subst h0
      rw [if_pos rfl, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k₂ _ => ?_
      show ctrl8 P Q (0, o₂) (0, k₂) * ctrl8 R S (0, k₂) (0, i₂) = P o₂ k₂ * R k₂ i₂
      rw [show ctrl8 P Q (0, o₂) (0, k₂) = P o₂ k₂ from by simp,
        show ctrl8 R S (0, k₂) (0, i₂) = R k₂ i₂ from by simp]
    · rw [if_neg h0, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k₂ _ => ?_
      show ctrl8 P Q (o₁, o₂) (o₁, k₂) * ctrl8 R S (o₁, k₂) (o₁, i₂) = Q o₂ k₂ * S k₂ i₂
      rw [show ctrl8 P Q (o₁, o₂) (o₁, k₂) = Q o₂ k₂ from by
            show (if o₁ = o₁ then (if o₁ = 0 then P o₂ k₂ else Q o₂ k₂) else 0) = Q o₂ k₂
            rw [if_pos rfl, if_neg h0],
        show ctrl8 R S (o₁, k₂) (o₁, i₂) = S k₂ i₂ from by
            show (if o₁ = o₁ then (if o₁ = 0 then R k₂ i₂ else S k₂ i₂) else 0) = S k₂ i₂
            rw [if_pos rfl, if_neg h0]]
  · rw [show ctrl8 (P * R) (Q * S) (o₁, o₂) (i₁, i₂) = 0 from if_neg hoi]
    exact Finset.sum_eq_zero fun k₂ _ => by
      show ctrl8 P Q (o₁, o₂) (o₁, k₂) * ctrl8 R S (o₁, k₂) (i₁, i₂) = 0
      rw [show ctrl8 R S (o₁, k₂) (i₁, i₂) = 0 from if_neg hoi, mul_zero]

/-- `embedAnc M = ctrl8 M M` (the same operator in both system blocks). -/
theorem embedAnc_eq_ctrl8 (M : Mat4) : embedAnc M = ctrl8 M M := by
  ext ⟨o₁, o₂⟩ ⟨i₁, i₂⟩
  rw [embedAnc, Matrix.kroneckerMap_apply]
  show (1 : Matrix (Fin 2) (Fin 2) ZOmegaSqrt2) o₁ i₁ * M o₂ i₂ = ctrl8 M M (o₁, o₂) (i₁, i₂)
  by_cases h : o₁ = i₁
  · subst h
    rw [Matrix.one_apply_eq, one_mul]
    show M o₂ i₂ = if o₁ = o₁ then (if o₁ = 0 then M o₂ i₂ else M o₂ i₂) else 0
    rw [if_pos rfl, ite_self]
  · rw [Matrix.one_apply_ne h, zero_mul]
    show (0 : ZOmegaSqrt2) = if o₁ = i₁ then (if o₁ = 0 then M o₂ i₂ else M o₂ i₂) else 0
    rw [if_neg h]

/-- The system-controlled cnots in block form. -/
theorem cnotSA_eq_ctrl8 : cnotSA = ctrl8 1 (Gate2.gateMatrix2 (.onFst .X)) := by decide

theorem cnotSB_eq_ctrl8 : cnotSB = ctrl8 1 (Gate2.gateMatrix2 (.onSnd .X)) := by decide

/-- `T` on the system line is the controlled scalar `ω`: `T_s ⊗ I₄ = ctrl8 1 (ω·I₄)`. -/
theorem embedSys_T_eq_ctrl8_omega_fst :
    embedSys (CliffordTGate.gateMatrix .T) = ctrl8 1 (Gate2.gateMatrix2 (.onFst .omega)) := by
  decide

theorem embedSys_T_eq_ctrl8_omega_snd :
    embedSys (CliffordTGate.gateMatrix .T) = ctrl8 1 (Gate2.gateMatrix2 (.onSnd .omega)) := by
  decide

/-! ### The Toffoli bricks (CCZ phase-polynomial word, kernel-verified) -/

/-- `T†` on ancilla₁ (`T† = T³·Z`). -/
def tDagA1 : List Gate3 := [.onA1 .T, .onA1 .T, .onA1 .T, .onA1 .Z]

/-- `T†` on ancilla₂. -/
def tDagA2 : List Gate3 := [.onA2 .T, .onA2 .T, .onA2 .T, .onA2 .Z]

/-- **The CCZ word** from the `ℤ₈` phase polynomial
`4·s·a·b = s+a+b − (s⊕a) − (a⊕b) − (s⊕b) + (s⊕a⊕b)`: `T` on each line, `T†` on each cnot-computed
pairwise XOR, `T` on the triple XOR (each XOR computed and uncomputed by cnots). -/
def cczWord : List Gate3 :=
  List.reverse
    (([.onSys .T, .onA1 .T, .onA2 .T] : List Gate3) ++
     ([.cxsa] ++ tDagA1 ++ [.cxsa]) ++
     ([.cxab] ++ tDagA2 ++ [.cxab]) ++
     ([.cxsb] ++ tDagA2 ++ [.cxsb]) ++
     ([.cxsb, .cxab, .onA2 .T, .cxab, .cxsb]))

/-- Toffoli (controls system+ancilla₁, target ancilla₂) = `H_b · CCZ · H_b`. -/
def toffSABWord : List Gate3 := .onA2 .H :: cczWord ++ [.onA2 .H]

/-- Toffoli (controls system+ancilla₂, target ancilla₁) = `H_a · CCZ · H_a`. -/
def toffSBAWord : List Gate3 := .onA1 .H :: cczWord ++ [.onA1 .H]

/-- The CCZ matrix: `(−1)^{s·a·b}` diagonal (structural conditions, kernel-friendly). -/
def cczSAB : Mat8 := Matrix.of fun o i =>
  if o = i then
    (if i.1 = 1 ∧ i.2.1 = 1 ∧ i.2.2 = 1 then CliffordTGate.ωS ^ 4 else 1)
  else 0

/-- **The CCZ word is CCZ** (kernel reduction, top-level so no elaborator budget). -/
theorem interp3_cczWord : interp3 cczWord = cczSAB := by decide +kernel

/-- The `H_b`-sandwich of CCZ is the controlled `cx01` (kernel reduction, 3 factors). -/
theorem ccz_sandwich_b : gateMatrix3 (.onA2 .H) * (cczSAB * interp3 [.onA2 .H]) =
    ctrl8 1 cnot01 := by decide +kernel

/-- The `H_a`-sandwich of CCZ is the controlled `cx10` (kernel reduction, 3 factors). -/
theorem ccz_sandwich_a : gateMatrix3 (.onA1 .H) * (cczSAB * interp3 [.onA1 .H]) =
    ctrl8 1 cnot10 := by decide +kernel

/-- **Toffoli realizes the controlled `cx01`**. -/
theorem interp3_toffSAB : interp3 toffSABWord = ctrl8 1 cnot01 := by
  rw [show toffSABWord = .onA2 .H :: (cczWord ++ [.onA2 .H]) from rfl, interp3_cons,
    interp3_append, interp3_cczWord]
  exact ccz_sandwich_b

/-- **Toffoli realizes the controlled `cx10`**. -/
theorem interp3_toffSBA : interp3 toffSBAWord = ctrl8 1 cnot10 := by
  rw [show toffSBAWord = .onA1 .H :: (cczWord ++ [.onA1 .H]) from rfl, interp3_cons,
    interp3_append, interp3_cczWord]
  exact ccz_sandwich_a

/-! ### The `|00⟩`-fixing invariant for the uncontrolled block -/

/-- `D` fixes the initialized ancilla state: its `(·, |00⟩)`-column is the `|00⟩` indicator. -/
def FixesE00 (D : Mat4) : Prop := ∀ j, D j (0, 0) = if j = (0, 0) then 1 else 0

instance (D : Mat4) : Decidable (FixesE00 D) := by unfold FixesE00; infer_instance

theorem FixesE00.one : FixesE00 1 := by decide

theorem FixesE00.mul {D₁ D₂ : Mat4} (h₁ : FixesE00 D₁) (h₂ : FixesE00 D₂) :
    FixesE00 (D₁ * D₂) := by
  intro j
  rw [Matrix.mul_apply,
    Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => by rw [h₂ k],
    Finset.sum_eq_single_of_mem ((0, 0) : Fin 2 × Fin 2) (Finset.mem_univ _)
      (fun k _ hk => by rw [if_neg hk, mul_zero]),
    if_pos rfl, mul_one]
  exact h₁ j

/-! ### The per-gate controlled lift -/

/-- **The controlled lift of a two-qubit generator**: target-diagonal gates lift uncontrolled
(their `s = 0` block fixes `|00⟩`); `X`/`Y`/`H` lift to genuinely controlled words; cnots lift to
Toffoli; the scalar `ω` lifts to `T` on the system line. -/
def ctrlLift : Gate2 → List Gate3
  | .onFst .T => [.onA1 .T]
  | .onFst .S => [.onA1 .S]
  | .onFst .Z => [.onA1 .Z]
  | .onFst .id => [.onA1 .id]
  | .onFst .omega => [.onSys .T]
  | .onFst .X => [.cxsa]
  | .onFst .Y => [.onA1 .S, .cxsa, .onA1 .S, .onA1 .Z]
  | .onFst .H => Gate2.chConjWord.map .onA1 ++ .cxsa :: Gate2.chConjInvWord.map .onA1
  | .onSnd .T => [.onA2 .T]
  | .onSnd .S => [.onA2 .S]
  | .onSnd .Z => [.onA2 .Z]
  | .onSnd .id => [.onA2 .id]
  | .onSnd .omega => [.onSys .T]
  | .onSnd .X => [.cxsb]
  | .onSnd .Y => [.onA2 .S, .cxsb, .onA2 .S, .onA2 .Z]
  | .onSnd .H => Gate2.chConjWord.map .onA2 ++ .cxsb :: Gate2.chConjInvWord.map .onA2
  | .cx01 => toffSABWord
  | .cx10 => toffSBAWord

/-- Dim-2 conjugation bricks for the `Y`-lift (kernel `decide`). -/
theorem S_conj_X_eq_Y :
    CliffordTGate.gateMatrix .S * (CliffordTGate.gateMatrix .X *
      (CliffordTGate.gateMatrix .S * CliffordTGate.gateMatrix .Z)) =
      CliffordTGate.gateMatrix .Y := by decide

theorem S_mul_S_mul_Z : CliffordTGate.gateMatrix .S *
    (CliffordTGate.gateMatrix .S * CliffordTGate.gateMatrix .Z) = 1 := by decide

/-- The `H`-conjugation at the `Mat4` level, second-ancilla flavor: the inc-29 dim-2 facts
transported through `embedSnd`. -/
theorem embedSnd_conj :
    Gate2.embedSnd (CliffordTGate.interp Gate2.chConjWord) *
      (Gate2.gateMatrix2 (.onSnd .X) * Gate2.embedSnd (CliffordTGate.interp Gate2.chConjInvWord)) =
      Gate2.gateMatrix2 (.onSnd .H) := by
  show Gate2.embedSnd (CliffordTGate.interp Gate2.chConjWord) *
    (Gate2.embedSnd (CliffordTGate.gateMatrix .X) *
      Gate2.embedSnd (CliffordTGate.interp Gate2.chConjInvWord)) =
    Gate2.embedSnd (CliffordTGate.gateMatrix .H)
  rw [← Gate2.embedSnd_mul, ← Gate2.embedSnd_mul, Gate2.chConj_conj_X]

theorem embedSnd_conj_inv :
    Gate2.embedSnd (CliffordTGate.interp Gate2.chConjWord) *
      Gate2.embedSnd (CliffordTGate.interp Gate2.chConjInvWord) = 1 := by
  rw [← Gate2.embedSnd_mul, Gate2.chConj_mul_inv, Gate2.embedSnd_one]

/-- First-ancilla flavor. -/
theorem embedFst_conj :
    Gate2.embedFst (CliffordTGate.interp Gate2.chConjWord) *
      (Gate2.gateMatrix2 (.onFst .X) * Gate2.embedFst (CliffordTGate.interp Gate2.chConjInvWord)) =
      Gate2.gateMatrix2 (.onFst .H) := by
  show Gate2.embedFst (CliffordTGate.interp Gate2.chConjWord) *
    (Gate2.embedFst (CliffordTGate.gateMatrix .X) *
      Gate2.embedFst (CliffordTGate.interp Gate2.chConjInvWord)) =
    Gate2.embedFst (CliffordTGate.gateMatrix .H)
  rw [← Gate2.embedFst_mul, ← Gate2.embedFst_mul, Gate2.chConj_conj_X]

theorem embedFst_conj_inv :
    Gate2.embedFst (CliffordTGate.interp Gate2.chConjWord) *
      Gate2.embedFst (CliffordTGate.interp Gate2.chConjInvWord) = 1 := by
  rw [← Gate2.embedFst_mul, Gate2.chConj_mul_inv, Gate2.embedFst_one]

/-- Interpretation of an `onA1`-mapped single-qubit word: `embedAnc ∘ embedFst`. -/
theorem interp3_map_onA1 (gs : List CliffordTGate) :
    interp3 (gs.map .onA1) = embedAnc (Gate2.embedFst (CliffordTGate.interp gs)) := by
  have h1 : gs.map Gate3.onA1 = (gs.map Gate2.onFst).map liftAnc := by
    rw [List.map_map]
    rfl
  rw [h1, ← embedAnc_interp2, ← Gate2.embedFst_interp]

theorem interp3_map_onA2 (gs : List CliffordTGate) :
    interp3 (gs.map .onA2) = embedAnc (Gate2.embedSnd (CliffordTGate.interp gs)) := by
  have h1 : gs.map Gate3.onA2 = (gs.map Gate2.onSnd).map liftAnc := by
    rw [List.map_map]
    rfl
  rw [h1, ← embedAnc_interp2, ← Gate2.embedSnd_interp]

/-- **The per-gate lift specification**: each generator's lift interprets to a system-controlled
block `ctrl8 D (gateMatrix2 g)` with `D` fixing `|00⟩`, within 30 gates. -/
theorem ctrlLift_gate_spec (g : Gate2) :
    ∃ D : Mat4, interp3 (ctrlLift g) = ctrl8 D (Gate2.gateMatrix2 g) ∧ FixesE00 D ∧
      (ctrlLift g).length ≤ 30 := by
  cases g with
  | onFst c =>
    cases c with
    | H =>
      refine ⟨1, ?_, FixesE00.one, by decide⟩
      show interp3 (Gate2.chConjWord.map .onA1 ++ .cxsa :: Gate2.chConjInvWord.map .onA1) = _
      rw [interp3_append, interp3_cons, interp3_map_onA1, interp3_map_onA1,
        show gateMatrix3 .cxsa = cnotSA from rfl, cnotSA_eq_ctrl8,
        embedAnc_eq_ctrl8, embedAnc_eq_ctrl8, ctrl8_mul, ctrl8_mul,
        show (Gate2.embedFst (CliffordTGate.interp Gate2.chConjWord) * (1 *
          Gate2.embedFst (CliffordTGate.interp Gate2.chConjInvWord))) = 1 from
            (congrArg (Gate2.embedFst (CliffordTGate.interp Gate2.chConjWord) * ·)
              (one_mul _)).trans embedFst_conj_inv,
        embedFst_conj]
    | T => exact ⟨Gate2.gateMatrix2 (.onFst .T),
        (mul_one _).trans (embedAnc_eq_ctrl8 _), by decide, by decide⟩
    | S => exact ⟨Gate2.gateMatrix2 (.onFst .S),
        (mul_one _).trans (embedAnc_eq_ctrl8 _), by decide, by decide⟩
    | Z => exact ⟨Gate2.gateMatrix2 (.onFst .Z),
        (mul_one _).trans (embedAnc_eq_ctrl8 _), by decide, by decide⟩
    | id => exact ⟨Gate2.gateMatrix2 (.onFst .id),
        (mul_one _).trans (embedAnc_eq_ctrl8 _), by decide, by decide⟩
    | omega =>
      exact ⟨1, (mul_one _).trans embedSys_T_eq_ctrl8_omega_fst, FixesE00.one, by decide⟩
    | X =>
      exact ⟨1, (mul_one _).trans cnotSA_eq_ctrl8, FixesE00.one, by decide⟩
    | Y =>
      refine ⟨1, ?_, FixesE00.one, by decide⟩
      show embedAnc (Gate2.gateMatrix2 (.onFst .S)) * (cnotSA *
        (embedAnc (Gate2.gateMatrix2 (.onFst .S)) * (embedAnc (Gate2.gateMatrix2 (.onFst .Z)) *
          1))) = ctrl8 1 (Gate2.gateMatrix2 (.onFst .Y))
      rw [show embedAnc (Gate2.gateMatrix2 (.onFst .Z)) * 1
          = embedAnc (Gate2.gateMatrix2 (.onFst .Z)) from mul_one _,
        cnotSA_eq_ctrl8, embedAnc_eq_ctrl8, embedAnc_eq_ctrl8,
        ctrl8_mul, ctrl8_mul, ctrl8_mul,
        show Gate2.gateMatrix2 (.onFst .S) * ((1 : Mat4) * (Gate2.gateMatrix2 (.onFst .S) *
          Gate2.gateMatrix2 (.onFst .Z))) = 1 from
          (congrArg (Gate2.gateMatrix2 (.onFst .S) * ·) (one_mul _)).trans (by
            show Gate2.embedFst (CliffordTGate.gateMatrix .S) *
              (Gate2.embedFst (CliffordTGate.gateMatrix .S) *
                Gate2.embedFst (CliffordTGate.gateMatrix .Z)) = 1
            rw [← Gate2.embedFst_mul, ← Gate2.embedFst_mul, S_mul_S_mul_Z, Gate2.embedFst_one]),
        show Gate2.gateMatrix2 (.onFst .S) * (Gate2.gateMatrix2 (.onFst .X) *
          (Gate2.gateMatrix2 (.onFst .S) * Gate2.gateMatrix2 (.onFst .Z))) =
          Gate2.gateMatrix2 (.onFst .Y) from by
            show Gate2.embedFst (CliffordTGate.gateMatrix .S) *
              (Gate2.embedFst (CliffordTGate.gateMatrix .X) *
                (Gate2.embedFst (CliffordTGate.gateMatrix .S) *
                  Gate2.embedFst (CliffordTGate.gateMatrix .Z))) =
              Gate2.gateMatrix2 (.onFst .Y)
            rw [← Gate2.embedFst_mul, ← Gate2.embedFst_mul, ← Gate2.embedFst_mul, S_conj_X_eq_Y]
            rfl]
  | onSnd c =>
    cases c with
    | H =>
      refine ⟨1, ?_, FixesE00.one, by decide⟩
      show interp3 (Gate2.chConjWord.map .onA2 ++ .cxsb :: Gate2.chConjInvWord.map .onA2) = _
      rw [interp3_append, interp3_cons, interp3_map_onA2, interp3_map_onA2,
        show gateMatrix3 .cxsb = cnotSB from rfl, cnotSB_eq_ctrl8,
        embedAnc_eq_ctrl8, embedAnc_eq_ctrl8, ctrl8_mul, ctrl8_mul,
        show (Gate2.embedSnd (CliffordTGate.interp Gate2.chConjWord) * (1 *
          Gate2.embedSnd (CliffordTGate.interp Gate2.chConjInvWord))) = 1 from
            (congrArg (Gate2.embedSnd (CliffordTGate.interp Gate2.chConjWord) * ·)
              (one_mul _)).trans embedSnd_conj_inv,
        embedSnd_conj]
    | T => exact ⟨Gate2.gateMatrix2 (.onSnd .T),
        (mul_one _).trans (embedAnc_eq_ctrl8 _), by decide, by decide⟩
    | S => exact ⟨Gate2.gateMatrix2 (.onSnd .S),
        (mul_one _).trans (embedAnc_eq_ctrl8 _), by decide, by decide⟩
    | Z => exact ⟨Gate2.gateMatrix2 (.onSnd .Z),
        (mul_one _).trans (embedAnc_eq_ctrl8 _), by decide, by decide⟩
    | id => exact ⟨Gate2.gateMatrix2 (.onSnd .id),
        (mul_one _).trans (embedAnc_eq_ctrl8 _), by decide, by decide⟩
    | omega =>
      exact ⟨1, (mul_one _).trans embedSys_T_eq_ctrl8_omega_snd, FixesE00.one, by decide⟩
    | X =>
      exact ⟨1, (mul_one _).trans cnotSB_eq_ctrl8, FixesE00.one, by decide⟩
    | Y =>
      refine ⟨1, ?_, FixesE00.one, by decide⟩
      show embedAnc (Gate2.gateMatrix2 (.onSnd .S)) * (cnotSB *
        (embedAnc (Gate2.gateMatrix2 (.onSnd .S)) * (embedAnc (Gate2.gateMatrix2 (.onSnd .Z)) *
          1))) = ctrl8 1 (Gate2.gateMatrix2 (.onSnd .Y))
      rw [show embedAnc (Gate2.gateMatrix2 (.onSnd .Z)) * 1
          = embedAnc (Gate2.gateMatrix2 (.onSnd .Z)) from mul_one _,
        cnotSB_eq_ctrl8, embedAnc_eq_ctrl8, embedAnc_eq_ctrl8,
        ctrl8_mul, ctrl8_mul, ctrl8_mul,
        show Gate2.gateMatrix2 (.onSnd .S) * ((1 : Mat4) * (Gate2.gateMatrix2 (.onSnd .S) *
          Gate2.gateMatrix2 (.onSnd .Z))) = 1 from
          (congrArg (Gate2.gateMatrix2 (.onSnd .S) * ·) (one_mul _)).trans (by
            show Gate2.embedSnd (CliffordTGate.gateMatrix .S) *
              (Gate2.embedSnd (CliffordTGate.gateMatrix .S) *
                Gate2.embedSnd (CliffordTGate.gateMatrix .Z)) = 1
            rw [← Gate2.embedSnd_mul, ← Gate2.embedSnd_mul, S_mul_S_mul_Z, Gate2.embedSnd_one]),
        show Gate2.gateMatrix2 (.onSnd .S) * (Gate2.gateMatrix2 (.onSnd .X) *
          (Gate2.gateMatrix2 (.onSnd .S) * Gate2.gateMatrix2 (.onSnd .Z))) =
          Gate2.gateMatrix2 (.onSnd .Y) from by
            show Gate2.embedSnd (CliffordTGate.gateMatrix .S) *
              (Gate2.embedSnd (CliffordTGate.gateMatrix .X) *
                (Gate2.embedSnd (CliffordTGate.gateMatrix .S) *
                  Gate2.embedSnd (CliffordTGate.gateMatrix .Z))) =
              Gate2.gateMatrix2 (.onSnd .Y)
            rw [← Gate2.embedSnd_mul, ← Gate2.embedSnd_mul, ← Gate2.embedSnd_mul, S_conj_X_eq_Y]
            rfl]
  | cx01 =>
    exact ⟨1, by rw [show Gate2.gateMatrix2 .cx01 = cnot01 from rfl]; exact interp3_toffSAB,
      FixesE00.one, by decide⟩
  | cx10 =>
    exact ⟨1, by rw [show Gate2.gateMatrix2 .cx10 = cnot10 from rfl]; exact interp3_toffSBA,
      FixesE00.one, by decide⟩

/-- The word-level controlled lift. -/
def ctrlLiftWord (w : List Gate2) : List Gate3 := w.flatMap ctrlLift

/-- **The controlled-lift theorem**: every two-qubit word `w` lifts to a three-qubit word of
length `≤ 30·|w|` interpreting to `ctrl8 D (interp2 w)` for a `|00⟩`-fixing `D`. Applied to the
column-lemma word for `|v⟩`, this is the KMM controlled-`C`. -/
theorem ctrlLift_word_spec (w : List Gate2) :
    ∃ D : Mat4, interp3 (ctrlLiftWord w) = ctrl8 D (Gate2.interp2 w) ∧ FixesE00 D ∧
      (ctrlLiftWord w).length ≤ 30 * w.length := by
  induction w with
  | nil =>
    refine ⟨1, ?_, FixesE00.one, by simp [ctrlLiftWord]⟩
    rw [show ctrlLiftWord [] = [] from rfl, interp3_nil, Gate2.interp2_nil, ctrl8_one_one]
  | cons g gs ih =>
    obtain ⟨D', hD', hfix', hlen'⟩ := ih
    obtain ⟨Dg, hDg, hfixg, hleng⟩ := ctrlLift_gate_spec g
    refine ⟨Dg * D', ?_, hfixg.mul hfix', ?_⟩
    · rw [show ctrlLiftWord (g :: gs) = ctrlLift g ++ ctrlLiftWord gs from
        List.flatMap_cons .., interp3_append, hDg, hD', ctrl8_mul, Gate2.interp2_cons]
    · rw [show ctrlLiftWord (g :: gs) = ctrlLift g ++ ctrlLiftWord gs from
        List.flatMap_cons ..]
      rw [List.length_append, List.length_cons]
      omega

end Gate3
end SKEFTHawking.RossSelinger
