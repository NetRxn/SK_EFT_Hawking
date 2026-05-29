/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — Matsumoto-Amano syllable strip (the recursion step)

The MA base-coverage recursion descends on `kSO3` (`BlochMap.lean`) by stripping a
leading syllable `s ∈ {T, HT, SHT}`. This file ships the **algebraic half** of the
recursion step (the `kSO3`-decrease *existence* — the residue crux — is the next
sub-build):

  * `IsCliffordTRealizable.adjoint` — realizability is closed under Hermitian
    adjoint (every gate's adjoint is a short Clifford+T word: `T† = Z·S·T`,
    `S† = Z·S`, `ω† = ω⁷`, the Paulis self-adjoint).
  * `Syllable` (`T | HT | SHT`) + `sylWord`/`sylMat`.
  * `stripMat s M := (sylMat s)† · M` — the leading-syllable strip.
  * `interp_sylWord_stripMat` — `interp (sylWord s) · stripMat s M = M` (the strip
    is exactly invertible; `sylMat s` is unitary).
  * `stripMat_realizable` — the strip preserves Clifford+T-realizability.
  * `selectSyllable` — the computable selector (the `kSO3`-reducing syllable, which
    by `kmm_ma_step_residue.py` is U(2)-residue-mod-2-determined and unique).

## References

  * Giles-Selinger 2013 (arXiv:1312.6584) — MA normal form `(T|ε)(HT|SHT)*C`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, for finite `decide`).
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.BlochHomomorphism

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-! ## Realizability is closed under adjoint -/

/-- **Per-gate Hermitian adjoint as a (short) Clifford+T word.** `T† = Z·S·T`,
`S† = Z·S`, `ω† = ω⁷`; the Paulis and `H` are self-adjoint. -/
def gateAdjWord : CliffordTGate → List CliffordTGate
  | .H => [.H]
  | .X => [.X]
  | .Y => [.Y]
  | .Z => [.Z]
  | .id => [.id]
  | .S => [.Z, .S]
  | .T => [.Z, .S, .T]
  | .omega => List.replicate 7 .omega

set_option maxRecDepth 4000 in
/-- **`gateAdjWord` realizes the adjoint gate matrix**. -/
theorem interp_gateAdjWord (g : CliffordTGate) :
    interp (gateAdjWord g) = ZOmegaSqrt2.adjoint (gateMatrix g) := by
  cases g <;> decide

/-- **Adjoint of a gate sequence** (reverse + per-gate adjoint word). -/
def adjointWord : List CliffordTGate → List CliffordTGate
  | [] => []
  | g :: gs => adjointWord gs ++ gateAdjWord g

/-- **`adjointWord` realizes the Hermitian adjoint of the interpretation**:
`interp (adjointWord gs) = (interp gs)†`. Anti-homomorphism induction. -/
theorem interp_adjointWord (gs : List CliffordTGate) :
    interp (adjointWord gs) = ZOmegaSqrt2.adjoint (interp gs) := by
  induction gs with
  | nil => show interp [] = ZOmegaSqrt2.adjoint (interp []); rw [interp_nil, ZOmegaSqrt2.adjoint_one]
  | cons g gs ih =>
    show interp (adjointWord gs ++ gateAdjWord g)
        = ZOmegaSqrt2.adjoint (gateMatrix g * interp gs)
    rw [interp_append, ih, interp_gateAdjWord, ZOmegaSqrt2.adjoint_mul]

/-- **Realizability is closed under Hermitian adjoint.** -/
theorem IsCliffordTRealizable.adjoint {M : Mat2} (h : IsCliffordTRealizable M) :
    IsCliffordTRealizable (ZOmegaSqrt2.adjoint M) := by
  obtain ⟨gs, hgs⟩ := h
  exact ⟨adjointWord gs, by rw [interp_adjointWord, hgs]⟩

/-! ## Matsumoto-Amano syllables and the strip -/

/-- **The three MA leading syllables** `(T | HT | SHT)` (Giles-Selinger Conv 7.9). -/
inductive Syllable : Type
  | T : Syllable
  | HT : Syllable
  | SHT : Syllable
  deriving DecidableEq, Repr

/-- **Syllable as a gate word.** -/
def sylWord : Syllable → List CliffordTGate
  | .T => [.T]
  | .HT => [.H, .T]
  | .SHT => [.S, .H, .T]

/-- **Syllable matrix** = interpretation of its word. -/
def sylMat (s : Syllable) : Mat2 := interp (sylWord s)

/-- **Every syllable is at most 3 gates** (the `3·k` part of the MA length bound). -/
theorem sylWord_length_le (s : Syllable) : (sylWord s).length ≤ 3 := by
  cases s <;> decide

set_option maxRecDepth 4000 in
/-- **Syllable matrices are unitary** (right inverse via adjoint). -/
theorem sylMat_mul_adjoint (s : Syllable) :
    sylMat s * ZOmegaSqrt2.adjoint (sylMat s) = 1 := by
  cases s <;> (unfold sylMat; decide)

/-- **The leading-syllable strip** `stripMat s M := (sylMat s)† · M`. Removes the
leading syllable; the recursion descends on `kSO3 (stripMat s M)`. -/
def stripMat (s : Syllable) (M : Mat2) : Mat2 := ZOmegaSqrt2.adjoint (sylMat s) * M

/-- **The strip is exactly invertible**: prepending the syllable's gates to a word
for `stripMat s M` recovers `M`. (`sylMat s` unitary.) -/
theorem interp_sylWord_stripMat (s : Syllable) (M : Mat2) :
    interp (sylWord s) * stripMat s M = M := by
  calc interp (sylWord s) * stripMat s M
      = sylMat s * (ZOmegaSqrt2.adjoint (sylMat s) * M) := rfl
    _ = (sylMat s * ZOmegaSqrt2.adjoint (sylMat s)) * M := (Matrix.mul_assoc _ _ _).symm
    _ = (1 : Mat2) * M := congrArg (· * M) (sylMat_mul_adjoint s)
    _ = M := Matrix.one_mul M

/-- **The strip preserves Clifford+T-realizability.** -/
theorem stripMat_realizable {M : Mat2} (s : Syllable) (h : IsCliffordTRealizable M) :
    IsCliffordTRealizable (stripMat s M) :=
  IsCliffordTRealizable.mul
    (IsCliffordTRealizable.adjoint (⟨sylWord s, rfl⟩ : IsCliffordTRealizable (sylMat s))) h

/-! ## The computable syllable selector -/

/-- **The `kSO3`-reducing syllable selector** (computable). Returns the first
syllable `s` whose strip strictly lowers `kSO3`. By `kmm_ma_step_residue.py` this
is U(2)-residue-mod-2-determined and (for non-Clifford realizable `M`) unique; the
`ma_step` existence theorem (that this `find?` succeeds when `kSO3 M ≥ 1`) is the
residue crux shipped next. -/
def selectSyllable (M : Mat2) : Option Syllable :=
  [Syllable.T, Syllable.HT, Syllable.SHT].find?
    (fun s => decide (kSO3 (stripMat s M) < kSO3 M))

/-- **Soundness of the selector**: if it returns `s`, then `s` strictly lowers
`kSO3`. (From `List.find?_some`.) -/
theorem selectSyllable_lt {M : Mat2} {s : Syllable} (h : selectSyllable M = some s) :
    kSO3 (stripMat s M) < kSO3 M := by
  have := List.find?_some h
  simpa using this

end KMM

end SKEFTHawking.RossSelinger
