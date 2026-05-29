/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — KMM reduction step: algebraic spine

Ships the **algebraically-verified backbone** of the KMM exact-synthesis
recursion (arXiv:1206.5236, Algorithm 1) on the runtime ring. The KMM
step writes a unitary `M` as `M = T^(8−j) · H · (H · T^j · M)`, peeling a
`H·T^j` factor; the residual `H·T^j·M` has strictly smaller `sde` for the
correct `j` (KMM Lemma 3 — the *termination* fact, deferred). The
*correctness* of the peel is purely algebraic (`H² = I`, `T⁸ = I`) and is
discharged here in full:

  * `gateMatrix_T_pow_eight : gateMatrix T ^ 8 = 1`  (`T = diag(1, ω)`,
    `ω⁸ = 1`).
  * `reconWord j` — the reconstruction word `T^(8−j) ++ [H]` whose
    interpretation left-inverts `H · T^j`.
  * `interp_reconWord_mul` — **the reduction-step correctness identity**:
    `interp (reconWord j) · (H · T^j · M) = M` for `j ≤ 8`. This is what
    makes the recursion reconstruct `M` exactly.
  * `isCliffordTRealizable_H_T_pow_mul` — realizability is preserved by
    the peel, so the recursive call stays in-domain.

## Remaining (the genuinely hard KMM core — deferred)

  * KMM Lemma 3: for `sde M ≥ 4`, some `j ∈ {0,1,2,3}` strictly reduces
    `sde` (residue argument in `ZOmega / √2·ZOmega`). Needed for
    termination / fuel-sufficiency.
  * `cliffordLookup` coverage on the `sde ≤ 3` orbit. Needed for the base
    case.

Together these discharge `KMMReductionExists` constructively. The spine
below is the algebraic half, complete and kernel-pure.

## References

  * Pre-Implementation Research Dossier §3.3.
  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) Algorithm 1.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.SdeMatrix

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate

/-! ## 1. `T` has order 8 -/

/-- **`T⁸ = I`**: the π/8 gate has order 8 (`ω⁸ = 1`). Proved from the
already-verified relations `T² = S`, `S² = Z`, `Z² = I` (avoiding a deep
`decide` on the 8-fold matrix power). -/
theorem gateMatrix_T_pow_eight : gateMatrix .T ^ 8 = 1 := by
  have hT2 : gateMatrix .T ^ 2 = gateMatrix .S := by rw [pow_two]; exact T_mul_T_eq_S
  have hT4 : gateMatrix .T ^ 4 = gateMatrix .Z := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hT2, pow_two]; exact S_mul_S_eq_Z
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hT4, pow_two]; exact Z_mul_Z

/-! ## 2. Interpretation of `T`-runs -/

/-- **Interpretation of a run of `T` gates**: `interp (replicate n T) = (gateMatrix T)^n`. -/
theorem interp_replicate_T (n : ℕ) :
    interp (List.replicate n .T) = gateMatrix .T ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, interp_cons, ih]
    exact (pow_succ' _ _).symm

/-! ## 3. The reconstruction word and the reduction-step identity -/

/-- **Reconstruction word** for the KMM peel of `H·T^j`: `T^(8−j) ++ [H]`.
Its interpretation is the left inverse `T^(8−j) · H` of `H · T^j`
(modulo `T⁸ = I`). -/
def reconWord (j : ℕ) : List CliffordTGate := List.replicate (8 - j) .T ++ [.H]

/-- **Interpretation of the reconstruction word**: `T^(8−j) · H`. -/
theorem interp_reconWord (j : ℕ) :
    interp (reconWord j) = gateMatrix .T ^ (8 - j) * gateMatrix .H := by
  rw [reconWord, interp_append, interp_replicate_T, interp_singleton]

/-- **The reconstruction word left-inverts `H·T^j`**:
`interp (reconWord j) · (H · T^j) = I` for `j ≤ 8`. Purely algebraic —
`H² = I` (`H_mul_H`) and `T⁸ = I` (`gateMatrix_T_pow_eight`). -/
theorem reconWord_inv (j : ℕ) (hj : j ≤ 8) :
    interp (reconWord j) * (gateMatrix .H * gateMatrix .T ^ j) = 1 := by
  rw [interp_reconWord]
  -- Matrix `*` here is the heterogeneous `Matrix.instHMul`; generic/`Matrix`
  -- associativity & `one_mul` do NOT rw-match it, but they typecheck as TERMS
  -- (the `Matrix.mul_assoc _ _ _` idiom, as in `interp_append`). So every
  -- matrix step is term-justified via `congrArg`; only the Nat exponent uses `rw`.
  calc gateMatrix .T ^ (8 - j) * gateMatrix .H * (gateMatrix .H * gateMatrix .T ^ j)
      = gateMatrix .T ^ (8 - j) * (gateMatrix .H * (gateMatrix .H * gateMatrix .T ^ j)) :=
        Matrix.mul_assoc _ _ _
    _ = gateMatrix .T ^ (8 - j) * (gateMatrix .H * gateMatrix .H * gateMatrix .T ^ j) :=
        congrArg (gateMatrix .T ^ (8 - j) * ·) (Matrix.mul_assoc _ _ _).symm
    _ = gateMatrix .T ^ (8 - j) * ((1 : Mat2) * gateMatrix .T ^ j) :=
        congrArg (gateMatrix .T ^ (8 - j) * ·) (congrArg (· * gateMatrix .T ^ j) H_mul_H)
    _ = gateMatrix .T ^ (8 - j) * gateMatrix .T ^ j :=
        congrArg (gateMatrix .T ^ (8 - j) * ·) (one_mul _)
    _ = gateMatrix .T ^ ((8 - j) + j) := (pow_add _ _ _).symm
    _ = gateMatrix .T ^ 8 := by rw [Nat.sub_add_cancel hj]
    _ = 1 := gateMatrix_T_pow_eight

/-- **Reduction-step correctness**: peeling `H·T^j` and prepending the
reconstruction word recovers `M` exactly, for any `j ≤ 8`:

  `interp (reconWord j) · (H · T^j · M) = M`.

This is the engine of `kmmReduce_correct`. -/
theorem interp_reconWord_mul (j : ℕ) (hj : j ≤ 8) (M : Mat2) :
    interp (reconWord j) * (gateMatrix .H * gateMatrix .T ^ j * M) = M := by
  calc interp (reconWord j) * (gateMatrix .H * gateMatrix .T ^ j * M)
      = interp (reconWord j) * (gateMatrix .H * gateMatrix .T ^ j) * M :=
        (Matrix.mul_assoc _ _ _).symm
    _ = (1 : Mat2) * M := congrArg (· * M) (reconWord_inv j hj)
    _ = M := one_mul _

/-! ## 4. Realizability is preserved by the peel -/

/-- **Powers of a gate matrix are realizable**. -/
theorem isCliffordTRealizable_gate_pow (g : CliffordTGate) (n : ℕ) :
    IsCliffordTRealizable (gateMatrix g ^ n) := by
  induction n with
  | zero => simpa using IsCliffordTRealizable.one
  | succ m ih =>
    rw [pow_succ]
    exact ih.mul (gateMatrix_isCliffordTRealizable g)

/-- **The peel `M ↦ H · T^j · M` preserves Clifford+T-realizability**, so
the KMM recursion stays in-domain. -/
theorem isCliffordTRealizable_H_T_pow_mul {M : Mat2} (j : ℕ)
    (hM : IsCliffordTRealizable M) :
    IsCliffordTRealizable (gateMatrix .H * gateMatrix .T ^ j * M) :=
  ((gateMatrix_isCliffordTRealizable .H).mul
    (isCliffordTRealizable_gate_pow .T j)).mul hM

end KMM

end SKEFTHawking.RossSelinger
