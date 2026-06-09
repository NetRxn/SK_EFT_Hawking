/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 3) — the unconditional normalized ancilla state column

`AncillaCompletion.lean` established, unconditionally (Lagrange four-squares), that the ancilla
"completion" entries solve the ℤ[ω] norm equation `normSq u + normSq t₁ + normSq t₂ = 2^k`. This file
lifts that integer identity to the **quantum-amplitude level** over `ZOmegaSqrt2 = ℤ[ω][1/√2]`:
the cleared amplitude column `(u, t₁, t₂)/√2^k` is a **unit vector** (`Σ |·|² = 1`), i.e. a genuine
normalized state of the (system + ancilla) register.

Mirrors the shipped single-qubit `KMM.colNormSq` (`normSq (mk u k) + normSq (mk t k) = 1`); the
three-entry ancilla version is the natural extension, and combining it with the keystone gives the
**unconditional** existence of the normalized ancilla state for every integer-residual approximant —
no relative-norm / prime-density hypothesis (cf. the ancilla-free `rossSelinger_synth_of_residual`).

## Headlines

  * `ZOmegaSqrt2.mk_add_same` — same-denominator addition `mk a k + mk b k = mk (a+b) k`.
  * `ancillaColNormSq` — the three-entry column normalization (extends `KMM.colNormSq`).
  * `exists_ancilla_normalized_column` — **for an approximant `u` with integer `normSq u = m ≤ 2^k`,
    there EXIST ancilla entries `t₁, t₂` making `(u,t₁,t₂)/√2^k` a unit vector, UNCONDITIONALLY.**
    The normalized (system+ancilla) quantum state realizing the system amplitude `u/√2^k` always
    exists — the KMM-ancilla "existence" (DR rec. #3) at the amplitude level.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.AncillaCompletion
import SKEFTHawking.FKLW.RossSelinger.GridSynth

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmegaSqrt2

/-- **Same-denominator addition**: `mk a k + mk b k = mk (a + b) k`. -/
theorem mk_add_same (a b : ZOmega) (k : ℕ) : mk a k + mk b k = mk (a + b) k := by
  rw [mk_add, mk_eq_mk_iff]; ring

end ZOmegaSqrt2

open ZOmegaSqrt2

/-- **Three-entry column normalization** (the ancilla extension of `KMM.colNormSq`): when the ℤ[ω]
norm equation `u·u* + t₁·t₁* + t₂·t₂* = √2^{2k}` (`= ⟨0,0,0,2^k⟩`) holds, the cleared amplitude
column `(mk u k, mk t₁ k, mk t₂ k)` is a unit vector. -/
theorem ancillaColNormSq (u t₁ t₂ : ZOmega) (k : ℕ)
    (h : ZOmega.normSq u + ZOmega.normSq t₁ + ZOmega.normSq t₂ = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega)) :
    normSq (mk u k) + normSq (mk t₁ k) + normSq (mk t₂ k) = 1 := by
  rw [normSq_mk, normSq_mk, normSq_mk, mk_add_same, mk_add_same, h,
      ← sqrt2_pow_two_mul k, one_def, mk_eq_mk_iff]
  ring

/-- **`((2^k : ℕ) : ZOmega) = ⟨0,0,0,2^k⟩`** — the nat-cast of `2^k` is the rational integer `2^k`. -/
theorem natCast_two_pow_eq (k : ℕ) : ((2 ^ k : ℕ) : ZOmega) = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega) := by
  show ZOmega.ofInt ((2 ^ k : ℕ) : ℤ) = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega)
  rw [ZOmega.ofInt]
  congr 1

/-- **Unconditional normalized ancilla state (the KMM-ancilla existence, amplitude level).** For an
approximant `u : ℤ[ω]` whose squared modulus is the rational integer `m ≤ 2^k` (the √2-balanced
approximant the KMM rounding targets), there EXIST ancilla completion entries `t₁, t₂ ∈ ℤ[ω]` such
that the cleared column `(u, t₁, t₂)/√2^k` is a **unit vector** — a genuine normalized state of the
(system + ancilla) register realizing the system amplitude `u/√2^k`. **UNCONDITIONALLY** — no
relative-norm / prime-density hypothesis (the residual `2^k − m ∈ ℕ` is a sum of two relative norms
by Lagrange `Nat.sum_four_squares`, `exists_two_relativeNorms_of_nat`). Contrast the ancilla-free
`rossSelinger_synth_of_residual`, whose unit column requires a single relative norm (conditional). -/
theorem exists_ancilla_normalized_column {u : ZOmega} {k m : ℕ}
    (hm : ZOmega.normSq u = (m : ZOmega)) (hmk : m ≤ 2 ^ k) :
    ∃ t₁ t₂ : ZOmega,
      normSq (mk u k) + normSq (mk t₁ k) + normSq (mk t₂ k) = 1 := by
  obtain ⟨t₁, t₂, ht⟩ := ancilla_completion_of_nat_residual hm hmk
  refine ⟨t₁, t₂, ancillaColNormSq u t₁ t₂ k ?_⟩
  rw [ht, natCast_two_pow_eq]

/-- **The KMM (arXiv:1212.0822 §2.1) ancilla state exists, unconditionally, for the z-rotation target.**
Faithful to the primary construction: the Gaussian-integer approximant `u = m₁ + m₂·i`
(`m₁ = ⌊2^k cos φ⌋`, `m₂ = ⌊2^k sin φ⌋`, so `u/2^k ≈ e^{iφ}`) has integer squared modulus
`|u|² = m₁² + m₂²`; whenever it lies in the disk (`m₁² + m₂² ≤ 4^k`, the §5 rounding constraint), the
KMM two-ancilla state column `|v⟩ = (1/2^k)(u, 0, t₁, t₂)` is a **unit vector** — the completion
entries `t₁ = a + b·i`, `t₂ = c + d·i` exist by Lagrange four-squares (the keystone), with NO
prime-density hypothesis. (Denominator exponent `2k`: `2^{2k} = 4^k`. This is the exact state circuit
C of KMM prepares; the remaining brick is C's Clifford+T synthesis.) -/
theorem kmm_ancilla_state_exists (m₁ m₂ : ℤ) (k : ℕ) (h : m₁ ^ 2 + m₂ ^ 2 ≤ 4 ^ k) :
    ∃ t₁ t₂ : ZOmega,
      normSq (mk ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2) (2 * k))
        + normSq (mk t₁ (2 * k)) + normSq (mk t₂ (2 * k)) = 1 := by
  have hpos : (0 : ℤ) ≤ m₁ ^ 2 + m₂ ^ 2 := add_nonneg (sq_nonneg m₁) (sq_nonneg m₂)
  have hu : ZOmega.normSq ((m₁ : ZOmega) + (m₂ : ZOmega) * ZOmega.ω ^ 2)
      = (((m₁ ^ 2 + m₂ ^ 2).toNat : ℕ) : ZOmega) := by
    rw [normSq_real_sumSq (conj_intCast m₁) (conj_intCast m₂),
        ← Int.cast_natCast (R := ZOmega) (m₁ ^ 2 + m₂ ^ 2).toNat,
        Int.toNat_of_nonneg hpos]
    push_cast; ring
  have hmk : (m₁ ^ 2 + m₂ ^ 2).toNat ≤ 2 ^ (2 * k) := by
    rw [pow_mul, show (2 : ℕ) ^ 2 = 4 from rfl, Int.toNat_le]
    push_cast; exact h
  exact exists_ancilla_normalized_column hu hmk

end SKEFTHawking.RossSelinger
