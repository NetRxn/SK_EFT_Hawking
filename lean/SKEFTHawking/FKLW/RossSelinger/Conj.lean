/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — complex conjugation + squared modulus on ZOmegaSqrt2

KMM exact synthesis (arXiv:1206.5236) tracks the smallest denominator
exponent of the **squared modulus** `|z|² = z · conj(z)` of the matrix
entries (Lemma 3 reduces `sde(|z|²)`; Lemma 4 uses `|z|² + |w|² = 1`).
This file lifts complex conjugation from `ZOmega` to the runtime ring
`ZOmegaSqrt2` and defines `normSq z = z * conj z`.

Conjugation is the Galois automorphism `σ₇` of `ℤ[ω]` (`ZOmega.conj`); it
fixes `√2 = ω − ω³` (`ZOmega.conj_sqrt2`), so it descends to the
localization `ℤ[ω][1/√2]`: `conj (z / √2^k) = conj z / √2^k`, i.e. on
`Frac` representatives `(num, den) ↦ (conj num, den)`, which respects the
`Frac` equivalence.

## Headline definitions

  * `ZOmega.conj_sqrt2_pow` — `conj (√2^k) = √2^k`.
  * `ZOmegaSqrt2.conj : ZOmegaSqrt2 → ZOmegaSqrt2` — lifted conjugation,
    a ring anti-involution that is in fact a ring hom (ℤ[ω] is commutative).
  * `ZOmegaSqrt2.conj_mk`, `conj_of`, `conj_add`, `conj_mul`, `conj_conj`.
  * `ZOmegaSqrt2.normSq z := z * conj z` — the squared modulus.

## References

  * Kliuchnikov-Maslov-Mosca 2013 (arXiv:1206.5236) §2–3 (sde of `|z|²`,
    Lemmas 3 & 4).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ZOmegaSqrt2

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **Conjugation fixes powers of `√2`**: `conj (√2^k) = √2^k`. -/
theorem conj_sqrt2_pow (k : ℕ) : conj (sqrt2 ^ k) = sqrt2 ^ k := by
  induction k with
  | zero => simp [conj_one]
  | succ n ih => rw [pow_succ, conj_mul, ih, conj_sqrt2]

end ZOmega

namespace ZOmegaSqrt2

/-- **Complex conjugation on `ZOmegaSqrt2`**, lifted from `ZOmega.conj`
through the quotient. On a representative `(num, den)` it is
`(conj num, den)`; this respects `Frac.equiv` because `conj` is a ring
hom fixing every power of `√2`. -/
def conj : ZOmegaSqrt2 → ZOmegaSqrt2 :=
  Quotient.map (fun f => (⟨ZOmega.conj f.num, f.den⟩ : Frac)) (by
    rintro a b hab
    show ZOmega.conj a.num * ZOmega.sqrt2 ^ b.den
       = ZOmega.conj b.num * ZOmega.sqrt2 ^ a.den
    have hab' : a.num * ZOmega.sqrt2 ^ b.den = b.num * ZOmega.sqrt2 ^ a.den := hab
    have h := congrArg ZOmega.conj hab'
    rwa [ZOmega.conj_mul, ZOmega.conj_mul, ZOmega.conj_sqrt2_pow,
         ZOmega.conj_sqrt2_pow] at h)

@[simp] theorem conj_mk (z : ZOmega) (k : ℕ) :
    conj (mk z k) = mk (ZOmega.conj z) k := rfl

@[simp] theorem conj_of (z : ZOmega) : conj (of z) = of (ZOmega.conj z) := by
  rw [of_def, conj_mk, of_def]

@[simp] theorem conj_zero : conj (0 : ZOmegaSqrt2) = 0 := by
  rw [zero_def, conj_mk, ZOmega.conj_zero]

@[simp] theorem conj_one : conj (1 : ZOmegaSqrt2) = 1 := by
  rw [one_def, conj_mk, ZOmega.conj_one]

/-- **`conj` is additive**. -/
theorem conj_add (x y : ZOmegaSqrt2) : conj (x + y) = conj x + conj y := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      obtain ⟨za, ka⟩ := a; obtain ⟨zb, kb⟩ := b
      show conj (mk za ka + mk zb kb)
         = conj (mk za ka) + conj (mk zb kb)
      simp only [mk_add, conj_mk, ZOmega.conj_add, ZOmega.conj_mul, ZOmega.conj_sqrt2_pow]

/-- **`conj` is multiplicative** (ℤ[ω] is commutative, so it is a genuine
ring hom, not merely an anti-hom). -/
theorem conj_mul (x y : ZOmegaSqrt2) : conj (x * y) = conj x * conj y := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      obtain ⟨za, ka⟩ := a; obtain ⟨zb, kb⟩ := b
      show conj (mk za ka * mk zb kb)
         = conj (mk za ka) * conj (mk zb kb)
      simp only [mk_mul, conj_mk, ZOmega.conj_mul]

/-- **`conj` is an involution**. -/
@[simp] theorem conj_conj (x : ZOmegaSqrt2) : conj (conj x) = x := by
  induction x using Quotient.inductionOn with
  | _ a =>
    obtain ⟨z, k⟩ := a
    show conj (conj (mk z k)) = mk z k
    rw [conj_mk, conj_mk, ZOmega.conj_conj]

/-- **The squared modulus** `|z|² = z · conj z`. KMM tracks `sde(|z|²)`
of the matrix entries. -/
def normSq (z : ZOmegaSqrt2) : ZOmegaSqrt2 := z * conj z

@[simp] theorem normSq_zero : normSq 0 = 0 := by rw [normSq, conj_zero, mul_zero]

@[simp] theorem normSq_one : normSq 1 = 1 := by rw [normSq, conj_one, mul_one]

/-- **`normSq` is conjugation-symmetric** (real): `conj (normSq z) = normSq z`. -/
theorem conj_normSq (z : ZOmegaSqrt2) : conj (normSq z) = normSq z := by
  rw [normSq, conj_mul, conj_conj, mul_comm, ← normSq]

/-- **`normSq` is multiplicative**: `|x·y|² = |x|²·|y|²`. -/
theorem normSq_mul (x y : ZOmegaSqrt2) : normSq (x * y) = normSq x * normSq y := by
  rw [normSq, conj_mul, normSq, normSq]; ring

/-- **`normSq` is conjugation-invariant**: `|conj z|² = |z|²`. -/
theorem normSq_conj (z : ZOmegaSqrt2) : normSq (conj z) = normSq z := by
  rw [normSq, conj_conj, mul_comm, ← normSq]

/-- **`|ω|² = 1`** (`ω` is a unit of modulus one). -/
@[simp] theorem normSq_omega : normSq (of ZOmega.ω) = 1 := by
  rw [normSq, conj_of, ← of_mul]
  have h : ZOmega.ω * ZOmega.conj ZOmega.ω = 1 := by decide
  rw [h, of_one]

/-- **`|1/√2|² = 1/2`** (`= mk 1 2`). -/
theorem normSq_invSqrt2 : normSq invSqrt2 = mk 1 2 := by
  rw [normSq, invSqrt2_def, conj_mk, ZOmega.conj_one, mk_mul, mul_one]

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
