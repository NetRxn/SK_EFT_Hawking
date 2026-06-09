/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 — KMM ancilla mechanism: unconditional norm-equation solvability

The Phase-6AM Wave 5 efficiency headline (`LogLengthHeadline.lean`) ships the **O(log 1/ε)
exponent-1** Clifford+T word length, but its `∀U`-unconditionality is gated on the **ancilla-free**
relative-norm existence `t†t = √2^{2k} − u·u*` (`rossSelinger_synth_of_residual`'s hypothesis `he`).
That gate is a genuine analytic-NT statement (prime-density of solvable residuals; strictly weaker
than Ross–Selinger Hypothesis 29 but still Lean-impractical — Friedlander–Iwaniec / half-dimensional
sieve, absent from Mathlib).

This file builds the **Kliuchnikov–Maslov–Mosca ancilla mechanism** (arXiv:1212.0822, PRL 110:190502 —
"approximates single qubit unitaries with precision ε using O(log 1/ε) Clifford and T gates and
employing up to two ancillary qubits"), which makes the norm equation **unconditionally solvable**:
adding ancilla qubits adds completion columns, turning the *single* relative-norm condition (a SUM OF
TWO squares over ℤ[√2], conditional — Fermat-style, needs inert primes to even powers) into a SUM OF
*FOUR* squares condition (**always solvable by Lagrange**, `Nat.sum_four_squares`, present in Mathlib).

## Headlines

  * `conj_natCast` / `conj_intCast` — rational integers are `conj`-fixed (real elements of `ℤ[ω]`).
  * `exists_two_relativeNorms_of_nat` — **the keystone.** Every `r : ℕ` is a sum of two `ℤ[ω]`
    relative norms: `∃ t₁ t₂, normSq t₁ + normSq t₂ = r`. Proof: `Nat.sum_four_squares` gives
    `r = a²+b²+c²+d²`; set `t₁ = a + b·ω²`, `t₂ = c + d·ω²` (`ω² = i`, and `a,b,c,d ∈ ℤ` are real),
    whence `normSq tᵢ = (·)² + (·)²` by `normSq_real_sumSq`. **Unconditional** — no prime-density,
    no Hypothesis 29.
  * `ancilla_completion_of_nat_residual` — the **unconditional unit-column completion**: for an
    approximant `u` whose squared modulus is the rational integer `m ≤ 2^k` (the √2-balanced
    approximant the KMM rounding targets), the two ancilla completion entries `t₁, t₂ ∈ ℤ[ω]` exist
    with `normSq u + normSq t₁ + normSq t₂ = 2^k`. The (1+ancilla)-qubit first column closes
    **with NO relative-norm hypothesis**, in direct contrast to the ancilla-free
    `rossSelinger_synth_of_residual`, which REQUIRES the residual be a single relative norm.

The remaining strands toward the full `∀U∈SU(2)` O(log 1/ε)-with-≤2-ancillas circuit headline
(ancilla-extended unitary semantics + the rounding step that produces an integer residual) are
sequenced into later increments of this track; the number-theoretic heart — the unconditional
solvability that genuinely removes the wall — is established here.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.

## References

  * Kliuchnikov–Maslov–Mosca, *Asymptotically optimal approximation of single qubit unitaries by
    Clifford and T circuits using a constant number of ancillary qubits*, PRL 110:190502 (2013),
    arXiv:1212.0822.
  * `Mathlib.NumberTheory.SumFourSquares` (`Nat.sum_four_squares`).
  * `RelativeNorm.lean` (`normSq_real_sumSq`, the index-2-safe two-squares reduction).
-/

import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
import Mathlib.NumberTheory.SumFourSquares

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-- **Rational integers are `conj`-fixed** (they are real elements of `ℤ[ω]`): `conj (n:ℤ) = n`.
(`(n : ZOmega) = ⟨0,0,0,n⟩`, and `conj ⟨a,b,c,d⟩ = ⟨-c,-b,-a,d⟩` fixes it.) -/
@[simp] theorem conj_intCast (n : ℤ) : ZOmega.conj (n : ZOmega) = (n : ZOmega) := by
  show ZOmega.conj (ZOmega.ofInt n) = ZOmega.ofInt n
  ext <;> simp [ZOmega.ofInt]

/-- **Natural-number casts are `conj`-fixed.** -/
@[simp] theorem conj_natCast (n : ℕ) : ZOmega.conj (n : ZOmega) = (n : ZOmega) := by
  rw [← Int.cast_natCast, conj_intCast]

/-- **The KMM ancilla keystone — every natural number is a sum of two `ℤ[ω]` relative norms.**

For any `r : ℕ` there exist `t₁ t₂ ∈ ℤ[ω]` with `normSq t₁ + normSq t₂ = r`. This is the exact
number-theoretic content of the KMM ancilla trick (arXiv:1212.0822): the ancilla adds completion
columns, so the residual need only be a sum of *two* relative norms — equivalently a sum of *four*
integer squares — which Lagrange's four-square theorem (`Nat.sum_four_squares`) supplies for **every**
`r`, with NO prime-density / Hypothesis-29 condition. Witness: `r = a²+b²+c²+d²`, take
`t₁ = a + b·ω²`, `t₂ = c + d·ω²` (`ω² = i`); the rational integers `a,b,c,d` are `conj`-fixed, so
`normSq_real_sumSq` gives `normSq t₁ = a²+b²` and `normSq t₂ = c²+d²`. -/
theorem exists_two_relativeNorms_of_nat (r : ℕ) :
    ∃ t₁ t₂ : ZOmega, ZOmega.normSq t₁ + ZOmega.normSq t₂ = (r : ZOmega) := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares r
  refine ⟨(a : ZOmega) + (b : ZOmega) * ZOmega.ω ^ 2,
          (c : ZOmega) + (d : ZOmega) * ZOmega.ω ^ 2, ?_⟩
  rw [normSq_real_sumSq (conj_natCast a) (conj_natCast b),
      normSq_real_sumSq (conj_natCast c) (conj_natCast d)]
  have hr : (r : ZOmega)
      = (a : ZOmega) ^ 2 + (b : ZOmega) ^ 2 + ((c : ZOmega) ^ 2 + (d : ZOmega) ^ 2) := by
    rw [← habcd]; push_cast; ring
  rw [hr]

/-- **Unconditional unit-column completion via the ancilla (KMM, arXiv:1212.0822).**

For an approximant `u : ℤ[ω]` whose squared modulus is the rational integer `m ≤ 2^k` (the
√2-balanced approximant the KMM rounding targets), the two ancilla "completion" entries
`t₁, t₂ ∈ ℤ[ω]` exist with `normSq u + normSq t₁ + normSq t₂ = 2^k`. So the (1+ancilla)-qubit first
column closes **UNCONDITIONALLY** — NO relative-norm / prime-density hypothesis — because the residual
`r = 2^k − m ∈ ℕ` is a sum of two relative norms (`exists_two_relativeNorms_of_nat`). Contrast the
ancilla-free `rossSelinger_synth_of_residual`, whose hypothesis `he` REQUIRES the residual be a
*single* relative norm (conditional: a sum of two squares over ℤ[√2], gated by the inert-prime
even-power criterion). -/
theorem ancilla_completion_of_nat_residual {u : ZOmega} {k m : ℕ}
    (hm : ZOmega.normSq u = (m : ZOmega)) (hmk : m ≤ 2 ^ k) :
    ∃ t₁ t₂ : ZOmega,
      ZOmega.normSq u + ZOmega.normSq t₁ + ZOmega.normSq t₂ = ((2 ^ k : ℕ) : ZOmega) := by
  obtain ⟨t₁, t₂, ht⟩ := exists_two_relativeNorms_of_nat (2 ^ k - m)
  refine ⟨t₁, t₂, ?_⟩
  rw [hm, add_assoc, ht, ← Nat.cast_add]
  congr 1
  omega

end SKEFTHawking.RossSelinger
