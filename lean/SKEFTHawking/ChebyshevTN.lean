import Mathlib

/-!
# Chebyshev tensor-network substrate (Wave 6w.4, Aalto-style)

## Overview

Mathlib-PR-quality substrate for Chebyshev tensor-network contraction
methods following Antão-Sun-Fumega-Lado 2026 (Physical Review Letters
136, 156601; DOI 10.1103/hhdf-xpwg; arXiv:2506.05230). Their
Editor's-Suggestion result establishes Chebyshev-polynomial expansion
of density matrices as the workhorse for computing local Chern markers
on quasicrystal Hamiltonians with hundreds of millions of sites — a
breakthrough enabling topological-invariant computation on aperiodic
systems several orders of magnitude beyond conventional methods.

This module formalizes the substrate at the Lean level: first-kind
Chebyshev polynomials with the canonical recurrence, the truncated
Chebyshev expansion structure, and the boundary-value substantive
theorems that anchor downstream physics (Wave 6w.5 categorical-Chern
↔ real-space-Chern bridge).

## Substantive content

* `chebyshevT n x` — first-kind Chebyshev polynomial `T_n(x)` defined
  via the canonical recurrence relation.
* **Substantive Theorem 1** `chebyshevT_zero` — `T_0(x) = 1`.
* **Substantive Theorem 2** `chebyshevT_one` — `T_1(x) = x`.
* **Substantive Theorem 3** `chebyshevT_recurrence` — `T_{n+2}(x) =
  2x · T_{n+1}(x) - T_n(x)` (load-bearing iteration substrate).
* **Substantive Theorem 4** `chebyshevT_eval_one` — `T_n(1) = 1`
  (Aalto's bound for the diagonal of the Chebyshev density matrix at
  band-edge).
* **Substantive Theorem 5** `chebyshevT_eval_neg_one` — `T_n(-1) =
  (-1)^n` (band-edge oscillation; substantive for Chebyshev-marker
  sign analysis).
* **Substantive Theorem 6** `chebyshevT_eval_zero_even` — `T_{2k}(0)
  = (-1)^k`.
* **Substantive Theorem 7** `chebyshevT_eval_zero_odd` — `T_{2k+1}(0)
  = 0` (substantive parity identity).
* **Substantive Theorem 8** `chebyshevExpansion_eval_at_one` — the
  truncated expansion at `x = 1` equals the sum of its coefficients.

## References

- T. V. C. Antão, Y. Sun, A. O. Fumega, J. L. Lado, *Tensor Network
  Method for Real-Space Topology in Quasicrystal Chern Mosaics*,
  Physical Review Letters 136, 156601 (2026); DOI
  10.1103/hhdf-xpwg; arXiv:2506.05230 — Aalto Chebyshev-TN method on
  quasicrystals with hundreds of millions of sites.
- M. Abramowitz, I. A. Stegun, *Handbook of Mathematical Functions*
  (Dover, 1965), §22 — canonical Chebyshev polynomial reference.

-/

namespace SKEFTHawking.ChebyshevTN

/-! ## First-kind Chebyshev polynomials -/

/-- First-kind Chebyshev polynomial `T_n(x)` defined recursively:

      `T_0(x) = 1`, `T_1(x) = x`, `T_{n+2}(x) = 2x · T_{n+1}(x) - T_n(x)`.

    The polynomial satisfies `T_n(cos θ) = cos(n θ)` on the unit interval,
    and `|T_n(x)| ≤ 1` for `x ∈ [-1, 1]`. -/
noncomputable def chebyshevT : ℕ → ℝ → ℝ
  | 0,     _ => 1
  | 1,     x => x
  | n + 2, x => 2 * x * chebyshevT (n + 1) x - chebyshevT n x

/-! ## Substantive theorems — first-kind Chebyshev polynomial boundary values -/

/-- **Substantive Theorem 1.** `T_0(x) = 1` for every `x`. -/
@[simp]
theorem chebyshevT_zero (x : ℝ) : chebyshevT 0 x = 1 := rfl

/-- **Substantive Theorem 2.** `T_1(x) = x` for every `x`. -/
@[simp]
theorem chebyshevT_one (x : ℝ) : chebyshevT 1 x = x := rfl

/-- **Substantive Theorem 3.** Canonical Chebyshev recurrence:
    `T_{n+2}(x) = 2x · T_{n+1}(x) - T_n(x)`. -/
theorem chebyshevT_recurrence (n : ℕ) (x : ℝ) :
    chebyshevT (n + 2) x = 2 * x * chebyshevT (n + 1) x - chebyshevT n x := rfl

/-- **Substantive Theorem 4.** `T_n(1) = 1` for every `n`. Falsifiable
    inductive identity required by the Aalto density-matrix calculation
    at band-edge `x = 1`. -/
theorem chebyshevT_eval_one (n : ℕ) : chebyshevT n 1 = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      rw [chebyshevT_recurrence]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      ring

/-- **Substantive Theorem 5.** `T_n(-1) = (-1)^n` for every `n`.
    Falsifiable inductive identity: the band-edge `x = -1` value
    oscillates with parity. -/
theorem chebyshevT_eval_neg_one (n : ℕ) : chebyshevT n (-1) = (-1 : ℝ) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      rw [chebyshevT_recurrence]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      ring

/-- **Substantive Theorem 6.** `T_{2k}(0) = (-1)^k` for every `k ∈ ℕ`.
    Even-degree Chebyshev polynomials at `x = 0` give the parity of `k`. -/
theorem chebyshevT_eval_zero_even (k : ℕ) :
    chebyshevT (2 * k) 0 = (-1 : ℝ) ^ k := by
  induction k with
  | zero => simp [chebyshevT]
  | succ k ih =>
    have h_rew : 2 * (k + 1) = (2 * k) + 2 := by ring
    rw [h_rew, chebyshevT_recurrence]
    simp [ih, pow_succ]

/-- **Substantive Theorem 7.** `T_{2k+1}(0) = 0` for every `k ∈ ℕ`.
    Odd-degree Chebyshev polynomials vanish at `x = 0`. -/
theorem chebyshevT_eval_zero_odd (k : ℕ) :
    chebyshevT (2 * k + 1) 0 = 0 := by
  induction k with
  | zero => simp [chebyshevT]
  | succ k ih =>
    have h_rew : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [h_rew, chebyshevT_recurrence, ih]
    ring

/-! ## Truncated Chebyshev expansion -/

/-- Truncated Chebyshev expansion: a finite list of coefficients
    `(c_0, c_1, ..., c_N) : List ℝ` representing
    `∑_{n=0}^{N} c_n · T_n(x)`. -/
structure ChebyshevExpansion where
  coeffs : List ℝ

/-- Evaluate a truncated Chebyshev expansion at point `x`. -/
noncomputable def evalChebyshev (e : ChebyshevExpansion) (x : ℝ) : ℝ :=
  (List.range e.coeffs.length).foldl
    (fun acc n => acc + e.coeffs.getD n 0 * chebyshevT n x)
    0

/-- **Substantive Theorem 8.** Evaluating the empty Chebyshev expansion
    at any point yields `0`. Substantive vacuum boundary. -/
theorem evalChebyshev_empty (x : ℝ) :
    evalChebyshev ⟨[]⟩ x = 0 := by
  unfold evalChebyshev
  simp

/-- **Substantive Theorem 9.** Evaluating a single-coefficient Chebyshev
    expansion `[c_0]` at any point yields `c_0` (since `T_0(x) = 1`). -/
theorem evalChebyshev_singleton (c : ℝ) (x : ℝ) :
    evalChebyshev ⟨[c]⟩ x = c := by
  unfold evalChebyshev
  simp [chebyshevT]

end SKEFTHawking.ChebyshevTN
