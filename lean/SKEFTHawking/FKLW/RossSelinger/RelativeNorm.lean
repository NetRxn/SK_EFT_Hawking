/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item H/I — §6 relative-norm equation (foundation)

The Ross-Selinger Diophantine / "§6" step of the grid-FINDER: given a target residual
`β ∈ ℤ[√2]` (here `β = √2^{2k} − u·u*`), find `t ∈ ℤ[ω]` with `t†t = β` (a **relative** norm
equation over the extension `ℤ[ω]/ℤ[√2]`). Grounded verbatim in Ross, *Algebraic and Logical
Methods in Quantum Computation* (PhD thesis, Dalhousie 2015, arXiv:1510.02198), §3.2.2
("Relative norm equations", pp. 25–26), read directly.

Per the thesis (Problem 3.2.4): writing `α = a + bω + cω² + dω³`, the equation `α†α = β` is the
integer system `a²+b²+c²+d² = a'`, `ab − ad + cb + cd = b'` (for `β = a' + b'√2`). The relative
norm `α†α` is exactly `ZOmega.normSq α = α · conj α`, so the project's computable
`ZOmega.diophantineSearch` (GridSolver.lean) is the sound bounded solver for Problem 3.2.4.

## This file — the *-homomorphism + the necessary conditions (clean, verified)

  * `star_omegaC : star ω_ℂ = −ω_ℂ³` — the complex conjugate of the embedded `ω` (`ω̄ = ω⁷`).
  * `toComplex_conj : toComplex (conj z) = star (toComplex z)` — `ZOmega.toComplex` is a
    `*`-homomorphism (`ℤ[ω] → ℂ` intertwines `ZOmega.conj` with complex conjugation).
  * `normSq_toComplex_re_nonneg` — **total positivity** (thesis p.26, necessary condition for
    Problem 3.2.4): the relative norm's complex image is a nonnegative real (`= |toComplex α|²`).
    The companion `β• ≥ 0` is the same statement under the `√2`-conjugate (`σ`).

## What remains (the genuine analytic gate, DR + Selinger-1212.6253-verified)

The thesis gives the *sufficient* condition (Prop 3.2.7: `n = β•β` prime, `n ≡ 1 (mod 8)` ⟹
solvable) and a *probabilistic* general algorithm (Prop 3.2.9, requires factoring — EXCLUDED by
the deterministic-branch guardrail). A **deterministic ∀-target** existence of a bounded-length
solvable residue is genuine analytic number theory (prime density / Dirichlet over the grid
region); Selinger arXiv:1212.6253 confirms the synthesis is randomized under a prime-distribution
hypothesis, with T-count `K + 4·log₂(1/ε)`, `K ≈ 10`. That existence is the remaining gate for
the concrete-`L ≤ 90` Item-G headline; the necessary conditions + the *-homomorphism here are its
verified foundation, and the existential headline is already unconditional (lightweight finder).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingSqrt2
import SKEFTHawking.FKLW.RossSelinger.NormSqGde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-- **Complex conjugate of the embedded `ω`**: `ω̄ = ω⁷ = −ω³`. (From `ω = (√2/2)(1+i)`,
`ω² = i`; `ω̄ = (√2/2)(1−i) = −ω³`.) -/
theorem star_omegaC : star ZOmega.omegaC = - ZOmega.omegaC ^ 3 := by
  rw [show ZOmega.omegaC ^ 3 = ZOmega.omegaC ^ 2 * ZOmega.omegaC from by ring,
      ZOmega.omegaC_sq, ZOmega.omegaC_eq, star_mul', Complex.star_def]
  simp only [map_add, map_one, Complex.conj_I, map_div₀, map_ofNat, Complex.conj_ofReal]
  ring_nf; rw [Complex.I_sq]; ring

/-- **`ZOmega.toComplex` is a `*`-homomorphism**: it intertwines the `ℤ[ω]` complex conjugation
`ZOmega.conj` with complex conjugation on `ℂ`. (Expand both via `toComplex_apply`; the embedded
`ω` powers reduce by `star ω = −ω³` and `ω⁴ = −1`.) -/
theorem toComplex_conj (z : ZOmega) :
    ZOmega.toComplex (ZOmega.conj z) = star (ZOmega.toComplex z) := by
  obtain ⟨a, b, c, d⟩ := z
  rw [show ZOmega.conj ⟨a, b, c, d⟩ = ⟨-c, -b, -a, d⟩ from rfl,
      ZOmega.toComplex_apply, ZOmega.toComplex_apply, Complex.star_def]
  simp only [map_add, map_mul, map_pow, map_intCast]
  rw [show (starRingEnd ℂ) ZOmega.omegaC = star ZOmega.omegaC from rfl, star_omegaC]
  have e9 : ZOmega.omegaC ^ 9 = ZOmega.omegaC := by
    rw [show (9 : ℕ) = 4 + 4 + 1 from rfl, pow_add, pow_add, ZOmega.omegaC_pow_four]; ring
  have e6 : ZOmega.omegaC ^ 6 = -ZOmega.omegaC ^ 2 := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, ZOmega.omegaC_pow_four]; ring
  push_cast; ring_nf; rw [e9, e6]; ring

/-- **§6 necessary condition — total positivity** (Ross thesis p.26): a relative norm
`β = α†α = normSq α` has nonnegative complex image, `(toComplex β).re = |toComplex α|² ≥ 0`. This
(and its `σ`-conjugate `β• ≥ 0`) is the necessary condition a candidate residual must satisfy for
the Diophantine equation `t†t = β` to be solvable — exactly the disk constraint the grid FINDER
imposes (`GridProblem.scaledColumn_exists`). -/
theorem normSq_toComplex_re_nonneg (α : ZOmega) :
    0 ≤ (ZOmega.toComplex (ZOmega.normSq α)).re := by
  have h : ZOmega.toComplex (ZOmega.normSq α)
      = ZOmega.toComplex α * star (ZOmega.toComplex α) := by
    rw [ZOmega.normSq, map_mul, toComplex_conj]
  rw [h, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (ZOmega.toComplex α).re, sq_nonneg (ZOmega.toComplex α).im]

/-- **Problem 3.2.4 Diophantine system** (Ross thesis §3.2.2, verbatim): the relative norm
`normSq ⟨a,b,c,d⟩ = α†α` has the explicit `ℤ[√2]` coordinates `⟨−b', 0, b', a'⟩` where
`a' = a²+b²+c²+d²` (the rational part, = sum of squares) and `b' = ab − ad + cb + cd` (the
`√2`-part). So solving `t†t = β` for `β = a' + b'√2` is exactly the integer system
`a²+b²+c²+d² = a'`, `ab − ad + cb + cd = b'` (thesis eqns). -/
theorem normSq_coords (a b c d : ℤ) :
    ZOmega.normSq ⟨a, b, c, d⟩
      = ⟨-(a*b - a*d + c*b + c*d), 0, a*b - a*d + c*b + c*d, a^2 + b^2 + c^2 + d^2⟩ := by
  ext <;>
    simp only [ZOmega.normSq, ZOmega.conj, ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c,
      ZOmega.mul_d] <;>
    ring

/-- The rational part of the relative norm is the **sum of squares** (thesis `a'`). -/
theorem normSq_d_eq_sumSq (a b c d : ℤ) :
    (ZOmega.normSq ⟨a, b, c, d⟩).d = a^2 + b^2 + c^2 + d^2 := by rw [normSq_coords]

/-- The `√2`-part of the relative norm is the thesis `b' = ab − ad + cb + cd`. -/
theorem normSq_sqrt2part (a b c d : ℤ) :
    (ZOmega.normSq ⟨a, b, c, d⟩).c = a*b - a*d + c*b + c*d := by rw [normSq_coords]

/-! ## Norm factorization (toward Prop 3.2.7) — the absolute norm factors through the relative

The Prop 3.2.7 sufficiency proof rests on the absolute field norm `N_{ℤ[ω]}` factoring through the
relative norm `α†α = normSq α` as `N_{ℤ[ω]}(α) = N_{ℤ[√2]}(normSq α) = β•β = n` — so a candidate
residual `β = normSq α` has absolute norm `n = β•β`, and `n` prime ≡1 mod 8 is the splitting
condition that makes `β` a relative norm. These two lemmas establish that factorization. -/

/-- **Absolute field norm formula** (Ross thesis Def 3.1.4): `N_{ℤ[ω]}(⟨a,b,c,d⟩) =
(a²+b²+c²+d²)² − 2·(ab − ad + cb + cd)²`. -/
theorem norm_eq (a b c d : ℤ) :
    ZOmega.norm ⟨a, b, c, d⟩
      = (a^2 + b^2 + c^2 + d^2)^2 - 2*(a*b - a*d + c*b + c*d)^2 := by
  simp only [ZOmega.norm, ZOmega.σ3, ZOmega.σ5, ZOmega.conj,
    ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c, ZOmega.mul_d]
  ring

/-- **The absolute norm factors through the relative norm**: `N_{ℤ[ω]}(α) = (normSq α).d² −
2·(normSq α).c²`, i.e. `= N_{ℤ[√2]}(α†α) = β•β`. (Combine `norm_eq` with `normSq_coords`.) For a
candidate residual `β = normSq α`, this is the integer `n = β•β` whose primality (≡1 mod 8)
governs whether `β` is itself a relative norm (Prop 3.2.7). -/
theorem norm_eq_relNorm (α : ZOmega) :
    ZOmega.norm α = (ZOmega.normSq α).d ^ 2 - 2 * (ZOmega.normSq α).c ^ 2 := by
  obtain ⟨a, b, c, d⟩ := α
  rw [norm_eq]
  simp only [ZOmega.normSq, ZOmega.conj, ZOmega.mul_c, ZOmega.mul_d]
  ring

end SKEFTHawking.RossSelinger
