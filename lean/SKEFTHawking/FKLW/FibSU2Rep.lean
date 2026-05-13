/-
SK_EFT_Hawking Phase 6p Wave 2c.4a-R4.2.a: Concrete Fibonacci 3-strand SU(2)
representation substrate (complex-matrix layer).

This module ships the **complex-matrix Fibonacci substrate** toward the
constructive discharge of the substantive `closure(range ρ_Fib) = univ`
hypothesis from the R2 soundness audit refactor (commit `f44c60d`,
2026-05-13). Downstream of this module:

  - R4.2.b: Yang-Baxter `σ_Fib_1 * σ_Fib_2 * σ_Fib_1 = σ_Fib_2 * σ_Fib_1 * σ_Fib_2`
    proven over ℂ (either by direct algebraic manipulation in ℂ, or by
    a ring-hom transport from the QCyc40Ext-side native_decide proof in
    `RouabahExplicit.lean`).
  - R4.2.c: `ρ_Fib_SU2 : BraidGroup 3 →* SU(2)` MonoidHom construction
    via `braidGroup3HomFromPair` (R4.1).
  - R4.2.d: `closure(Set.range ρ_Fib_SU2) = Set.univ` discharge.
    Two paths:
      (i) Constructive: Weyl-equidistribution + Euler-axes covering of
          SU(2). Requires substantial substrate ship (matrix-log
          Lipschitz / dense-axes-rotation infra absent from Mathlib4).
      (ii) Scoped HBS axiom (with user sign-off, citing Hormozi-
           Bonesteel-Simon 2007 / Bonesteel et al. 2005 / FLW 2002).
  - R4.2.e: composition with `bridge_FKLW_unitary` →
    `fibonacci_3strand_example_substantive` becomes unconditional.

## R4.2.a scope (this module, 2026-05-13)

  **Provides**: concrete `R1_C, Rtau_C, φ_C, F_C ∈ ℂ` /
  `Matrix (Fin 2) (Fin 2) ℂ` with the algebraic identities for the
  R-eigenvalues + golden-ratio + F-matrix involution. Substrate level
  only — no σ₂, no MonoidHom, no Yang-Baxter, no density.

  **Does NOT provide**: σ_Fib_2 (defined in R4.2.b); ρ_Fib_SU2 (needs YB);
  the SU(2)-element-lifted versions (needs det normalization, deferred to
  R4.2.b); any density statement.

## Why this layering

The original R4.2 sub-wave plan (memory file 2026-05-13) called for
shipping the full chain (concrete MonoidHom + density). The honest
substrate audit performed before this commit reveals:

  - Yang-Baxter over ℂ for the Fibonacci F-matrix data requires either
    a substantial direct-algebraic proof (~200-500 LoC) or a ring-hom
    transport from `QCyc40Ext → ℂ` (which itself requires ~200-400 LoC
    of cyclotomic-field-to-ℂ embedding infrastructure absent from
    Mathlib4 at the project-local level).
  - The density discharge requires Mathlib infrastructure (matrix log
    Lipschitz, dense-axes-rotation density argument for SU(2), or the
    classical "two non-commuting infinite-order rotations generate
    dense" theorem) that does not currently exist project-locally or in
    Mathlib4.

A staged ship (R4.2.a substrate → R4.2.b YB+σ₂ → R4.2.c MonoidHom →
R4.2.d density) decouples these obligations and produces a clean
checkpoint at each level.

## Pipeline Invariant compliance

  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new project-local axioms): RESPECTED (zero new axioms).
  - Strengthening discipline:
    * P3 (trivial discharge): every theorem has substantive algebraic
      content (R-eigenvalue unit-modulus, golden ratio identity, F²=I
      via φ-relation).
    * P5 (existential unfolding): no existential bundling; each lemma
      captures one algebraic content unit.

## Primary references

  - Hormozi, Bonesteel, Simon, *Phys. Rev. Lett.* 99, 200502 (2007);
    arXiv:0706.0478 (HBS 2007 — Fibonacci universality).
  - Bonesteel, Hormozi, Zikos, Simon, *Phys. Rev. Lett.* 95, 140503
    (2005) (qubit gates from Fibonacci braiding).
  - Freedman, Larsen, Wang, *Comm. Math. Phys.* 227/228, 605/177
    (2002); arXiv:math/0103200 (FLW 2002 — Theorem 0.1).
  - Reichardt, arXiv:quant-ph/0506220 (2005) (independent constructive
    universality).

Zero sorry. Zero new project-local axioms in this module.
-/

import Mathlib
import SKEFTHawking.FKLW.AharonovAradBridge
import SKEFTHawking.FKLW.AharonovAradBridgeIteration
import SKEFTHawking.FKLW.FibRepInfiniteOrder

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open Complex Real
open scoped Matrix

/-! ## 1. R-eigenvalues over ℂ

The Fibonacci R-matrix eigenvalues from Q(ζ₅) lifted to ℂ via
`ζ₅ ↦ Complex.exp (2π · I / 5)`:

  - R₁ = ζ₅³ = exp(-4πi/5) (vacuum channel; order 5)
  - R_τ = -ζ₅⁴ = exp(3πi/5) (τ channel; order 10)
  -/

/-- R₁ = exp(-4πi/5), the Fibonacci R-matrix vacuum-channel eigenvalue
in ℂ. -/
noncomputable def R1_C : ℂ := Complex.exp (((-4 * Real.pi / 5 : ℝ) : ℂ) * Complex.I)

/-- R_τ = exp(3πi/5), the Fibonacci R-matrix τ-channel eigenvalue in ℂ. -/
noncomputable def Rtau_C : ℂ := Complex.exp (((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I)

/-- R₁ has unit modulus (it's `exp` of a pure imaginary number). -/
theorem norm_R1_C : ‖R1_C‖ = 1 := by
  unfold R1_C
  rw [Complex.norm_exp]
  simp

/-- R_τ has unit modulus. -/
theorem norm_Rtau_C : ‖Rtau_C‖ = 1 := by
  unfold Rtau_C
  rw [Complex.norm_exp]
  simp

/-! ## 2. Golden ratio over ℂ

The Fibonacci F-matrix entries involve `φ = (1+√5)/2` and `1/√φ`.
Mathlib provides `Real.goldenRatio` with the key identity `φ² = φ + 1`. -/

/-- Golden ratio as a complex number. -/
noncomputable def φ_C : ℂ := (Real.goldenRatio : ℂ)

/-- 1/φ as a complex number. -/
noncomputable def φInv_C : ℂ := ((Real.goldenRatio⁻¹ : ℝ) : ℂ)

/-- 1/√φ as a complex number. The positive square root branch. -/
noncomputable def φInvSqrt_C : ℂ := (((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) : ℂ)

/-- φ ≠ 0 in ℂ. -/
theorem φ_C_ne_zero : φ_C ≠ 0 := by
  unfold φ_C
  exact_mod_cast Real.goldenRatio_ne_zero

/-- φ² = φ + 1 in ℂ (lifted from `Real.goldenRatio_sq`). -/
theorem φ_C_sq : φ_C ^ 2 = φ_C + 1 := by
  unfold φ_C
  have h : (Real.goldenRatio : ℝ) ^ 2 = (Real.goldenRatio : ℝ) + 1 := Real.goldenRatio_sq
  exact_mod_cast h

/-- φ · φ⁻¹ = 1 in ℂ. -/
theorem φ_C_mul_inv : φ_C * φInv_C = 1 := by
  unfold φ_C φInv_C
  have h : Real.goldenRatio * Real.goldenRatio⁻¹ = 1 :=
    mul_inv_cancel₀ Real.goldenRatio_ne_zero
  exact_mod_cast h

/-- (1/√φ)² = 1/φ in ℂ. Uses `Real.sq_sqrt` on the positive `φ`. -/
theorem φInvSqrt_C_sq : φInvSqrt_C ^ 2 = φInv_C := by
  unfold φInvSqrt_C φInv_C
  have hpos : 0 ≤ Real.goldenRatio := le_of_lt Real.goldenRatio_pos
  have hne : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  have hsne : Real.sqrt Real.goldenRatio ≠ 0 := by
    rw [Real.sqrt_ne_zero hpos]
    exact hne
  -- Real-level identity: (√φ)⁻¹^2 = φ⁻¹
  have h : ((Real.sqrt Real.goldenRatio)⁻¹ : ℝ) ^ 2 = (Real.goldenRatio⁻¹ : ℝ) := by
    rw [inv_pow, Real.sq_sqrt hpos]
  exact_mod_cast h

/-! ## 3. The F-matrix in `Matrix (Fin 2) (Fin 2) ℂ`

  F = [[1/φ, 1/√φ], [1/√φ, -1/φ]]

This is the Bonesteel-Hormozi-Simon F-matrix (the Fibonacci F-symbol
in the qubit recoupling channel). Its key property is `F² = I`, which
follows from `(1/φ)² + (1/√φ)² = 1/φ² + 1/φ = 1` — a consequence of
the golden ratio identity `φ² = φ + 1`. -/

/-- The Fibonacci F-matrix. -/
noncomputable def F_C : Matrix (Fin 2) (Fin 2) ℂ :=
  !![φInv_C, φInvSqrt_C; φInvSqrt_C, -φInv_C]

/-- Key F² = I diagonal identity: `1/φ² + 1/φ = 1`. -/
private theorem F_C_diag_identity : φInv_C * φInv_C + φInvSqrt_C * φInvSqrt_C = 1 := by
  -- From φInvSqrt_C^2 = φInv_C: φInvSqrt_C * φInvSqrt_C = φInv_C.
  have hsq : φInvSqrt_C * φInvSqrt_C = φInv_C := by
    have := φInvSqrt_C_sq; rw [sq] at this; exact this
  rw [hsq]
  -- Now: φInv_C * φInv_C + φInv_C = 1.
  -- Multiply by φ²: φ² * φInv² + φ² * φInv = 1 + φ = φ². So φInv² + φInv = 1.
  have h1 : φ_C * φInv_C = 1 := φ_C_mul_inv
  have h2 : φ_C ^ 2 = φ_C + 1 := φ_C_sq
  have hne : φ_C ≠ 0 := φ_C_ne_zero
  have hsq_ne : φ_C ^ 2 ≠ 0 := pow_ne_zero _ hne
  -- Compute φ² * (φInv² + φInv) = φ²
  have key : φ_C ^ 2 * (φInv_C * φInv_C + φInv_C) = φ_C ^ 2 * 1 := by
    calc φ_C ^ 2 * (φInv_C * φInv_C + φInv_C)
        = (φ_C * φInv_C) * (φ_C * φInv_C) + φ_C * (φ_C * φInv_C) := by ring
      _ = 1 * 1 + φ_C * 1 := by rw [h1]
      _ = φ_C + 1 := by ring
      _ = φ_C ^ 2 := h2.symm
      _ = φ_C ^ 2 * 1 := by ring
  exact mul_left_cancel₀ hsq_ne key

/-- F² = I (the load-bearing involution property). -/
theorem F_C_sq : F_C * F_C = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F_C, Matrix.mul_apply, Fin.sum_univ_two]
  -- (0,0): φInv_C * φInv_C + φInvSqrt_C * φInvSqrt_C = 1
  · exact F_C_diag_identity
  -- (0,1): φInv_C * φInvSqrt_C + φInvSqrt_C * (-φInv_C) = 0
  · ring
  -- (1,0): φInvSqrt_C * φInv_C + (-φInv_C) * φInvSqrt_C = 0
  · ring
  -- (1,1): φInvSqrt_C * φInvSqrt_C + φInv_C * φInv_C = 1
  --        (matrix simp normalizes -φInv_C · -φInv_C to φInv_C · φInv_C)
  · -- Use the diagonal identity in the order (φInvSqrt²) + (φInv²) = (φInv) + (φInv²) = 1
    have hsq : φInvSqrt_C * φInvSqrt_C = φInv_C := by
      have := φInvSqrt_C_sq; rw [sq] at this; exact this
    rw [hsq]
    -- Goal: φInv_C + φInv_C * φInv_C = 1
    have key := F_C_diag_identity
    rw [hsq] at key
    -- key : φInv_C * φInv_C + φInv_C = 1
    linear_combination key

/-! ## 4. σ_1 and σ_2 matrices over ℂ

  σ_1 = diag(R_1, R_τ) — the diagonal braid generator (braids anyons 1, 2)
  σ_2 = F · σ_1 · F  — the conjugate (braids anyons 2, 3)

Note (non-trivial det): det(σ_1) = R_1 · R_τ = exp(-πi/5) ≠ 1, so σ_1 is
in U(2) but NOT yet in SU(2). The det-normalization to SU(2) requires
multiplication by ω = exp(πi/10) (a 20th root of unity); this is deferred
to R4.2.c with the MonoidHom construction. -/

/-- The diagonal braid generator σ_1 = diag(R_1, R_τ). -/
noncomputable def σ_Fib_1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![R1_C, 0; 0, Rtau_C]

/-- The conjugate braid generator σ_2 = F · σ_1 · F. -/
noncomputable def σ_Fib_2 : Matrix (Fin 2) (Fin 2) ℂ :=
  F_C * σ_Fib_1 * F_C

/-- A complex number with unit modulus times its conjugate is 1. -/
private theorem unit_norm_mul_conj {z : ℂ} (hz : ‖z‖ = 1) :
    z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj]
  -- Goal: (Complex.normSq z : ℂ) = 1
  have hnorm_sq : Complex.normSq z = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm]
  rw [hnorm_sq, hz]
  norm_num

/-- σ_1 is unitary: σ_1 · σ_1⋆ = 1. -/
theorem σ_Fib_1_unitary :
    σ_Fib_1 * star σ_Fib_1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ_Fib_1, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.star_eq_conjTranspose]
  -- (0,0): R1_C * conj R1_C = 1
  · exact unit_norm_mul_conj norm_R1_C
  -- (1,1): Rtau_C * conj Rtau_C = 1
  · exact unit_norm_mul_conj norm_Rtau_C

/-- det(σ_1) = R_1 · R_τ. -/
theorem σ_Fib_1_det :
    σ_Fib_1.det = R1_C * Rtau_C := by
  simp [σ_Fib_1, Matrix.det_fin_two_of]

/-- φInv_C is real-cast (its conjugate equals itself). -/
private theorem star_φInv_C : (starRingEnd ℂ) φInv_C = φInv_C := by
  unfold φInv_C; exact Complex.conj_ofReal _

/-- φInvSqrt_C is real-cast. -/
private theorem star_φInvSqrt_C : (starRingEnd ℂ) φInvSqrt_C = φInvSqrt_C := by
  unfold φInvSqrt_C; exact Complex.conj_ofReal _

/-- F is Hermitian (`star F = F`): all entries are real and F is symmetric. -/
theorem F_C_star : star F_C = F_C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F_C, star_φInv_C, star_φInvSqrt_C]

/-- F is unitary: `F * star F = 1` (follows from F Hermitian + F² = I). -/
theorem F_C_unitary : F_C * star F_C = 1 := by
  rw [F_C_star]; exact F_C_sq

/-- σ_2 is unitary: σ_2 * star σ_2 = 1.
Uses F Hermitian + F² = I + σ_1 unitary:
  σ_2 (star σ_2) = (F σ_1 F)(F star σ_1 F) = F σ_1 (F²) (star σ_1) F
                 = F σ_1 (star σ_1) F = F · 1 · F = F² = 1. -/
theorem σ_Fib_2_unitary :
    σ_Fib_2 * star σ_Fib_2 = 1 := by
  unfold σ_Fib_2
  have hFstar : star F_C = F_C := F_C_star
  have hF2 : F_C * F_C = 1 := F_C_sq
  have hσ1u : σ_Fib_1 * star σ_Fib_1 = 1 := σ_Fib_1_unitary
  -- (F σ_1 F)(star (F σ_1 F)) = F σ_1 F · (star F) · (star σ_1) · (star F)
  --                            = F σ_1 F · F · (star σ_1) · F   (F star = F)
  --                            = F σ_1 (FF) (star σ_1) F
  --                            = F σ_1 · 1 · (star σ_1) F        (F²=I)
  --                            = F (σ_1 star σ_1) F = F · 1 · F = F² = 1.
  calc F_C * σ_Fib_1 * F_C * star (F_C * σ_Fib_1 * F_C)
      = F_C * σ_Fib_1 * F_C * (star F_C * star σ_Fib_1 * star F_C) := by
        rw [show star (F_C * σ_Fib_1 * F_C) =
              star F_C * star σ_Fib_1 * star F_C by
          rw [star_mul, star_mul, ← mul_assoc]]
    _ = F_C * σ_Fib_1 * F_C * (F_C * star σ_Fib_1 * F_C) := by rw [hFstar]
    _ = F_C * σ_Fib_1 * (F_C * F_C) * (star σ_Fib_1 * F_C) := by
        noncomm_ring
    _ = F_C * σ_Fib_1 * 1 * (star σ_Fib_1 * F_C) := by rw [hF2]
    _ = F_C * (σ_Fib_1 * star σ_Fib_1) * F_C := by noncomm_ring
    _ = F_C * 1 * F_C := by rw [hσ1u]
    _ = F_C * F_C := by noncomm_ring
    _ = 1 := hF2

/-- σ_2 has the same determinant as σ_1, because det(F) = ±1 and
det(F · σ_1 · F) = det(F)² · det(σ_1) = det(σ_1). -/
theorem σ_Fib_2_det_eq_σ_Fib_1_det :
    σ_Fib_2.det = σ_Fib_1.det := by
  unfold σ_Fib_2
  rw [Matrix.det_mul, Matrix.det_mul]
  -- det(F) * det(σ_1) * det(F) = det(F)² · det(σ_1)
  -- F² = I ⇒ det(F)² = det(I) = 1
  have hF2 : F_C.det * F_C.det = 1 := by
    have : F_C.det * F_C.det = (F_C * F_C).det := (Matrix.det_mul F_C F_C).symm
    rw [this, F_C_sq]
    exact Matrix.det_one
  -- Goal after rewrites: F_C.det * σ_Fib_1.det * F_C.det = σ_Fib_1.det
  -- Rearrange to σ_Fib_1.det * (F_C.det * F_C.det) and use hF2.
  have key : F_C.det * σ_Fib_1.det * F_C.det = σ_Fib_1.det * (F_C.det * F_C.det) := by ring
  rw [key, hF2, mul_one]

/-! ## 5. The cyclotomic-Fibonacci bridge identity

The single non-trivial transcendental ingredient for proving Yang-Baxter
over ℂ: `R1_C² + R1_C³ = 1/φ`. This is the ℂ-level statement of the
classical algebraic identity `ζ + ζ⁴ = 1/φ` (where ζ = exp(2πi/5)),
which connects the cyclotomic field Q(ζ_5) to the quadratic-irrational
field Q(√5).

Decomposing R1_C^2 = exp(-8πi/5) = exp(2πi/5) (mod 2πi periodicity)
and R1_C^3 = exp(-12πi/5) = exp(-2πi/5), we get
`R1_C² + R1_C³ = 2·cos(2π/5)`. Then `2·cos(2π/5) = (√5-1)/2 = 1/φ`
via Mathlib's `Real.cos_pi_div_five = (1+√5)/4` + double-angle formula.

This identity is the **only** Fibonacci-specific transcendental content
in the YB proof; the remaining algebra is purely formal manipulation of
`φ² = φ + 1`, `R1_C^5 = 1`, and `Rtau_C^5 = -1` (or related).
-/

/-- `R1_C^5 = 1`: R₁ is a primitive 5th root of unity.

Computed via `exp(5 · (-4π/5)·I) = exp(-4π·I) = (exp(2π·I))^{-2} = 1`. -/
theorem R1_C_pow_5 : R1_C ^ 5 = 1 := by
  unfold R1_C
  rw [← Complex.exp_nat_mul]
  -- 5 * ((-4π/5 : ℝ) : ℂ) · I = -4π · I  (need to push to canonical form)
  have heq : ((5 : ℕ) : ℂ) * (((-4 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) =
              ((-2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [heq]
  exact Complex.exp_int_mul_two_pi_mul_I (-2)

/-- `Rtau_C^5 = -1`: R_τ is a primitive 10th root of unity.

Computed via `exp(5 · 3π/5 · I) = exp(3π·I) = exp(π·I) · exp(2π·I) = -1 · 1`. -/
theorem Rtau_C_pow_5 : Rtau_C ^ 5 = -1 := by
  unfold Rtau_C
  rw [← Complex.exp_nat_mul]
  -- 5 * (3π/5 · I) = 3π·I = π·I + 2π·I
  have heq : ((5 : ℕ) : ℂ) * (((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) =
              (Real.pi : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I 1, mul_one,
      Complex.exp_pi_mul_I]

/-- `R1_C^10 = 1`. -/
private theorem R1_C_pow_10 : R1_C ^ 10 = 1 := by
  rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, R1_C_pow_5]; norm_num

/-- `Rtau_C^10 = 1`: R_τ is a 10th root of unity. -/
theorem Rtau_C_pow_10 : Rtau_C ^ 10 = 1 := by
  rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, Rtau_C_pow_5]; norm_num

/-- Helper: `2·cos(2π/5) = (√5 - 1)/2`. Derived from `Real.cos_pi_div_five`
via the double-angle formula. -/
private theorem two_cos_two_pi_div_five :
    2 * Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 2 := by
  have h : Real.cos (2 * Real.pi / 5) = 2 * Real.cos (Real.pi / 5) ^ 2 - 1 := by
    rw [show (2 * Real.pi / 5 : ℝ) = 2 * (Real.pi / 5) by ring]
    exact Real.cos_two_mul _
  rw [h, Real.cos_pi_div_five]
  have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  -- Goal: 2 * (2 * ((1 + √5)/4)^2 - 1) = (√5 - 1)/2
  -- Expand: 2*(2*(1+2√5+5)/16 - 1) = (1+2√5+5)/4 - 2 = (6+2√5)/4 - 8/4 = (2√5 - 2)/4 = (√5-1)/2 ✓
  nlinarith [hsq, sq_nonneg (Real.sqrt 5 - 1), sq_nonneg (Real.sqrt 5 + 1)]

/-- Helper: `(√5 - 1)/2 = goldenRatio⁻¹` (real-side). -/
private theorem goldenRatio_inv_eq :
    (Real.goldenRatio⁻¹ : ℝ) = (Real.sqrt 5 - 1) / 2 := by
  -- goldenRatio = (1 + √5)/2, so 1/goldenRatio = 2/(1+√5) = (√5-1)/2 after rationalization
  unfold Real.goldenRatio
  rw [show ((1 + Real.sqrt 5) / 2 : ℝ)⁻¹ = 2 / (1 + Real.sqrt 5) by
    rw [inv_div]]
  -- 2/(1+√5) = (√5-1)/2 via (1+√5)(√5-1) = 5 - 1 = 4
  have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hne : (1 + Real.sqrt 5 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 1 + Real.sqrt 5 :=
      add_pos zero_lt_one (Real.sqrt_pos.mpr (by norm_num))
    exact ne_of_gt this
  field_simp
  linear_combination -hsq

/-- Helper: `exp(z·I) + exp(-z·I) = 2·cos(z)` for `z : ℂ`. -/
private theorem exp_z_I_add_exp_neg_z_I (z : ℂ) :
    Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I) =
    2 * Complex.cos z := by
  -- Use Mathlib's `Complex.cos = (exp(z·I) + exp(-z·I))/2`
  rw [Complex.cos]
  ring

/-- **The cyclotomic-Fibonacci bridge identity.**

`R1_C² + R1_C³ = 1/φ` in ℂ. This is the load-bearing transcendental
content of the Yang-Baxter relation: it links the cyclotomic field
Q(ζ_5) to the golden-ratio field Q(√5) via Re(exp(2πi/5)) = (√5-1)/4.

Proof: `R1_C² + R1_C³ = exp(-8πi/5) + exp(-12πi/5) = exp(2πi/5) +
exp(-2πi/5) = 2·cos(2π/5) = (√5-1)/2 = 1/φ`. -/
theorem R1_C_sq_add_cube_eq_φInv :
    R1_C ^ 2 + R1_C ^ 3 = (Real.goldenRatio⁻¹ : ℂ) := by
  -- Strategy: show LHS = 2 · cos(2π/5) (real-cast); then bridge to 1/φ.
  unfold R1_C
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  -- LHS = exp(2·(-4π/5)·I) + exp(3·(-4π/5)·I) = exp(-8π/5·I) + exp(-12π/5·I)
  -- Mod 2π: -8π/5 ≡ 2π/5; -12π/5 ≡ -2π/5.
  have h1 : ((2 : ℕ) : ℂ) * (((-4 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) =
              ((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I +
              ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  have h2 : ((3 : ℕ) : ℂ) * (((-4 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) =
              -(((2 * Real.pi / 5 : ℝ) : ℂ)) * Complex.I +
              ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one, mul_one]
  -- Goal: exp(θ·I) + exp(-θ·I) = (1/φ : ℂ), where θ = 2π/5
  rw [exp_z_I_add_exp_neg_z_I ((2 * Real.pi / 5 : ℝ) : ℂ)]
  -- Now goal: 2 * Complex.cos ((2π/5 : ℝ) : ℂ) = ((Real.goldenRatio⁻¹ : ℝ) : ℂ)
  rw [show Complex.cos ((2 * Real.pi / 5 : ℝ) : ℂ) =
        ((Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) from
        (Complex.ofReal_cos _).symm]
  rw [show (2 : ℂ) * ((Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) =
        ((2 * Real.cos (2 * Real.pi / 5) : ℝ) : ℂ) by push_cast; ring]
  rw [show (2 * Real.cos (2 * Real.pi / 5) : ℝ) = (Real.goldenRatio⁻¹ : ℝ) by
    rw [two_cos_two_pi_div_five, goldenRatio_inv_eq]]
  push_cast
  rfl

/-! ## 6. Rotation identity: `Rtau_C = -R1_C^3`

A second algebraic ingredient for the YB proof: the rotation relating
R₁ and R_τ. We have `R1_C = exp(-4πi/5)` and `Rtau_C = exp(3πi/5)`.
Since `R1_C^3 = exp(-12πi/5) = exp(-2πi/5)` (mod 2π) and
`-exp(-2πi/5) = exp(iπ - 2πi/5) = exp(3πi/5) = Rtau_C`, we get
`Rtau_C = -R1_C^3`. -/

/-- `Rtau_C = -R1_C^3`: the rotation identity. -/
theorem Rtau_C_eq_neg_R1_C_pow_3 : Rtau_C = -(R1_C ^ 3) := by
  unfold R1_C Rtau_C
  rw [← Complex.exp_nat_mul]
  -- show exp((3π/5)·I) = -exp(3 · (-4π/5)·I)
  -- 3·(-4π/5)·I = -12π/5·I
  -- exp(-12π/5·I) + π·I·shift = exp(-12π/5·I + π·I + 2π·I) where the 2π·I lifts to 1
  -- Compute: 3π/5 = -12π/5 + π + 2π = (-12π + 5π + 10π)/5 = 3π/5 ✓
  -- So: exp(3π/5·I) = exp(π·I)·exp(2π·I)·exp(-12π/5·I) = (-1)·1·R1_C^3 = -R1_C^3
  have heq : ((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I =
              (Real.pi : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
              ((3 : ℕ) : ℂ) * (((-4 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [heq, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I 1,
      Complex.exp_pi_mul_I, mul_one]
  ring

/-! ## 7. Core algebraic identities for Yang-Baxter

The key φ-identities used in the YB proof. -/

/-- `φInv_C² + φInv_C = 1` — the F²=I diagonal identity, lifted from
`F_C_diag_identity` by replacing `φInvSqrt_C²` with `φInv_C`. -/
theorem φInv_C_sq_add_self : φInv_C ^ 2 + φInv_C = 1 := by
  have h := F_C_diag_identity
  have hsq : φInvSqrt_C * φInvSqrt_C = φInv_C := by
    have := φInvSqrt_C_sq; rw [sq] at this; exact this
  rw [hsq] at h
  linear_combination h

/-- `φInv_C³ = 2·φInv_C - 1` — derived from `φInv_C² + φInv_C = 1`. -/
theorem φInv_C_pow_3 : φInv_C ^ 3 = 2 * φInv_C - 1 := by
  have h := φInv_C_sq_add_self
  -- φInv_C^3 = φInv_C · φInv_C^2 = φInv_C · (1 - φInv_C)
  -- = φInv_C - φInv_C^2 = φInv_C - (1 - φInv_C) = 2*φInv_C - 1
  linear_combination φInv_C * h - h

/-- **Core YB algebraic identity** (the substantive content all 4 YB
entries reduce to):

`φInv_C² · (R1_C² + Rtau_C²) + (2·φInv_C - 1) · R1_C · Rtau_C = 0`

Proof: substitute `Rtau_C = -R1_C^3`, then `R1_C^5 = 1`, then bridge
`R1_C² + R1_C³ = φInv_C`, then algebraic identity `φInv_C³ = 2·φInv_C - 1`.

Strategy: multiply both sides by `R1_C` (nonzero) to convert `R1_C^4`
into `R1_C^5 = 1`, then linear-combine the three substrate identities. -/
theorem fib_yb_core_identity :
    φInv_C ^ 2 * (R1_C ^ 2 + Rtau_C ^ 2) +
      (2 * φInv_C - 1) * R1_C * Rtau_C = 0 := by
  rw [Rtau_C_eq_neg_R1_C_pow_3]
  have hR5 : R1_C ^ 5 = 1 := R1_C_pow_5
  -- Convert the bridge to the φInv_C form (handle ℝ→ℂ cast).
  have hbridge : R1_C ^ 2 + R1_C ^ 3 = φInv_C := by
    have h := R1_C_sq_add_cube_eq_φInv
    unfold φInv_C
    rw [h]
    push_cast; rfl
  have hφ3 : φInv_C ^ 3 = 2 * φInv_C - 1 := φInv_C_pow_3
  have hR1_ne : R1_C ≠ 0 := by
    intro h
    have h2 : ‖R1_C‖ = 0 := by rw [h, norm_zero]
    rw [norm_R1_C] at h2; norm_num at h2
  -- Reduce to showing R1_C * (LHS) = R1_C * 0
  refine mul_left_cancel₀ hR1_ne ?_
  rw [mul_zero]
  -- New goal: R1_C * (φInv_C^2 * (R1_C^2 + (-R1_C^3)^2) +
  --                   (2*φInv_C - 1) * R1_C * (-R1_C^3)) = 0
  -- = φInv_C^2 * R1_C^3 + φInv_C^2 * R1_C^7 - (2*φInv_C - 1) * R1_C^5
  -- Combine via linear_combination with coefficients derived from manual analysis:
  --   c_hR5 := φInv_C^2 * R1_C^2 - (2*φInv_C - 1)
  --   c_hbridge := φInv_C^2
  --   c_hφ3 := 1
  linear_combination
    (φInv_C ^ 2 * R1_C ^ 2 - (2 * φInv_C - 1)) * hR5 +
    φInv_C ^ 2 * hbridge + hφ3

/-! ## 8. σ_Fib_2 entry-level computations + Yang-Baxter matrix entries

Compute each entry of `σ_Fib_2 = F_C · σ_Fib_1 · F_C` directly,
using `q² = p` to simplify (where p = φInv_C, q = φInvSqrt_C). -/

/-- σ_Fib_1 entry [0,0] = R1_C. -/
private theorem σ_Fib_1_apply_00 : σ_Fib_1 0 0 = R1_C := rfl

/-- σ_Fib_1 entry [0,1] = 0. -/
private theorem σ_Fib_1_apply_01 : σ_Fib_1 0 1 = 0 := rfl

/-- σ_Fib_1 entry [1,0] = 0. -/
private theorem σ_Fib_1_apply_10 : σ_Fib_1 1 0 = 0 := rfl

/-- σ_Fib_1 entry [1,1] = Rtau_C. -/
private theorem σ_Fib_1_apply_11 : σ_Fib_1 1 1 = Rtau_C := rfl

/-- F_C entry [0,0] = φInv_C. -/
private theorem F_C_apply_00 : F_C 0 0 = φInv_C := rfl

/-- F_C entry [0,1] = φInvSqrt_C. -/
private theorem F_C_apply_01 : F_C 0 1 = φInvSqrt_C := rfl

/-- F_C entry [1,0] = φInvSqrt_C. -/
private theorem F_C_apply_10 : F_C 1 0 = φInvSqrt_C := rfl

/-- F_C entry [1,1] = -φInv_C. -/
private theorem F_C_apply_11 : F_C 1 1 = -φInv_C := rfl

/-- σ_Fib_2[0,0] = φInv_C² · R1_C + φInv_C · Rtau_C. -/
theorem σ_Fib_2_apply_00 :
    σ_Fib_2 0 0 = φInv_C ^ 2 * R1_C + φInv_C * Rtau_C := by
  unfold σ_Fib_2
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_two, Matrix.mul_apply,
             σ_Fib_1_apply_00, σ_Fib_1_apply_01, σ_Fib_1_apply_10, σ_Fib_1_apply_11,
             F_C_apply_00, F_C_apply_01, F_C_apply_10, F_C_apply_11,
             mul_zero, zero_mul, add_zero, zero_add]
  -- Goal: φInv_C * R1_C * φInv_C + φInvSqrt_C * Rtau_C * φInvSqrt_C = φInv_C² · R1_C + φInv_C · Rtau_C
  have hq2 : φInvSqrt_C * φInvSqrt_C = φInv_C := by
    have := φInvSqrt_C_sq; rw [sq] at this; exact this
  linear_combination Rtau_C * hq2

/-- σ_Fib_2[0,1] = φInv_C · φInvSqrt_C · (R1_C - Rtau_C). -/
theorem σ_Fib_2_apply_01 :
    σ_Fib_2 0 1 = φInv_C * φInvSqrt_C * (R1_C - Rtau_C) := by
  unfold σ_Fib_2
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_two, Matrix.mul_apply,
             σ_Fib_1_apply_00, σ_Fib_1_apply_01, σ_Fib_1_apply_10, σ_Fib_1_apply_11,
             F_C_apply_00, F_C_apply_01, F_C_apply_10, F_C_apply_11,
             mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- σ_Fib_2[1,0] = σ_Fib_2[0,1] = φInv_C · φInvSqrt_C · (R1_C - Rtau_C). -/
theorem σ_Fib_2_apply_10 :
    σ_Fib_2 1 0 = φInv_C * φInvSqrt_C * (R1_C - Rtau_C) := by
  unfold σ_Fib_2
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_two, Matrix.mul_apply,
             σ_Fib_1_apply_00, σ_Fib_1_apply_01, σ_Fib_1_apply_10, σ_Fib_1_apply_11,
             F_C_apply_00, F_C_apply_01, F_C_apply_10, F_C_apply_11,
             mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- σ_Fib_2[1,1] = φInv_C · R1_C + φInv_C² · Rtau_C. -/
theorem σ_Fib_2_apply_11 :
    σ_Fib_2 1 1 = φInv_C * R1_C + φInv_C ^ 2 * Rtau_C := by
  unfold σ_Fib_2
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_two, Matrix.mul_apply,
             σ_Fib_1_apply_00, σ_Fib_1_apply_01, σ_Fib_1_apply_10, σ_Fib_1_apply_11,
             F_C_apply_00, F_C_apply_01, F_C_apply_10, F_C_apply_11,
             mul_zero, zero_mul, add_zero, zero_add]
  have hq2 : φInvSqrt_C * φInvSqrt_C = φInv_C := by
    have := φInvSqrt_C_sq; rw [sq] at this; exact this
  linear_combination R1_C * hq2

/-- **Yang-Baxter matrix entry [0,0]** (R4.2.b.3, this commit):

`(σ_Fib_1 * σ_Fib_2 * σ_Fib_1) 0 0 = (σ_Fib_2 * σ_Fib_1 * σ_Fib_2) 0 0`

After expanding via `Matrix.mul_apply` + `Fin.sum_univ_two`, both sides
become polynomials in `{R1_C, Rtau_C, φInv_C, φInvSqrt_C}`. Manual
coefficient derivation (see comments inside the proof) yields:

  LHS - RHS = c_phisqrt · (φInvSqrt_C² - φInv_C)
            + c_hcore   · (φInv_C² · (R1_C² + Rtau_C²) + (2·φInv_C - 1)·R1_C·Rtau_C)
            + c_hsq     · (φInv_C² + φInv_C - 1)

with
  c_phisqrt = -φInv_C² · Rtau_C · (R1_C - Rtau_C)²
  c_hcore   = (R1_C - Rtau_C) · φInv_C
  c_hsq     = -φInv_C² · R1_C³ - 2·φInv_C·R1_C²·Rtau_C + φInv_C·R1_C·Rtau_C²

The strategy and coefficient derivation is documented in §9. -/
theorem σ_Fib_yb_entry_00 :
    (σ_Fib_1 * σ_Fib_2 * σ_Fib_1) 0 0 =
      (σ_Fib_2 * σ_Fib_1 * σ_Fib_2) 0 0 := by
  -- Step 1: Expand matrix products
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
             σ_Fib_1_apply_00, σ_Fib_1_apply_01, σ_Fib_1_apply_10, σ_Fib_1_apply_11,
             σ_Fib_2_apply_00, σ_Fib_2_apply_01, σ_Fib_2_apply_10, σ_Fib_2_apply_11,
             mul_zero, zero_mul, add_zero, zero_add]
  -- Step 2: Set up hypotheses
  have hq2 : φInvSqrt_C ^ 2 = φInv_C := φInvSqrt_C_sq
  have hsq : φInv_C ^ 2 + φInv_C = 1 := φInv_C_sq_add_self
  have hcore : φInv_C ^ 2 * (R1_C ^ 2 + Rtau_C ^ 2) +
               (2 * φInv_C - 1) * R1_C * Rtau_C = 0 := fib_yb_core_identity
  -- Step 3: linear_combination with hand-derived coefficients
  linear_combination
    (-(φInv_C ^ 2 * Rtau_C * (R1_C - Rtau_C) ^ 2)) * hq2 +
    ((R1_C - Rtau_C) * φInv_C) * hcore +
    (-(φInv_C ^ 2 * R1_C ^ 3) - 2 * φInv_C * R1_C ^ 2 * Rtau_C +
      φInv_C * R1_C * Rtau_C ^ 2) * hsq

/-- **Yang-Baxter matrix entry [0,1]** (R4.2.b.3).

After expansion via `Matrix.mul_apply`:
  LHS[0,1] = R1_C · σ_Fib_2[0,1] · Rtau_C = φInv_C · φInvSqrt_C · R1_C · Rtau_C · (R1_C - Rtau_C)
  RHS[0,1] = factors as φInv_C · φInvSqrt_C · (R1_C - Rtau_C) · [φInv_C²·(R1_C² + Rtau_C²) + 2·φInv_C·R1_C·Rtau_C]

The difference factors cleanly as `-φInv_C · φInvSqrt_C · (R1_C - Rtau_C) · hcore`,
so only `fib_yb_core_identity` is needed (no `hq2` or `hsq` consumed). -/
theorem σ_Fib_yb_entry_01 :
    (σ_Fib_1 * σ_Fib_2 * σ_Fib_1) 0 1 =
      (σ_Fib_2 * σ_Fib_1 * σ_Fib_2) 0 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
             σ_Fib_1_apply_00, σ_Fib_1_apply_01, σ_Fib_1_apply_10, σ_Fib_1_apply_11,
             σ_Fib_2_apply_00, σ_Fib_2_apply_01, σ_Fib_2_apply_10, σ_Fib_2_apply_11,
             mul_zero, zero_mul, add_zero, zero_add]
  have hcore : φInv_C ^ 2 * (R1_C ^ 2 + Rtau_C ^ 2) +
               (2 * φInv_C - 1) * R1_C * Rtau_C = 0 := fib_yb_core_identity
  linear_combination
    (-(φInv_C * φInvSqrt_C * (R1_C - Rtau_C))) * hcore

/-- **Yang-Baxter matrix entry [1,0]** (R4.2.b.3).

By σ_Fib_2 symmetry (σ_Fib_2[0,1] = σ_Fib_2[1,0]) and σ_Fib_1 being diagonal,
LHS[1,0] = LHS[0,1] and RHS[1,0] = RHS[0,1], so the proof is structurally
identical to `σ_Fib_yb_entry_01`. -/
theorem σ_Fib_yb_entry_10 :
    (σ_Fib_1 * σ_Fib_2 * σ_Fib_1) 1 0 =
      (σ_Fib_2 * σ_Fib_1 * σ_Fib_2) 1 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
             σ_Fib_1_apply_00, σ_Fib_1_apply_01, σ_Fib_1_apply_10, σ_Fib_1_apply_11,
             σ_Fib_2_apply_00, σ_Fib_2_apply_01, σ_Fib_2_apply_10, σ_Fib_2_apply_11,
             mul_zero, zero_mul, add_zero, zero_add]
  have hcore : φInv_C ^ 2 * (R1_C ^ 2 + Rtau_C ^ 2) +
               (2 * φInv_C - 1) * R1_C * Rtau_C = 0 := fib_yb_core_identity
  linear_combination
    (-(φInv_C * φInvSqrt_C * (R1_C - Rtau_C))) * hcore

/-- **Yang-Baxter matrix entry [1,1]** (R4.2.b.3).

By the `R1_C ↔ Rtau_C` symmetry of the [0,0] case, the same coefficient structure
applies with R1_C and Rtau_C swapped in `c_phisqrt`, `c_hcore`, and `c_hsq`. -/
theorem σ_Fib_yb_entry_11 :
    (σ_Fib_1 * σ_Fib_2 * σ_Fib_1) 1 1 =
      (σ_Fib_2 * σ_Fib_1 * σ_Fib_2) 1 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
             σ_Fib_1_apply_00, σ_Fib_1_apply_01, σ_Fib_1_apply_10, σ_Fib_1_apply_11,
             σ_Fib_2_apply_00, σ_Fib_2_apply_01, σ_Fib_2_apply_10, σ_Fib_2_apply_11,
             mul_zero, zero_mul, add_zero, zero_add]
  have hq2 : φInvSqrt_C ^ 2 = φInv_C := φInvSqrt_C_sq
  have hsq : φInv_C ^ 2 + φInv_C = 1 := φInv_C_sq_add_self
  have hcore : φInv_C ^ 2 * (R1_C ^ 2 + Rtau_C ^ 2) +
               (2 * φInv_C - 1) * R1_C * Rtau_C = 0 := fib_yb_core_identity
  linear_combination
    (-(φInv_C ^ 2 * R1_C * (R1_C - Rtau_C) ^ 2)) * hq2 +
    ((Rtau_C - R1_C) * φInv_C) * hcore +
    (-(φInv_C ^ 2 * Rtau_C ^ 3) - 2 * φInv_C * R1_C * Rtau_C ^ 2 +
      φInv_C * R1_C ^ 2 * Rtau_C) * hsq

/-- **Yang-Baxter matrix relation** (R4.2.b.3 SHIP, this commit).

`σ_Fib_1 * σ_Fib_2 * σ_Fib_1 = σ_Fib_2 * σ_Fib_1 * σ_Fib_2`

Assembled from the 4 entry-level theorems via `Matrix.ext` + `Fin.cases`.
This is the load-bearing braid relation for the Fibonacci 2-anyon-strand
representation, lifting `RouabahExplicit.lean`'s native_decide-on-QCyc20 proof
to the analytic complex-number version where R4.2 continuation (det normalization +
substantive density) takes over. -/
theorem σ_Fib_yang_baxter :
    σ_Fib_1 * σ_Fib_2 * σ_Fib_1 = σ_Fib_2 * σ_Fib_1 * σ_Fib_2 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact σ_Fib_yb_entry_00
  · exact σ_Fib_yb_entry_01
  · exact σ_Fib_yb_entry_10
  · exact σ_Fib_yb_entry_11

/-! ## 9. Yang-Baxter algebraic reduction (R4.2.b.3 implementation notes)

With the bridge identity `R1_C² + R1_C³ = 1/φ` and rotation
`Rtau_C = -R1_C³`, the per-entry YB proofs (R4.2.b.3, this commit)
follow this structure. Throughout, abbreviate `p = φInv_C`,
`q = φInvSqrt_C`, `a = R1_C`, `b = Rtau_C`. Recall `q² = p`,
`p² + p = 1`, and the core identity
`hcore : p²·(a² + b²) + (2p - 1)·a·b = 0`.

  **Step 1 — Expand**: Apply `Matrix.mul_apply` + `Fin.sum_univ_two`,
  then substitute `σ_Fib_{1,2}_apply_*` to reduce each entry equation
  to a polynomial identity in `{a, b, p, q}`.

  **Step 2 — Coefficient discovery (YB[0,0])**:
  After expansion, `LHS - RHS` has the form
      LHS - RHS = c_hcore·hcore_LHS + c_hsq·(p²+p-1) + c_phisqrt·(q²-p)
  Manual derivation (see fib_yb_core_identity proof comments + this
  documentation) yields:
      c_hcore   = (a - b)·p
      c_hsq     = -p²·a³ - 2·p·a²·b + p·a·b²
      c_phisqrt = -p²·b·(a - b)²
  These are the coefficients fed to `linear_combination` in
  `σ_Fib_yb_entry_00`; `ring` then closes the residual.

  **Step 3 — Symmetry (YB[1,1])**: Under the involution `a ↔ b`,
  LHS[1,1] - RHS[1,1] = the a↔b swap of LHS[0,0] - RHS[0,0]. Thus
  σ_Fib_yb_entry_11 uses the coefficients of [0,0] with a ↔ b swap:
      c_hcore   = (b - a)·p     (sign flip via the swap)
      c_hsq     = -p²·b³ - 2·p·a·b² + p·a²·b
      c_phisqrt = -p²·a·(a - b)²    (since (b-a)² = (a-b)²)

  **Step 4 — Off-diagonal (YB[0,1] = YB[1,0])**: By symmetry of
  σ_Fib_2 (σ_Fib_2[0,1] = σ_Fib_2[1,0]) and the diagonality of σ_Fib_1,
  both LHS[0,1] = LHS[1,0] = p·q·a·b·(a-b), and similarly for the RHS.
  The difference factors cleanly:
      LHS - RHS = -p·q·(a-b)·hcore_LHS
  So only one hypothesis is consumed:  c_hcore = -p·q·(a-b),
  no hq2 or hsq needed.

  **Step 5 — Matrix assembly**: `σ_Fib_yang_baxter` follows by
  `Matrix.ext` + `fin_cases` over the four entry lemmas.

This completes the analytical path from R4.1 substrate
(`braidGroup3HomFromPair`) + R4.2.a/b substrate (σ_1, σ_2 unitary, det)
+ R4.2.b.1 bridge + R4.2.b.2 core identity to the full Yang-Baxter
relation `σ_Fib_1 · σ_Fib_2 · σ_Fib_1 = σ_Fib_2 · σ_Fib_1 · σ_Fib_2`. -/

/-! ## 7. Module summary

FibSU2Rep.lean (Phase 6p Wave 2c.4a-R4.2.a + R4.2.b.{1,2,3}, 2026-05-13):

**Substrate provided (this ship, 2026-05-13)**:
  - `R1_C, Rtau_C : ℂ` — Fibonacci R-matrix eigenvalues in ℂ.
  - `norm_R1_C, norm_Rtau_C` — unit-modulus proofs.
  - `φ_C, φInv_C, φInvSqrt_C : ℂ` — golden ratio + reciprocal + square root reciprocal.
  - `φ_C_sq, φ_C_mul_inv, φInvSqrt_C_sq` — algebraic identities.
  - `F_C : Matrix (Fin 2) (Fin 2) ℂ` — the Fibonacci F-matrix.
  - **`F_C_sq : F_C * F_C = 1`** — F is an involution.
  - **`F_C_star : star F_C = F_C`** — F is Hermitian (real-valued + symmetric).
  - **`F_C_unitary : F_C * star F_C = 1`** — F is unitary (Hermitian + F²=I).
  - `σ_Fib_1, σ_Fib_2 : Matrix (Fin 2) (Fin 2) ℂ` — braid generators in U(2).
  - **`σ_Fib_1_unitary : σ_Fib_1 * star σ_Fib_1 = 1`** — σ_1 unitary.
  - **`σ_Fib_2_unitary : σ_Fib_2 * star σ_Fib_2 = 1`** — σ_2 unitary (via F + σ_1).
  - **`σ_Fib_1_det : σ_Fib_1.det = R1_C * Rtau_C`** — det of σ_1.
  - **`σ_Fib_2_det_eq_σ_Fib_1_det : σ_Fib_2.det = σ_Fib_1.det`** — det
    invariance under F-conjugation.

**R4.2.b.1 ship (commit 64fc14b)**: cyclotomic-Fibonacci bridge identity:
  - `R1_C_pow_5 : R1_C^5 = 1` (5th root of unity)
  - `Rtau_C_pow_5 : Rtau_C^5 = -1` (10th root of unity)
  - `Rtau_C_pow_10 : Rtau_C^10 = 1`
  - **`Rtau_C_eq_neg_R1_C_pow_3 : Rtau_C = -R1_C^3`** — rotation identity
    linking the two R-eigenvalues
  - **`R1_C_sq_add_cube_eq_φInv : R1_C^2 + R1_C^3 = (Real.goldenRatio⁻¹ : ℂ)`** —
    THE LOAD-BEARING BRIDGE: links cyclotomic field Q(ζ_5) to golden-ratio
    field Q(√5) via `2·cos(2π/5) = (√5-1)/2 = 1/φ` (proved using
    `Real.cos_pi_div_five = (1+√5)/4` + double-angle formula).
  - Plus auxiliary `exp_z_I_add_exp_neg_z_I : exp(z·I) + exp(-z·I) = 2·cos z`
    (reusable Euler-formula lemma).

**R4.2.b.2 ship (commit deddb99)**: core YB algebraic identity + σ_Fib_2 entries:
  - **`fib_yb_core_identity`** : `φInv_C²·(R1_C² + Rtau_C²) + (2·φInv_C - 1)·R1_C·Rtau_C = 0`
    — the substantive algebraic content all 4 YB entries reduce to.
  - `φInv_C_sq_add_self : φInv_C² + φInv_C = 1` (lifted from F²=I).
  - `φInv_C_pow_3 : φInv_C³ = 2·φInv_C - 1`.
  - `σ_Fib_2_apply_{00,01,10,11}` matrix entry lemmas (using `q²=p`).

**R4.2.b.3 ship (this commit)**: Yang-Baxter matrix relation.
  - `σ_Fib_yb_entry_{00,01,10,11}` — per-entry braid identities, each
    proved by `linear_combination` with hand-derived polynomial coefficients
    against `{hcore, φInv_C_sq_add_self, φInvSqrt_C_sq}`.
  - **`σ_Fib_yang_baxter : σ_Fib_1 * σ_Fib_2 * σ_Fib_1 = σ_Fib_2 * σ_Fib_1 * σ_Fib_2`**
    — full matrix-level Yang-Baxter relation, assembled by `Matrix.ext` +
    `Fin.cases` over the four entry lemmas. Standard-kernel-only.

**Deferred to R4.2.c sub-wave (det normalization + MonoidHom)**:
  - ω = exp(πi/10) det-normalization to bring σ_1, σ_2 into SU(2).
  - `ρ_Fib_SU2 : BraidGroup 3 →* SU(2)` via `braidGroup3HomFromPair`.

**Deferred to R4.2.d sub-wave (substantive density)**:
  - `closure(Set.range ρ_Fib_SU2) = Set.univ`
  - Either constructive (Weyl-equidistribution + Euler-axes) or scoped
    HBS axiom with user sign-off.

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new axioms): RESPECTED (zero introduced).

Zero sorry. Zero new project-local axioms in this module.
-/

end SKEFTHawking.FKLW
