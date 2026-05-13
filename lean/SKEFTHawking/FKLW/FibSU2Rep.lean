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

/-! ## 5. Module summary

FibSU2Rep.lean (Phase 6p Wave 2c.4a-R4.2.a, 2026-05-13):

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

**Deferred to R4.2.b proper sub-wave (Yang-Baxter)**:
  - `σ_Fib_1 * σ_Fib_2 * σ_Fib_1 = σ_Fib_2 * σ_Fib_1 * σ_Fib_2` over ℂ.
  - Either direct algebraic proof (~200-500 LoC) or ring-hom transport
    from QCyc40Ext native_decide proof (~200-400 LoC of cyclotomic
    embedding infrastructure).

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
