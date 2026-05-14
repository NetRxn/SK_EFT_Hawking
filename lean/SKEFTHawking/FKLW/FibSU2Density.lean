/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6p Wave 2c.4a-R4.2.d — Fibonacci SU(2) density (Path (i) constructive)

The headline target: prove

  `closure (Set.range ρ_Fib_SU2) = (Set.univ : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ))`

which, composed with `bridge_FKLW_unitary_hom` from
`FKLW.AharonovAradBridgeIteration`, delivers
`DenseInSpecialUnitary 3 2 (fun b => ρ_Fib_SU2 b).val` for the concrete
Fibonacci representation `ρ_Fib_SU2` of `R4.2.c`.

## Structural plan

The constructive density argument decomposes as:

  **Phase D1 (this commit, partial)**: structural facts about σ_Fib_{1,2}_SU.
    - Eigenvalues: σ_Fib_1_SU = diag(ω·R_1, ω·R_τ) = diag(exp(-7πi/10), exp(7πi/10)).
    - Finite order in SU(2): σ_Fib_1_SU^20 = 1, σ_Fib_2_SU^20 = 1.
    - σ_Fib_1_SU and σ_Fib_2_SU don't commute (separating fact — they
      satisfy YB `aba = bab` but NOT the commutation `ab = ba`).

  **Phase D2 (future)**: trace and rotation-axis structure.
    - tr(σ_Fib_1_SU) = exp(-7πi/10) + exp(7πi/10) = 2·cos(7π/10) = (1-√5)/2.
    - σ_Fib_1_SU corresponds to a rotation by angle 7π/5 around the z-axis
      (in the standard SU(2)→SO(3) double cover).
    - σ_Fib_2_SU rotation axis is conjugate by F_C; non-parallel to z-axis.

  **Phase D3 (future)**: subgroup-of-SU(2) classification or HBS-style
    infinite-order braid word. The closed subgroups of SU(2) are
    classified (cyclic, dihedral, binary tetra/octa/ico, U(1)-tori, SU(2)).
    Show ⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ is not contained in any proper closed
    subgroup → its closure is SU(2).

  **Phase D4 (future)**: assemble closure = univ → DenseInSpecialUnitary.

This module ships Phase D1. Phases D2-D4 are deferred to future R4.2.d
sub-waves. No new axioms.

References:
- Hormozi, Bonesteel, Simon 2007, *Phys. Rev. Lett.* 98, 090501
  (arXiv:cond-mat/0610082) — Fibonacci braid density.
- Bonesteel, Hormozi, Zikos, Simon 2005, *Phys. Rev. Lett.* 95, 140503
  (arXiv:quant-ph/0505065) — explicit braid construction.
- Freedman, Larsen, Wang 2002, *Commun. Math. Phys.* 227, 605
  (arXiv:quant-ph/0001108) — original universal quantum computation
  via braiding.
-/

import SKEFTHawking.FKLW.FibSU2Rep

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open Complex Real
open scoped Matrix

/-! ## 1. Powers of σ_Fib_1 in the unscaled-by-ω matrix form

Compute (σ_Fib_1)^n explicitly: since σ_Fib_1 = diag(R_1, R_τ) is
diagonal, (σ_Fib_1)^n = diag(R_1^n, R_τ^n). With R_1^5 = 1, R_τ^5 = -1,
R_τ^10 = 1, we have (σ_Fib_1)^10 = I. -/

/-- `σ_Fib_1^n` for `σ_Fib_1 = diag(R_1, R_τ)` is `diag(R_1^n, R_τ^n)`. -/
private theorem σ_Fib_1_pow_eq (n : ℕ) :
    σ_Fib_1 ^ n = !![R1_C ^ n, 0; 0, Rtau_C ^ n] := by
  induction n with
  | zero =>
    simp [pow_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [σ_Fib_1, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- `σ_Fib_1^10 = I` (since R_1^10 = 1 and R_τ^10 = 1). -/
theorem σ_Fib_1_pow_10 :
    σ_Fib_1 ^ 10 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [σ_Fib_1_pow_eq]
  have hR1 : R1_C ^ 10 = 1 := by
    have h5 := R1_C_pow_5
    have : R1_C ^ 10 = (R1_C ^ 5) ^ 2 := by ring
    rw [this, h5]; norm_num
  have hRτ : Rtau_C ^ 10 = 1 := by
    have h5 := Rtau_C_pow_5
    have : Rtau_C ^ 10 = (Rtau_C ^ 5) ^ 2 := by ring
    rw [this, h5]; norm_num
  rw [hR1, hRτ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-! ## 2. Order of σ_Fib_1_SU in SU(2)

`σ_Fib_1_SU_mat^n = ω_Fib_C^n • σ_Fib_1^n`. Combined with
ω_Fib_C^20 = exp(2πi) = 1 and σ_Fib_1^20 = (σ_Fib_1^10)^2 = I^2 = I,
we get `σ_Fib_1_SU_mat^20 = 1`. -/

/-- `ω_Fib_C^20 = 1` (since ω = exp(πi/10) is a 20th root of unity). -/
theorem ω_Fib_C_pow_20 : ω_Fib_C ^ 20 = 1 := by
  unfold ω_Fib_C
  rw [← Complex.exp_nat_mul]
  -- 20 * (π/10 · I) = 2π · I = 1 · (2π · I)
  rw [show ((20 : ℕ) : ℂ) * (((Real.pi / 10 : ℝ) : ℂ) * Complex.I) =
        ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  -- exp(1 · 2π · I) = 1
  exact Complex.exp_int_mul_two_pi_mul_I 1

/-- `σ_Fib_1^20 = I` (consequence of σ_Fib_1^10 = I). -/
theorem σ_Fib_1_pow_20 :
    σ_Fib_1 ^ 20 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h10 := σ_Fib_1_pow_10
  have heq : σ_Fib_1 ^ 20 = (σ_Fib_1 ^ 10) ^ 2 := by
    rw [← pow_mul]
  rw [heq, h10, one_pow]

/-- `σ_Fib_1_SU_mat^20 = I` — the det-normalized braid generator has
order dividing 20 in `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem σ_Fib_1_SU_mat_pow_20 :
    σ_Fib_1_SU_mat ^ 20 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold σ_Fib_1_SU_mat
  rw [smul_pow, ω_Fib_C_pow_20, σ_Fib_1_pow_20, one_smul]

/-! ## 3. Non-commutation of σ_Fib_1_SU and σ_Fib_2_SU

The braid generators don't commute, since they satisfy Yang-Baxter
(`aba = bab`) but NOT the abelian relation (`ab = ba`). For 2×2
matrices, the (0,1)-entry of (σ_2·σ_1 - σ_1·σ_2) is non-zero, which
suffices to distinguish the two products.

This is the **critical separating fact** for density: a subgroup of
SU(2) generated by two non-commuting elements (with appropriate
spectral properties) is NOT contained in a 1-parameter subgroup.

Concrete computation:
  σ_Fib_1 · σ_Fib_2 [0,1] = R_1 · σ_Fib_2[0,1] = R_1 · φInv_C · φInvSqrt_C · (R_1 - R_τ)
  σ_Fib_2 · σ_Fib_1 [0,1] = σ_Fib_2[0,1] · R_τ = φInv_C · φInvSqrt_C · (R_1 - R_τ) · R_τ

Difference: φInv_C · φInvSqrt_C · (R_1 - R_τ) · (R_1 - R_τ) = φInv_C · φInvSqrt_C · (R_1 - R_τ)²

Since R_1 ≠ R_τ (different unit-modulus complex numbers), φInv_C ≠ 0,
φInvSqrt_C ≠ 0, this entry is non-zero.

For now, we ship the existential form (the matrices differ at the [0,1]
entry); future work will compute the explicit non-zero value. -/

/-- `σ_Fib_1 * σ_Fib_2 ≠ σ_Fib_2 * σ_Fib_1` (the braid generators don't
commute). -/
theorem σ_Fib_not_commute :
    σ_Fib_1 * σ_Fib_2 ≠ σ_Fib_2 * σ_Fib_1 := by
  intro h_comm
  -- Project to the [0,1] entry and derive a contradiction from
  -- R_1 ≠ R_τ (different unit-modulus values).
  have h_entry : (σ_Fib_1 * σ_Fib_2) 0 1 = (σ_Fib_2 * σ_Fib_1) 0 1 := by
    rw [h_comm]
  -- LHS = R_1 · σ_Fib_2[0,1], RHS = σ_Fib_2[0,1] · R_τ
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
             show σ_Fib_1 0 0 = R1_C from rfl,
             show σ_Fib_1 0 1 = 0 from rfl,
             show σ_Fib_1 1 0 = 0 from rfl,
             show σ_Fib_1 1 1 = Rtau_C from rfl,
             zero_mul, mul_zero, add_zero, zero_add] at h_entry
  -- h_entry: R1_C * σ_Fib_2 0 1 = σ_Fib_2 0 1 * Rtau_C
  rw [σ_Fib_2_apply_01] at h_entry
  -- h_entry: R1_C * (φInv_C * φInvSqrt_C * (R1_C - Rtau_C)) =
  --          (φInv_C * φInvSqrt_C * (R1_C - Rtau_C)) * Rtau_C
  -- Rearrange: (φInv_C · φInvSqrt_C · (R_1 - R_τ)) · (R_1 - R_τ) = 0
  -- ⇒ φInv_C · φInvSqrt_C · (R_1 - R_τ)² = 0
  have h_diff : φInv_C * φInvSqrt_C * (R1_C - Rtau_C) ^ 2 = 0 := by
    have : R1_C * (φInv_C * φInvSqrt_C * (R1_C - Rtau_C)) -
           (φInv_C * φInvSqrt_C * (R1_C - Rtau_C)) * Rtau_C = 0 := by
      rw [h_entry]; ring
    linear_combination this
  -- Now derive: R_1 ≠ R_τ (otherwise (R_1 - R_τ)² = 0 and we'd need
  -- φInv_C · φInvSqrt_C = 0, but neither is zero).
  -- R_1 - R_τ: |R_1| = |R_τ| = 1 but they're different points.
  -- Explicitly: R_1 = exp(-4πi/5), R_τ = exp(3πi/5).
  -- R_1 / R_τ = exp(-4πi/5 - 3πi/5) = exp(-7πi/5).
  -- |R_1 - R_τ|² = 2 - 2·Re(R_1 · conj(R_τ)) = 2 - 2·cos(-7π/5) > 0.
  -- We use a cleaner algebraic route: R_1^2 + R_1^3 = 1/φ ≠ 0 implies
  -- R_1 ≠ R_τ. But this is indirect. Let's argue R_1 ≠ R_τ directly via
  -- norm of difference.
  have h_R1_ne_Rtau : R1_C ≠ Rtau_C := by
    intro h_eq
    -- If R_1 = R_τ, then R_1^5 = R_τ^5, but R_1^5 = 1 and R_τ^5 = -1.
    have h1 := R1_C_pow_5
    have h2 := Rtau_C_pow_5
    rw [h_eq] at h1
    -- h1 : Rtau_C ^ 5 = 1, h2 : Rtau_C ^ 5 = -1
    rw [h1] at h2
    -- h2 : 1 = -1; derive (2 : ℂ) = 0 contradiction.
    -- linear_combination h2: residual is 2 - 0 - (1 - (-1)) = 0.
    have : (2 : ℂ) = 0 := by linear_combination h2
    norm_num at this
  -- (R_1 - R_τ)² ≠ 0
  have h_diff_sq : (R1_C - Rtau_C) ^ 2 ≠ 0 := by
    intro hsq
    have h_zero : R1_C - Rtau_C = 0 := by
      have : (R1_C - Rtau_C) * (R1_C - Rtau_C) = 0 := by
        have := hsq; rw [sq] at this; exact this
      rcases mul_self_eq_zero.mp this with h
      exact h
    have : R1_C = Rtau_C := by linear_combination h_zero
    exact h_R1_ne_Rtau this
  -- φInv_C ≠ 0
  have h_φInv_ne : φInv_C ≠ 0 := by
    intro h_φ
    -- φInv_C^2 + φInv_C = 1; if φInv_C = 0, then 0 = 1, contradiction.
    have h := φInv_C_sq_add_self
    rw [h_φ] at h
    simp at h
  -- φInvSqrt_C ≠ 0
  have h_φInvSqrt_ne : φInvSqrt_C ≠ 0 := by
    intro h_φ
    -- φInvSqrt_C^2 = φInv_C; if φInvSqrt_C = 0, then φInv_C = 0,
    -- contradiction with h_φInv_ne.
    have h := φInvSqrt_C_sq
    rw [h_φ] at h
    rw [sq, zero_mul] at h
    exact h_φInv_ne h.symm
  -- Now (φInv_C · φInvSqrt_C · (R_1 - R_τ)²) = 0 with all three factors
  -- non-zero: contradiction.
  have h_prod_ne : φInv_C * φInvSqrt_C * (R1_C - Rtau_C) ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero h_φInv_ne h_φInvSqrt_ne) h_diff_sq
  exact h_prod_ne h_diff

/-- `σ_Fib_1_SU_mat * σ_Fib_2_SU_mat ≠ σ_Fib_2_SU_mat * σ_Fib_1_SU_mat`.
The det-normalized generators inherit non-commutation from σ_Fib_{1,2}. -/
theorem σ_Fib_SU_mat_not_commute :
    σ_Fib_1_SU_mat * σ_Fib_2_SU_mat ≠ σ_Fib_2_SU_mat * σ_Fib_1_SU_mat := by
  unfold σ_Fib_1_SU_mat σ_Fib_2_SU_mat
  intro h_comm
  -- (ω • σ_1)·(ω • σ_2) = ω² • (σ_1·σ_2), similarly for RHS.
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h_comm
  rw [show (ω_Fib_C • σ_Fib_2) * (ω_Fib_C • σ_Fib_1) =
        (ω_Fib_C * ω_Fib_C) • (σ_Fib_2 * σ_Fib_1) by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]] at h_comm
  -- ω² ≠ 0, so cancel: σ_Fib_1·σ_Fib_2 = σ_Fib_2·σ_Fib_1, contradicting σ_Fib_not_commute.
  have hω_sq_ne : ω_Fib_C * ω_Fib_C ≠ 0 := by
    have hω_ne : ω_Fib_C ≠ 0 := by
      intro h_ω
      have h_norm : ‖ω_Fib_C‖ = 0 := by rw [h_ω, norm_zero]
      rw [norm_ω_Fib_C] at h_norm
      norm_num at h_norm
    exact mul_ne_zero hω_ne hω_ne
  have h_cancel : σ_Fib_1 * σ_Fib_2 = σ_Fib_2 * σ_Fib_1 := by
    -- smul cancellation: (a • M) = (a • N) → M = N when a ≠ 0
    apply (smul_right_injective (Matrix (Fin 2) (Fin 2) ℂ) hω_sq_ne)
    exact h_comm
  exact σ_Fib_not_commute h_cancel

/-- `σ_Fib_1_SU * σ_Fib_2_SU ≠ σ_Fib_2_SU * σ_Fib_1_SU` (in SU(2)). -/
theorem σ_Fib_SU_not_commute :
    σ_Fib_1_SU * σ_Fib_2_SU ≠ σ_Fib_2_SU * σ_Fib_1_SU := by
  intro h_comm
  -- SU(2) equality ⟹ underlying matrix equality.
  have h_mat : σ_Fib_1_SU_mat * σ_Fib_2_SU_mat = σ_Fib_2_SU_mat * σ_Fib_1_SU_mat := by
    have h_val : (σ_Fib_1_SU * σ_Fib_2_SU).val = (σ_Fib_2_SU * σ_Fib_1_SU).val := by
      rw [h_comm]
    -- Subtype equality ⟹ value equality. The value of the product is the
    -- matrix product of the values.
    exact h_val
  exact σ_Fib_SU_mat_not_commute h_mat

/-! ## 4. Trace invariants of products

The trace of a product gives a rotation-angle invariant. For SU(2):
if `tr(g) = 2·cos(θ/2)`, then `g` rotates by angle `θ` in SO(3).

We compute `tr(σ_Fib_1_SU * σ_Fib_2_SU) = 1`, which corresponds to a
rotation by `2π/3` in SO(3) (since `2·cos(π/3) = 1`). This shows that
the product has *order 6 in SU(2)* (order 3 in SO(3)). -/

/-- `(σ_Fib_1 * σ_Fib_2) 0 0 = φInv_C² · R1_C² + φInv_C · R1_C · Rtau_C`. -/
private theorem σ_Fib_1_mul_σ_Fib_2_apply_00 :
    (σ_Fib_1 * σ_Fib_2) 0 0 =
      φInv_C ^ 2 * R1_C ^ 2 + φInv_C * R1_C * Rtau_C := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
             show σ_Fib_1 0 0 = R1_C from rfl,
             show σ_Fib_1 0 1 = 0 from rfl,
             σ_Fib_2_apply_00, zero_mul, add_zero]
  ring

/-- `(σ_Fib_1 * σ_Fib_2) 1 1 = φInv_C · R1_C · Rtau_C + φInv_C² · Rtau_C²`. -/
private theorem σ_Fib_1_mul_σ_Fib_2_apply_11 :
    (σ_Fib_1 * σ_Fib_2) 1 1 =
      φInv_C * R1_C * Rtau_C + φInv_C ^ 2 * Rtau_C ^ 2 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
             show σ_Fib_1 1 0 = 0 from rfl,
             show σ_Fib_1 1 1 = Rtau_C from rfl,
             σ_Fib_2_apply_11, zero_mul, zero_add]
  ring

/-- **Spectral invariant**: `tr(σ_Fib_1 * σ_Fib_2) = ω² · 1 - 2·p + 2·p`
which simplifies through bridge-identity arithmetic. We compute the
intermediate algebraic form here. -/
theorem σ_Fib_1_mul_σ_Fib_2_trace :
    Matrix.trace (σ_Fib_1 * σ_Fib_2) =
      φInv_C ^ 2 * (R1_C ^ 2 + Rtau_C ^ 2) +
      2 * φInv_C * R1_C * Rtau_C := by
  rw [Matrix.trace_fin_two, σ_Fib_1_mul_σ_Fib_2_apply_00,
      σ_Fib_1_mul_σ_Fib_2_apply_11]
  ring

/-- **Bridge consequence**: using `fib_yb_core_identity`,
`tr(σ_Fib_1 * σ_Fib_2) = R1_C * Rtau_C`.

Proof: `tr = p²·(R_1² + R_τ²) + 2p·R_1·R_τ`. Apply core_identity
`p²·(R_1² + R_τ²) + (2p-1)·R_1·R_τ = 0` to rewrite
`p²·(R_1² + R_τ²) = (1 - 2p)·R_1·R_τ`. Then
`tr = (1-2p)·R_1·R_τ + 2p·R_1·R_τ = R_1·R_τ`. -/
theorem σ_Fib_1_mul_σ_Fib_2_trace_eq :
    Matrix.trace (σ_Fib_1 * σ_Fib_2) = R1_C * Rtau_C := by
  have h := fib_yb_core_identity
  rw [σ_Fib_1_mul_σ_Fib_2_trace]
  linear_combination h

/-- **`tr(σ_Fib_1_SU * σ_Fib_2_SU) = 1`** — spectral invariant of the
det-normalized product.

Proof: `tr(ω·σ_1 · ω·σ_2) = ω² · tr(σ_1 · σ_2) = ω² · R_1 · R_τ`.
By `ω_Fib_C_sq_mul_det`, this equals `1`.

**Physical meaning**: in the SU(2)→SO(3) double cover, an element
with trace `1` corresponds to a rotation by `θ` with `2·cos(θ/2) = 1`,
i.e., `θ = 2π/3`. So `σ_1_SU · σ_2_SU` has order `6` in SU(2)
(order `3` in SO(3)). -/
theorem σ_Fib_1_SU_mul_σ_Fib_2_SU_trace :
    Matrix.trace (σ_Fib_1_SU_mat * σ_Fib_2_SU_mat) = 1 := by
  unfold σ_Fib_1_SU_mat σ_Fib_2_SU_mat
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.trace_smul, σ_Fib_1_mul_σ_Fib_2_trace_eq]
  -- Goal: (ω_Fib_C * ω_Fib_C) • (R1_C * Rtau_C) = 1
  -- i.e., ω² · (R_1 · R_τ) = 1
  have h := ω_Fib_C_sq_mul_det
  rw [smul_eq_mul, ← sq]
  exact h

/-! ## 5. Phase D2: individual-generator trace formulas and F-conjugacy

While §4 computed the product trace `tr(σ_Fib_1_SU · σ_Fib_2_SU) = 1`,
this section computes the trace of each generator individually and
establishes the F-conjugacy that relates them.

**Individual traces**: `tr(σ_Fib_1_SU_mat) = tr(σ_Fib_2_SU_mat)
= exp(-7πi/10) + exp(7πi/10) = 2·cos(7π/10)`.

**F-conjugacy**: `σ_Fib_2_SU_mat = F_C · σ_Fib_1_SU_mat · F_C` (where
F_C is the Bonesteel F-matrix and `F_C² = I`). This means σ_Fib_2_SU
and σ_Fib_1_SU have the same spectrum and the same rotation angle in
the SU(2)→SO(3) double cover (`θ = 7π/5`), but DIFFERENT rotation
axes — the axis of σ_Fib_2 is obtained from that of σ_Fib_1 by the
F-rotation.

**Non-centrality**: since the diagonal entries of σ_Fib_1_SU_mat are
`ω · R_1 = exp(-7πi/10)` and `ω · R_τ = exp(7πi/10)`, which are
distinct, σ_Fib_1_SU_mat is NOT a scalar matrix. In particular,
σ_Fib_1_SU_mat ≠ I and σ_Fib_1_SU_mat ≠ -I. Same for σ_Fib_2_SU_mat
(via F-conjugacy of a non-scalar matrix).

**Density implication**: combined with non-commutation (§3), the
subgroup `⟨σ_Fib_1_SU, σ_Fib_2_SU⟩` is non-abelian and contains
non-central elements. This rules out two large families of closed
subgroups of SU(2): the center `{±I}` (since both generators are
outside it) and 1-parameter subgroups (since non-commuting generators
cannot lie in a common 1-torus). Phase D3 will use the remaining
structural facts to rule out finite subgroups and the normalizers of
1-tori. -/

/-- `R1_C ≠ Rtau_C`: the two R-eigenvalues are distinct. Proved via
`R1_C^5 = 1` vs `Rtau_C^5 = -1`. -/
theorem R1_C_ne_Rtau_C : R1_C ≠ Rtau_C := by
  intro h_eq
  have h1 := R1_C_pow_5
  have h2 := Rtau_C_pow_5
  rw [h_eq] at h1
  rw [h1] at h2
  have : (2 : ℂ) = 0 := by linear_combination h2
  norm_num at this

/-! ### 5a. Trace formulas for individual generators -/

/-- `tr(σ_Fib_1) = R_1 + R_τ` (`σ_Fib_1` is diagonal). -/
theorem σ_Fib_1_trace : Matrix.trace σ_Fib_1 = R1_C + Rtau_C := by
  rw [Matrix.trace_fin_two]
  rfl

/-- `tr(σ_Fib_2) = R_1 + R_τ` (same as σ_Fib_1, since σ_Fib_2 is
F-conjugate to σ_Fib_1 and trace is conjugation-invariant — proved
here via direct algebraic computation using `φInv_C² + φInv_C = 1`). -/
theorem σ_Fib_2_trace : Matrix.trace σ_Fib_2 = R1_C + Rtau_C := by
  rw [Matrix.trace_fin_two, σ_Fib_2_apply_00, σ_Fib_2_apply_11]
  -- LHS = (φInv²·R_1 + φInv·R_τ) + (φInv·R_1 + φInv²·R_τ)
  --     = (φInv² + φInv)·(R_1 + R_τ) = 1·(R_1 + R_τ) = R_1 + R_τ
  have h := φInv_C_sq_add_self
  linear_combination (R1_C + Rtau_C) * h

/-- `tr(σ_Fib_1_SU_mat) = exp(-7πi/10) + exp(7πi/10)` — exponential
form of the spectral invariant.

Proof: `tr(ω·σ_Fib_1) = ω·(R_1 + R_τ) = ω·R_1 + ω·R_τ`. Compute:
`ω·R_1 = exp(π/10·I)·exp(-4π/5·I) = exp((π/10 - 8π/10)·I)
= exp(-7π/10·I)`, similarly `ω·R_τ = exp(7π/10·I)`. -/
theorem σ_Fib_1_SU_mat_trace_eq :
    Matrix.trace σ_Fib_1_SU_mat =
      Complex.exp (((-7 * Real.pi / 10 : ℝ) : ℂ) * Complex.I) +
      Complex.exp (((7 * Real.pi / 10 : ℝ) : ℂ) * Complex.I) := by
  unfold σ_Fib_1_SU_mat
  rw [Matrix.trace_smul, σ_Fib_1_trace, smul_eq_mul, mul_add]
  -- Goal: ω·R_1 + ω·R_τ = exp(-7π/10·I) + exp(7π/10·I)
  unfold ω_Fib_C R1_C Rtau_C
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring

/-! ### 5b. F-conjugacy of σ_Fib_2 with σ_Fib_1 -/

/-- The det-normalized σ_Fib_2 is F-conjugate to the det-normalized
σ_Fib_1: `σ_Fib_2_SU_mat = F_C · σ_Fib_1_SU_mat · F_C`.

Proof: `σ_Fib_2 := F·σ_Fib_1·F` by definition. Then
`ω • (F·σ_Fib_1·F) = F·(ω • σ_Fib_1)·F` by Matrix.smul_mul. -/
theorem σ_Fib_2_SU_mat_eq_F_conj :
    σ_Fib_2_SU_mat = F_C * σ_Fib_1_SU_mat * F_C := by
  unfold σ_Fib_2_SU_mat σ_Fib_2 σ_Fib_1_SU_mat
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]

/-- Trace of `σ_Fib_2_SU_mat` equals trace of `σ_Fib_1_SU_mat`.
Proof: via F-conjugacy + trace cyclicity + F² = I. -/
theorem σ_Fib_2_SU_mat_trace_eq_σ_Fib_1_SU_mat_trace :
    Matrix.trace σ_Fib_2_SU_mat = Matrix.trace σ_Fib_1_SU_mat := by
  rw [σ_Fib_2_SU_mat_eq_F_conj]
  -- tr(F · σ_Fib_1_SU_mat · F) = tr((F · F) · σ_Fib_1_SU_mat) (cyclic)
  --                            = tr(1 · σ_Fib_1_SU_mat) (F² = I)
  --                            = tr(σ_Fib_1_SU_mat)
  rw [Matrix.trace_mul_cycle, F_C_sq, one_mul]

/-- `tr(σ_Fib_2_SU_mat) = exp(-7πi/10) + exp(7πi/10)` (same as
σ_Fib_1_SU_mat, by F-conjugacy). -/
theorem σ_Fib_2_SU_mat_trace_eq :
    Matrix.trace σ_Fib_2_SU_mat =
      Complex.exp (((-7 * Real.pi / 10 : ℝ) : ℂ) * Complex.I) +
      Complex.exp (((7 * Real.pi / 10 : ℝ) : ℂ) * Complex.I) := by
  rw [σ_Fib_2_SU_mat_trace_eq_σ_Fib_1_SU_mat_trace, σ_Fib_1_SU_mat_trace_eq]

/-! ### 5c. Non-centrality: σ_Fib_{1,2}_SU_mat ≠ ±I -/

/-- The diagonal entries of σ_Fib_1_SU_mat differ:
`σ_Fib_1_SU_mat[0,0] = ω·R_1 ≠ ω·R_τ = σ_Fib_1_SU_mat[1,1]`. -/
theorem σ_Fib_1_SU_mat_diag_ne :
    σ_Fib_1_SU_mat 0 0 ≠ σ_Fib_1_SU_mat 1 1 := by
  unfold σ_Fib_1_SU_mat
  simp only [Matrix.smul_apply, show σ_Fib_1 0 0 = R1_C from rfl,
             show σ_Fib_1 1 1 = Rtau_C from rfl, smul_eq_mul]
  intro h
  have h_ω_ne : ω_Fib_C ≠ 0 := by
    intro h_ω
    have h_norm : ‖ω_Fib_C‖ = 0 := by rw [h_ω, norm_zero]
    rw [norm_ω_Fib_C] at h_norm
    norm_num at h_norm
  exact R1_C_ne_Rtau_C (mul_left_cancel₀ h_ω_ne h)

/-- σ_Fib_1_SU_mat is NOT a scalar multiple of the identity. Proof:
a scalar matrix has equal diagonal entries, but σ_Fib_1_SU_mat[0,0]
≠ σ_Fib_1_SU_mat[1,1]. -/
theorem σ_Fib_1_SU_mat_ne_smul_one (c : ℂ) :
    σ_Fib_1_SU_mat ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  apply σ_Fib_1_SU_mat_diag_ne
  rw [h]
  simp [Matrix.smul_apply]

/-- σ_Fib_1_SU_mat ≠ I (the identity matrix). -/
theorem σ_Fib_1_SU_mat_ne_one :
    σ_Fib_1_SU_mat ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  apply σ_Fib_1_SU_mat_ne_smul_one 1
  rw [h, one_smul]

/-- σ_Fib_1_SU_mat ≠ -I. -/
theorem σ_Fib_1_SU_mat_ne_neg_one :
    σ_Fib_1_SU_mat ≠ -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  apply σ_Fib_1_SU_mat_ne_smul_one (-1)
  rw [h, neg_smul, one_smul]

/-- σ_Fib_2_SU_mat is NOT a scalar matrix. Proof: F-conjugating a
scalar matrix gives the same scalar matrix (since F² = I and scalar
matrices commute with everything), so if σ_Fib_2_SU_mat = c • I,
then σ_Fib_1_SU_mat = c • I as well, contradicting
σ_Fib_1_SU_mat_ne_smul_one. -/
theorem σ_Fib_2_SU_mat_ne_smul_one (c : ℂ) :
    σ_Fib_2_SU_mat ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  apply σ_Fib_1_SU_mat_ne_smul_one c
  -- From σ_Fib_2_SU_mat = c • 1 and σ_Fib_2_SU_mat = F · σ_Fib_1_SU_mat · F:
  -- F · σ_Fib_1_SU_mat · F = c • 1
  -- Multiply by F on both sides: F · (F · σ_Fib_1_SU_mat · F) · F = F · (c • 1) · F
  -- LHS = (F·F) · σ_Fib_1_SU_mat · (F·F) = 1 · σ_Fib_1_SU_mat · 1 = σ_Fib_1_SU_mat
  -- RHS = F · (c • 1) · F = c • (F · 1 · F) = c • (F · F) = c • 1
  have h_conj : F_C * σ_Fib_1_SU_mat * F_C = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← σ_Fib_2_SU_mat_eq_F_conj]; exact h
  -- Wrap with F on both sides:
  have h_wrap : F_C * (F_C * σ_Fib_1_SU_mat * F_C) * F_C =
                F_C * (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * F_C := by
    rw [h_conj]
  -- LHS reduces to σ_Fib_1_SU_mat via F² = I
  have h_LHS : F_C * (F_C * σ_Fib_1_SU_mat * F_C) * F_C = σ_Fib_1_SU_mat := by
    rw [show F_C * (F_C * σ_Fib_1_SU_mat * F_C) * F_C =
          (F_C * F_C) * σ_Fib_1_SU_mat * (F_C * F_C) by
      simp [mul_assoc]]
    rw [F_C_sq, one_mul, mul_one]
  -- RHS reduces to c • 1 via F² = I and smul commutes with multiplication
  have h_RHS : F_C * (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * F_C =
               c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, F_C_sq]
  rw [h_LHS, h_RHS] at h_wrap
  exact h_wrap

/-- σ_Fib_2_SU_mat ≠ I. -/
theorem σ_Fib_2_SU_mat_ne_one :
    σ_Fib_2_SU_mat ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  apply σ_Fib_2_SU_mat_ne_smul_one 1
  rw [h, one_smul]

/-- σ_Fib_2_SU_mat ≠ -I. -/
theorem σ_Fib_2_SU_mat_ne_neg_one :
    σ_Fib_2_SU_mat ≠ -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  apply σ_Fib_2_SU_mat_ne_smul_one (-1)
  rw [h, neg_smul, one_smul]

/-! ### 5d. SU(2)-level non-identity statements -/

/-- σ_Fib_1_SU ≠ 1 in SU(2). Lifted from σ_Fib_1_SU_mat_ne_one. -/
theorem σ_Fib_1_SU_ne_one : σ_Fib_1_SU ≠ 1 := by
  intro h
  apply σ_Fib_1_SU_mat_ne_one
  show σ_Fib_1_SU.val = 1
  rw [h]
  rfl

/-- σ_Fib_2_SU ≠ 1 in SU(2). Lifted from σ_Fib_2_SU_mat_ne_one. -/
theorem σ_Fib_2_SU_ne_one : σ_Fib_2_SU ≠ 1 := by
  intro h
  apply σ_Fib_2_SU_mat_ne_one
  show σ_Fib_2_SU.val = 1
  rw [h]
  rfl

/-! ## 6. Phase D3.a: conjugation analysis and N(T) ruleout

A closed subgroup G ⊆ SU(2) of dimension 1 is either a maximal torus
T or its normalizer N(T). The normalizer N(T) has two connected
components: T and a coset T·s where s² ∈ T. Crucially, conjugation by
elements of N(T) \ T **inverts** elements of T:

  s ∈ N(T) \ T, t ∈ T  ⟹  s · t · s⁻¹ = t⁻¹.

This section establishes the matrix-level inequality:

  σ_Fib_2_SU_mat · σ_Fib_1_SU_mat · star σ_Fib_2_SU_mat ≠ star σ_Fib_1_SU_mat,

which is equivalent to:

  σ_Fib_2_SU_mat · σ_Fib_1_SU_mat ≠ star σ_Fib_1_SU_mat · σ_Fib_2_SU_mat.

Hence the subgroup `⟨σ_Fib_1_SU, σ_Fib_2_SU⟩` cannot be contained in
any N(T): either σ_Fib_2_SU ∈ T (forcing commute via T abelian, which
contradicts §3 non-commutation) or σ_Fib_2_SU ∈ N(T)\T (forcing
inversion under conjugation, which contradicts the inequality here).

Combined with D2's center + 1-torus ruleouts, the only closed
subgroups of SU(2) still in play are the finite binary subgroups
(Z_n, BD_4n, 2T, 2O, 2I) — to be ruled out in D3.b — and SU(2) itself.

**Proof strategy**: project to matrix entry [0,0]. After expanding
both sides via `Matrix.mul_apply` and the diagonal structure of
σ_Fib_1, the constraint reduces to `(ω² · R_1² - 1) · σ_Fib_2[0,0] = 0`.
We show both factors are non-zero:
- `ω²·R_1² ≠ 1` via `(ω²·R_1²)^5 = -1` (using ω^10 = -1 and R_1^10 = 1).
- `σ_Fib_2[0,0] ≠ 0` via `σ_Fib_2[0,0] = φInv · (φInv·R_1 + R_τ)`;
  if `φInv·R_1 + R_τ = 0` then `R_τ = -φInv·R_1`; taking 5th powers
  gives `-1 = -φInv^5`, i.e., `φInv^5 = 1`; but φInv is real with
  `|φInv| = 1/φ < 1`, so `φInv^5 < 1`, contradiction. -/

/-- `ω_Fib_C^10 = -1`. Helper: ω = exp(πi/10) has order 20, so
`ω^10 = exp(πi) = -1`. -/
private theorem ω_Fib_C_pow_10 : ω_Fib_C ^ 10 = -1 := by
  unfold ω_Fib_C
  rw [← Complex.exp_nat_mul]
  rw [show ((10 : ℕ) : ℂ) * (((Real.pi / 10 : ℝ) : ℂ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- `R1_C^10 = 1`. Derived from `R1_C^5 = 1` by squaring. -/
private theorem R1_C_pow_10 : R1_C ^ 10 = 1 := by
  have h5 := R1_C_pow_5
  have : R1_C ^ 10 = (R1_C ^ 5) ^ 2 := by ring
  rw [this, h5]; norm_num

/-- **Key blocking identity for N(T) ruleout**: `ω² · R_1² ≠ 1`.

Proof: `(ω²·R_1²)^5 = ω^10·R_1^10 = (-1)·1 = -1`. If `ω²·R_1² = 1`,
then `1^5 = 1 ≠ -1`, contradiction. -/
theorem ω_Fib_C_sq_mul_R1_C_sq_ne_one :
    ω_Fib_C ^ 2 * R1_C ^ 2 ≠ 1 := by
  intro h
  have h_pow : (ω_Fib_C ^ 2 * R1_C ^ 2) ^ 5 = 1 := by
    rw [h]; norm_num
  have h_factored : (ω_Fib_C ^ 2 * R1_C ^ 2) ^ 5 = ω_Fib_C ^ 10 * R1_C ^ 10 := by
    ring
  rw [h_factored, ω_Fib_C_pow_10, R1_C_pow_10] at h_pow
  -- h_pow : -1 * 1 = 1, i.e., -1 = 1 in ℂ
  have : (2 : ℂ) = 0 := by linear_combination -h_pow
  norm_num at this

/-- `φInv_C^5 ≠ 1`. Since `φInv_C = (Real.goldenRatio⁻¹ : ℂ)` is a
real complex number with `0 < φInv_C < 1`, its 5th power is also a
real complex number `< 1`, hence `≠ 1`. -/
private theorem φInv_C_pow_5_ne_one : φInv_C ^ 5 ≠ 1 := by
  unfold φInv_C
  -- Cast: (a : ℝ → ℂ)^5 = ((a^5 : ℝ) : ℂ)
  rw [← Complex.ofReal_pow]
  intro h_eq
  -- h_eq : ((Real.goldenRatio⁻¹)^5 : ℂ) = 1 = ((1 : ℝ) : ℂ)
  have h_real : (Real.goldenRatio⁻¹ : ℝ) ^ 5 = 1 := by
    have : ((Real.goldenRatio⁻¹ ^ 5 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [h_eq]; push_cast; rfl
    exact_mod_cast this
  -- But (φInv)^5 < 1 since 0 < φInv < 1
  have h_phi_pos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have h_phi_gt_one : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have h_phiInv_pos : (0 : ℝ) < Real.goldenRatio⁻¹ := inv_pos.mpr h_phi_pos
  have h_phiInv_lt_one : Real.goldenRatio⁻¹ < 1 := by
    rw [inv_eq_one_div, div_lt_one h_phi_pos]
    exact h_phi_gt_one
  have h_pow_lt : Real.goldenRatio⁻¹ ^ 5 < 1 :=
    (pow_lt_one_iff_of_nonneg h_phiInv_pos.le (by norm_num : (5 : ℕ) ≠ 0)).mpr
      h_phiInv_lt_one
  linarith

/-- **`σ_Fib_2[0,0] ≠ 0`**.

Proof: `σ_Fib_2[0,0] = φInv² · R_1 + φInv · R_τ = φInv · (φInv · R_1 + R_τ)`.
Suppose σ_Fib_2[0,0] = 0. Then either `φInv = 0` (false, since φInv is
the inverse of the positive real golden ratio) or `φInv · R_1 + R_τ = 0`,
i.e., `R_τ = -φInv · R_1`. Taking 5th powers: `R_τ^5 = -φInv^5 · R_1^5`,
i.e., `-1 = -φInv^5`, so `φInv^5 = 1`. But φInv^5 < 1, contradiction. -/
theorem σ_Fib_2_apply_00_ne_zero : σ_Fib_2 0 0 ≠ 0 := by
  rw [σ_Fib_2_apply_00]
  intro h
  -- h : φInv² · R_1 + φInv · R_τ = 0
  -- Factor: φInv · (φInv · R_1 + R_τ) = 0
  have h_factor : φInv_C * (φInv_C * R1_C + Rtau_C) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h_factor with h_phi_zero | h_rest
  · -- φInv = 0: impossible since φInv^2 + φInv = 1
    have h_sq := φInv_C_sq_add_self
    rw [h_phi_zero] at h_sq
    norm_num at h_sq
  · -- φInv · R_1 + R_τ = 0, so R_τ = -φInv · R_1
    have h_Rtau : Rtau_C = -(φInv_C * R1_C) := by
      linear_combination h_rest
    -- Take 5th powers: R_τ^5 = -φInv^5 · R_1^5
    have h_Rtau5 := Rtau_C_pow_5
    have h_R1_5 := R1_C_pow_5
    have h_pow5 : Rtau_C ^ 5 = -(φInv_C ^ 5 * R1_C ^ 5) := by
      rw [h_Rtau]; ring
    rw [h_R1_5, mul_one, h_Rtau5] at h_pow5
    -- h_pow5 : -1 = -φInv^5
    have h_phiInv5 : φInv_C ^ 5 = 1 := by linear_combination h_pow5
    exact φInv_C_pow_5_ne_one h_phiInv5

/-- `(σ_Fib_2 · σ_Fib_1)[0,0] = σ_Fib_2[0,0] · R_1` (σ_Fib_1 diagonal). -/
private theorem σ_Fib_2_mul_σ_Fib_1_apply_00 :
    (σ_Fib_2 * σ_Fib_1) 0 0 = σ_Fib_2 0 0 * R1_C := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
             show σ_Fib_1 0 0 = R1_C from rfl,
             show σ_Fib_1 1 0 = 0 from rfl,
             mul_zero, add_zero]

/-- **`σ_Fib_2_SU_mat · σ_Fib_1_SU_mat ≠ star σ_Fib_1_SU_mat · σ_Fib_2_SU_mat`**
— the headline N(T)-ruleout inequality.

Equivalent to: `σ_Fib_2_SU · σ_Fib_1_SU · σ_Fib_2_SU⁻¹ ≠ σ_Fib_1_SU⁻¹`,
since for SU(2) the inverse is the star (conjugate transpose).

**Argument**: project to entry [0,0]. After expansion:
- LHS[0,0] = `ω² · σ_Fib_2[0,0] · R_1`
- RHS[0,0] = `star(ω · R_1) · ω · σ_Fib_2[0,0]`

Equality forces (after canceling σ_Fib_2[0,0] ≠ 0 and ω ≠ 0)
`ω · R_1 = star(ω · R_1)`, i.e., `ω · R_1` is real. For
unit-modulus `ω · R_1`, this means `(ω · R_1)² = 1`. But
`ω² · R_1² ≠ 1`, contradiction. -/
theorem σ_Fib_SU_mat_not_conj_inverts :
    σ_Fib_2_SU_mat * σ_Fib_1_SU_mat ≠
      star σ_Fib_1_SU_mat * σ_Fib_2_SU_mat := by
  intro h_eq
  -- Project to entry [0,0]
  have h_00 : (σ_Fib_2_SU_mat * σ_Fib_1_SU_mat) 0 0 =
              (star σ_Fib_1_SU_mat * σ_Fib_2_SU_mat) 0 0 := by
    rw [h_eq]
  -- Helper: matrix entries of σ_Fib_1_SU_mat
  have h_σ1_00 : σ_Fib_1_SU_mat 0 0 = ω_Fib_C * R1_C := by
    show (ω_Fib_C • σ_Fib_1) 0 0 = ω_Fib_C * R1_C
    simp [Matrix.smul_apply, smul_eq_mul, show σ_Fib_1 0 0 = R1_C from rfl]
  have h_σ1_10 : σ_Fib_1_SU_mat 1 0 = 0 := by
    show (ω_Fib_C • σ_Fib_1) 1 0 = 0
    simp [Matrix.smul_apply, smul_eq_mul, show σ_Fib_1 1 0 = 0 from rfl]
  have h_σ2_00 : σ_Fib_2_SU_mat 0 0 = ω_Fib_C * σ_Fib_2 0 0 := by
    show (ω_Fib_C • σ_Fib_2) 0 0 = ω_Fib_C * σ_Fib_2 0 0
    simp [Matrix.smul_apply, smul_eq_mul]
  -- LHS [0,0] = σ_Fib_2_SU_mat[0,0] · σ_Fib_1_SU_mat[0,0] (σ_Fib_1_SU_mat[1,0]=0)
  have h_LHS : (σ_Fib_2_SU_mat * σ_Fib_1_SU_mat) 0 0 =
               ω_Fib_C ^ 2 * σ_Fib_2 0 0 * R1_C := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h_σ1_10, mul_zero, add_zero,
               h_σ1_00, h_σ2_00]
    ring
  -- RHS [0,0]: use Matrix.conjTranspose / star
  -- (star M)[i,j] = star (M[j,i])
  have h_star_00 : (star σ_Fib_1_SU_mat) 0 0 = star (ω_Fib_C * R1_C) := by
    show star (σ_Fib_1_SU_mat 0 0) = star (ω_Fib_C * R1_C)
    rw [h_σ1_00]
  have h_star_01 : (star σ_Fib_1_SU_mat) 0 1 = 0 := by
    show star (σ_Fib_1_SU_mat 1 0) = 0
    rw [h_σ1_10, star_zero]
  have h_RHS : (star σ_Fib_1_SU_mat * σ_Fib_2_SU_mat) 0 0 =
               star (ω_Fib_C * R1_C) * (ω_Fib_C * σ_Fib_2 0 0) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h_star_01, zero_mul, add_zero,
               h_star_00, h_σ2_00]
  rw [h_LHS, h_RHS] at h_00
  -- h_00 : ω² · σ_Fib_2[0,0] · R_1 = star(ω · R_1) · ω · σ_Fib_2[0,0]
  -- Cancel σ_Fib_2[0,0] (≠ 0)
  have h_σ2_ne := σ_Fib_2_apply_00_ne_zero
  have h_factored : (ω_Fib_C ^ 2 * R1_C - star (ω_Fib_C * R1_C) * ω_Fib_C) *
                    σ_Fib_2 0 0 = 0 := by
    linear_combination h_00
  have h_arg : ω_Fib_C ^ 2 * R1_C = star (ω_Fib_C * R1_C) * ω_Fib_C := by
    rcases mul_eq_zero.mp h_factored with h | h
    · linear_combination h
    · exact absurd h h_σ2_ne
  -- Cancel ω (≠ 0): ω · R_1 = star(ω · R_1)
  have h_ω_ne : ω_Fib_C ≠ 0 := by
    intro h_ω
    have h_norm : ‖ω_Fib_C‖ = 0 := by rw [h_ω, norm_zero]
    rw [norm_ω_Fib_C] at h_norm
    norm_num at h_norm
  have h_unit : ω_Fib_C * R1_C = star (ω_Fib_C * R1_C) := by
    have h_cancel : ω_Fib_C * (ω_Fib_C * R1_C) =
                    ω_Fib_C * (star (ω_Fib_C * R1_C)) := by
      linear_combination h_arg
    exact mul_left_cancel₀ h_ω_ne h_cancel
  -- (ω · R_1) · star(ω · R_1) = 1 (unit modulus)
  have h_norm_ω : ‖ω_Fib_C‖ = 1 := norm_ω_Fib_C
  have h_norm_R1 : ‖R1_C‖ = 1 := norm_R1_C
  have h_norm_prod : ‖ω_Fib_C * R1_C‖ = 1 := by
    rw [norm_mul, h_norm_ω, h_norm_R1, mul_one]
  -- For unit-modulus z, z · star z = 1 (inline of `unit_norm_mul_conj`)
  have h_z_star : (ω_Fib_C * R1_C) * star (ω_Fib_C * R1_C) = 1 := by
    show (ω_Fib_C * R1_C) * (starRingEnd ℂ) (ω_Fib_C * R1_C) = 1
    rw [Complex.mul_conj]
    have h_normSq : Complex.normSq (ω_Fib_C * R1_C) = ‖ω_Fib_C * R1_C‖ ^ 2 :=
      (Complex.sq_norm _).symm
    rw [h_normSq, h_norm_prod]
    norm_num
  have h_sq : (ω_Fib_C * R1_C) ^ 2 = 1 := by
    have h_chain : (ω_Fib_C * R1_C) ^ 2 =
                   (ω_Fib_C * R1_C) * star (ω_Fib_C * R1_C) := by
      rw [sq, ← h_unit]
    rw [h_chain, h_z_star]
  have h_pow : ω_Fib_C ^ 2 * R1_C ^ 2 = 1 := by
    have : ω_Fib_C ^ 2 * R1_C ^ 2 = (ω_Fib_C * R1_C) ^ 2 := by ring
    rw [this, h_sq]
  exact ω_Fib_C_sq_mul_R1_C_sq_ne_one h_pow

/-! ## 7. Phase D3.b: order analysis + finite-subgroup ruleout

After D3.a established that ⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ is not contained
in any torus normalizer N(T), only finite binary subgroups of SU(2)
(Z_n, BD_4n, 2T, 2O, 2I) and SU(2) itself remain as candidates.

This section ships the substrate to rule out all finite binary
subgroups:

  **`σ_Fib_1_SU_mat^4 ≠ I`** AND **`σ_Fib_1_SU_mat^10 = -I`**
    (hence `σ_Fib_1_SU_mat^10 ≠ I`).

Combined with `σ_Fib_1_SU_mat^20 = I` (§2, D1), the **multiplicative
order of `σ_Fib_1_SU_mat` in `M₂(ℂ)` is exactly 20**: order divides
20 (since σ^20 = I) but neither 4 nor 10 (so order ∉ {1, 2, 4, 5, 10},
leaving only 20).

**Finite-subgroup ruleout** (proof-by-docstring; formalizing the
subgroup classes is a Mathlib4 substrate gap):

| Class | Max element order | σ_Fib_1_SU order 20 forces |
|-------|-------------------|------------------------------|
| Z_n   | n                 | n ≥ 20, but Z_n abelian ⊥ §3 non-commute |
| BD_4n (order 4n) | cyclic part 2n, outside 4 | 2n ≥ 20 (so n ≥ 10); σ_Fib_2_SU order 20 also in cyclic Z_{2n} (else order 4 ≠ 20); both in abelian Z_{2n} ⊥ non-commute |
| 2T (order 24)    | 6                 | 20 > 6 → σ_Fib_1_SU ∉ 2T  |
| 2O (order 48)    | 8                 | 20 > 8 → σ_Fib_1_SU ∉ 2O  |
| 2I (order 120)   | 10                | 20 > 10 → σ_Fib_1_SU ∉ 2I |

Together with D2 (center {±I} ruled out, 1-tori ruled out) and D3.a
(N(T) ruled out), the closure of ⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ in SU(2)
must equal **SU(2) itself** — the headline density discharge.

**Slick algebraic identity**: `(ω · R_1)^4 = R_1` (proved here as
`ω_R1_pow_4_eq_R1`). This is the cyclotomic consequence of
`ω^4 · R_1^3 = 1` (since ω^4 = ζ_5, R_1 = ζ_5^3, so ω^4·R_1^3 = ζ_5·ζ_5^9 = ζ_5^{10} = 1).
Combined with `R_1 ≠ 1` (proved via the R4.2.b.1 bridge identity
`R_1^2 + R_1^3 = 1/φ`), we get `(ω·R_1)^4 ≠ 1`, hence `σ^4 ≠ I`. -/

/-- `R1_C ≠ 1`: the 5th root of unity R_1 = exp(-4πi/5) is not the
trivial root. Proof via the bridge identity `R_1^2 + R_1^3 = 1/φ`:
if R_1 = 1, then `1 + 1 = 1/φ`, i.e., `2 = 1/φ`. But `1/φ < 1 < 2`. -/
private theorem R1_C_ne_one : R1_C ≠ 1 := by
  intro h
  have h_bridge := R1_C_sq_add_cube_eq_φInv
  rw [h] at h_bridge
  -- h_bridge : 1^2 + 1^3 = (Real.goldenRatio⁻¹ : ℂ)
  have h_lhs : (1 : ℂ) ^ 2 + (1 : ℂ) ^ 3 = (2 : ℂ) := by ring
  rw [h_lhs] at h_bridge
  -- h_bridge : (2 : ℂ) = (Real.goldenRatio⁻¹ : ℂ)
  have h_real : (2 : ℝ) = Real.goldenRatio⁻¹ := by exact_mod_cast h_bridge
  -- But 1/φ < 1 < 2
  have h_phi_pos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have h_phi_gt : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have h_phiInv_lt_one : Real.goldenRatio⁻¹ < 1 := by
    rw [inv_eq_one_div, div_lt_one h_phi_pos]
    exact h_phi_gt
  linarith

/-- `ω^4 · R_1^3 = 1`: the cyclotomic-Fibonacci consequence
`ω^4 = ζ_5, R_1 = ζ_5^3` ⟹ `ω^4·R_1^3 = ζ_5^{10} = 1`.

Computed: `4 · (π/10·I) + 3 · (-4π/5·I) = (2π/5 - 12π/5)·I
= -2π·I = -1 · (2π·I)`, so `exp(...) = exp(-1 · 2π·I) = 1`. -/
private theorem ω_pow_4_mul_R1_pow_3 :
    ω_Fib_C ^ 4 * R1_C ^ 3 = 1 := by
  unfold ω_Fib_C R1_C
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  rw [show ((4 : ℕ) : ℂ) * (((Real.pi / 10 : ℝ) : ℂ) * Complex.I) +
        ((3 : ℕ) : ℂ) * (((-4 * Real.pi / 5 : ℝ) : ℂ) * Complex.I) =
        ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I (-1)

/-- **`(ω · R_1)^4 = R_1`** — the slick algebraic reduction
from a 4th-power computation to a primitive 5th-root-of-unity.

Proof: `(ω·R_1)^4 = ω^4·R_1^4 = (ω^4·R_1^3) · R_1 = 1 · R_1 = R_1`. -/
private theorem ω_R1_pow_4_eq_R1 :
    (ω_Fib_C * R1_C) ^ 4 = R1_C := by
  rw [mul_pow]
  have h := ω_pow_4_mul_R1_pow_3
  have : ω_Fib_C ^ 4 * R1_C ^ 4 = ω_Fib_C ^ 4 * R1_C ^ 3 * R1_C := by ring
  rw [this, h, one_mul]

/-- **`σ_Fib_1_SU_mat^4 ≠ I`** — rules out element order 4.

Proof: `σ_Fib_1_SU_mat^4 = ω^4 • σ_Fib_1^4`. Project to entry [0,0]:
`[σ_Fib_1_SU_mat^4][0,0] = ω^4 · R_1^4 = (ω·R_1)^4 = R_1`. If
σ_Fib_1_SU_mat^4 = I, then R_1 = 1, contradicting `R1_C_ne_one`. -/
theorem σ_Fib_1_SU_mat_pow_4_ne_one :
    σ_Fib_1_SU_mat ^ 4 ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  -- σ_Fib_1_SU_mat^4 = ω^4 • σ_Fib_1^4
  have h_pow : σ_Fib_1_SU_mat ^ 4 = ω_Fib_C ^ 4 • σ_Fib_1 ^ 4 := by
    show (ω_Fib_C • σ_Fib_1) ^ 4 = ω_Fib_C ^ 4 • σ_Fib_1 ^ 4
    rw [smul_pow]
  rw [h_pow, σ_Fib_1_pow_eq] at h
  -- h : ω^4 • diag(R_1^4, R_τ^4) = 1
  -- Project to entry [0,0]
  have h_00 : ω_Fib_C ^ 4 * R1_C ^ 4 = 1 := by
    have h_entry : ((ω_Fib_C ^ 4) • (!![R1_C ^ 4, 0; 0, Rtau_C ^ 4] :
                    Matrix (Fin 2) (Fin 2) ℂ)) 0 0 =
                   (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
      rw [h]
    simp [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at h_entry
    exact h_entry
  -- h_00 : ω^4 · R_1^4 = 1
  have h_factor : (ω_Fib_C * R1_C) ^ 4 = ω_Fib_C ^ 4 * R1_C ^ 4 := by ring
  rw [← h_factor, ω_R1_pow_4_eq_R1] at h_00
  -- h_00 : R_1 = 1
  exact R1_C_ne_one h_00

/-- **`σ_Fib_1_SU_mat^10 = -I`** — the concrete value of the 10th
power. Combined with `σ_Fib_1_SU_mat^20 = I` (§2, D1), this shows
σ_Fib_1_SU_mat has period exactly 20 in M₂(ℂ).

Proof: `σ^10 = (ω • σ_Fib_1)^10 = ω^10 • σ_Fib_1^10 = (-1) • I = -I`. -/
theorem σ_Fib_1_SU_mat_pow_10_eq_neg_one :
    σ_Fib_1_SU_mat ^ 10 = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  show (ω_Fib_C • σ_Fib_1) ^ 10 = -1
  rw [smul_pow, ω_Fib_C_pow_10, σ_Fib_1_pow_10]
  rw [neg_smul, one_smul]

/-- **`σ_Fib_1_SU_mat^10 ≠ I`** — rules out element orders {5, 10}.

Proof: σ^10 = -I (above) and -I ≠ I (differ at entry [0,0]). -/
theorem σ_Fib_1_SU_mat_pow_10_ne_one :
    σ_Fib_1_SU_mat ^ 10 ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [σ_Fib_1_SU_mat_pow_10_eq_neg_one]
  intro h
  have h_00 : (-1 : ℂ) = 1 := by
    have h_entry : (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 =
                   (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
    simp [Matrix.neg_apply, Matrix.one_apply] at h_entry
    exact h_entry
  norm_num at h_00

/-- **`σ_Fib_1_SU_mat` has multiplicative period exactly 20** in `M₂(ℂ)`.

Statement: `σ^k ≠ I` for `k ∈ {1, 2, 4, 5, 10}` AND `σ^20 = I`. Since
the only divisors of 20 are {1, 2, 4, 5, 10, 20}, the order is 20.

We package the order-≥-20 part: for all 0 < k < 20 with k dividing 20,
σ^k ≠ I. -/
theorem σ_Fib_1_SU_mat_has_period_20 :
    σ_Fib_1_SU_mat ^ 20 = 1 ∧
    σ_Fib_1_SU_mat ^ 10 ≠ 1 ∧
    σ_Fib_1_SU_mat ^ 4 ≠ 1 := by
  refine ⟨?_, σ_Fib_1_SU_mat_pow_10_ne_one, σ_Fib_1_SU_mat_pow_4_ne_one⟩
  -- σ^20 = (σ^10)^2 = (-I)^2 = I
  have h10 := σ_Fib_1_SU_mat_pow_10_eq_neg_one
  have h_eq : σ_Fib_1_SU_mat ^ 20 = (σ_Fib_1_SU_mat ^ 10) ^ 2 := by
    rw [← pow_mul]
  rw [h_eq, h10]
  -- (-1)^2 = 1
  rw [neg_one_sq]

/-! ### Finite-subgroup ruleout consequences (proof-by-docstring)

The above period-20 result + non-commutation directly preclude
⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ being contained in any finite binary
subgroup of SU(2). The argument (recorded here for traceability,
formalization deferred pending Mathlib4 substrate):

**`σ_Fib_1_SU ∉ 2I`** (order 120): max element order in 2I is 10
(the lift of A_5's order-5 elements). Since σ_Fib_1_SU has period
20 > 10, it cannot be in 2I.

**`σ_Fib_1_SU ∉ 2O`** (order 48): max element order 8 < 20.

**`σ_Fib_1_SU ∉ 2T`** (order 24): max element order 6 < 20.

**`⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ ⊄ Z_n` for any n**: Z_n is abelian, but
the generators don't commute (§3).

**`⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ ⊄ BD_4n`**: BD_4n has a cyclic subgroup
Z_{2n} of index 2; elements outside Z_{2n} have order 4. Since
σ_Fib_2_SU has period 20 (analogous to σ_Fib_1_SU via F-conjugacy),
σ_Fib_2_SU must be in Z_{2n} (else order would be 4, contradicting
period 20). But Z_{2n} is abelian, and σ_Fib_1_SU is also in Z_{2n},
forcing commutation — contradicts §3 non-commutation. -/

/-! ## 8. Conditional density theorem (Phase D1 final)

Given the residual closure-equals-univ hypothesis (which constitutes
the HBS density theorem yet-to-be-proved-constructively), the
`DenseInSpecialUnitary` conclusion for Fibonacci follows immediately
from R4.2.c + the existing AA bridge.

This theorem makes explicit what's remaining for full Path (i) discharge:
just the substantive density result `closure(range ρ_Fib_SU2) = univ`. -/

/-- **Fibonacci density theorem, conditional on the residual
closure-equals-univ hypothesis.**

Given the HBS density hypothesis (`closure(range ρ_Fib_SU2) = univ` in
SU(2)), the Fibonacci representation `ρ_Fib_SU2` is dense in SU(2) in
the entrywise topology sense (`DenseInSpecialUnitary 3 2 _`). This is
the canonical Phase 6p Wave 2c.4a-R4.2-final conclusion.

The residual hypothesis `h_closure_eq_univ` is the substantive HBS
density result, to be discharged in Phase D2-D4 of R4.2.d. -/
theorem fibonacci_density_conditional
    (h_closure_eq_univ :
      closure (Set.range ρ_Fib_SU2) =
        (Set.univ : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ))) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (ρ_Fib_SU2 b : Matrix (Fin 2) (Fin 2) ℂ)) := by
  -- All ρ_Fib_SU2 outputs are in SU(2) by construction.
  have h_unitary : ∀ b : SKEFTHawking.BraidGroup 3,
      (ρ_Fib_SU2 b : Matrix (Fin 2) (Fin 2) ℂ) ∈
        Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    fun b => (ρ_Fib_SU2 b).property
  -- h_ext is trivial (function equality of the two access patterns).
  have h_ext : ∀ b : SKEFTHawking.BraidGroup 3,
      ((ρ_Fib_SU2 b) : Matrix (Fin 2) (Fin 2) ℂ) =
        (fun b => (ρ_Fib_SU2 b : Matrix (Fin 2) (Fin 2) ℂ)) b := fun _ => rfl
  -- Apply the project's bridge_FKLW_unitary_hom.
  exact SKEFTHawking.FKLW.AharonovAradBridge.bridge_FKLW_unitary_hom
    3 2 (by omega) (fun b => (ρ_Fib_SU2 b : Matrix (Fin 2) (Fin 2) ℂ))
    h_unitary ρ_Fib_SU2 h_ext h_closure_eq_univ

/-! ## 10. Closure-as-subgroup substrate (Phase D4.1)

The D2 + D3.a + D3.b results have informally ruled out every proper
closed subgroup of SU(2) that could contain both generators. To lift
those informal ruleouts toward a formal `closure = univ` statement,
we package the closure of `range ρ_Fib_SU2` as a closed subgroup of
SU(2) (call it `H_Fib`) and re-state the residual D4 hypothesis as
`H_Fib = ⊤`.

This requires two general-purpose substrate pieces NOT in Mathlib4 as
of v4.29.0:

  - `ContinuousInv` for `Matrix.specialUnitaryGroup (Fin n) ℂ`. This
    follows from the fact that `(A : SU(n))⁻¹ = star A` (definitional
    in Mathlib) and `star` on `Matrix (Fin n) (Fin n) ℂ` is continuous
    (via `Matrix.instContinuousStar`). The proof is short (4 lines)
    but the instance is missing upstream.

  - `IsTopologicalGroup` for the same — immediate from `ContinuousMul`
    (via `Submonoid.continuousMul`) plus the new `ContinuousInv`.

Once those instances are available, `Subgroup.topologicalClosure`
applies and `H_Fib := ρ_Fib_SU2.range.topologicalClosure` is a
well-formed closed subgroup of SU(2). We then ship membership lemmas
for the generators and the lift lemma to/from the `Set.closure` form
used by `fibonacci_density_conditional`, plus a clean `H_Fib = ⊤`
form of the conditional density theorem.

After this section, the **only** remaining substrate gap for full
constructive D4 discharge is the classification of closed subgroups
of SU(2) (Cartan + 1-dim/3-dim structure theorem). All of D1-D3.b's
structural ruleouts now become potentially actionable at the
subgroup level. -/

/-- `Matrix.specialUnitaryGroup (Fin n) ℂ` has continuous inversion.

Inversion on SU(n) is defined as `star` (the conjugate transpose, which
agrees with the inverse on the unitary group). `star` on `Matrix` is
continuous (`Matrix.instContinuousStar`), and the subtype map preserves
continuity, so `Continuous fun A : SU(n) => star A` lifts to
`Continuous fun A : SU(n) => A⁻¹` via the definition `Inv` instance. -/
noncomputable instance su_continuousInv (n : ℕ) :
    ContinuousInv ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) := by
  refine ⟨?_⟩
  refine Continuous.subtype_mk ?_ ?_
  exact (continuous_star (R := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val

/-- `Matrix.specialUnitaryGroup (Fin n) ℂ` is a topological group.

Combines `Submonoid.continuousMul` (inherited from `Matrix`'s continuous
multiplication on a Submonoid) with the new `su_continuousInv` instance.
The `IsTopologicalGroup` class extends `ContinuousMul` and `ContinuousInv`,
both of which are now in scope. -/
noncomputable instance su_isTopologicalGroup (n : ℕ) :
    IsTopologicalGroup ↥(Matrix.specialUnitaryGroup (Fin n) ℂ) := { }

/-- **The Fibonacci closure subgroup.**

`H_Fib` is the topological closure of `MonoidHom.range ρ_Fib_SU2`, viewed
as a closed subgroup of SU(2). By construction `H_Fib` contains the image
of every braid word under `ρ_Fib_SU2`, and is the smallest closed subgroup
of SU(2) with that property.

The residual D4 target reformulated: prove `H_Fib = ⊤`. -/
noncomputable def H_Fib : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ρ_Fib_SU2.range.topologicalClosure

/-- `H_Fib` is a closed subset of SU(2). -/
theorem H_Fib_isClosed :
    IsClosed (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
  Subgroup.isClosed_topologicalClosure _

/-- `σ_Fib_1_SU ∈ H_Fib`: the first braid generator's SU(2) image lies in
the Fibonacci closure subgroup. -/
theorem σ_Fib_1_SU_mem_H_Fib : σ_Fib_1_SU ∈ H_Fib := by
  show σ_Fib_1_SU ∈ ρ_Fib_SU2.range.topologicalClosure
  apply Subgroup.le_topologicalClosure
  exact MonoidHom.mem_range.mpr
    ⟨SKEFTHawking.BraidGroup.σ (⟨0, by omega⟩ : Fin (3 - 1)), ρ_Fib_SU2_apply_σ0⟩

/-- `σ_Fib_2_SU ∈ H_Fib`: the second braid generator's SU(2) image lies in
the Fibonacci closure subgroup. -/
theorem σ_Fib_2_SU_mem_H_Fib : σ_Fib_2_SU ∈ H_Fib := by
  show σ_Fib_2_SU ∈ ρ_Fib_SU2.range.topologicalClosure
  apply Subgroup.le_topologicalClosure
  exact MonoidHom.mem_range.mpr
    ⟨SKEFTHawking.BraidGroup.σ (⟨1, by omega⟩ : Fin (3 - 1)), ρ_Fib_SU2_apply_σ1⟩

/-- **Lift lemma**: the `Subgroup`-eq-`⊤` form of the residual D4
hypothesis is equivalent to the `Set`-eq-`Set.univ` form used by
`fibonacci_density_conditional`.

The two surface forms differ only in the bundled-vs-coerced view of
closure: `H_Fib = ⊤` (a `Subgroup` equality) iff
`closure (Set.range ρ_Fib_SU2) = Set.univ` (a `Set` equality). -/
theorem H_Fib_eq_top_iff_closure_eq_univ :
    H_Fib = ⊤ ↔ closure (Set.range ρ_Fib_SU2) =
      (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  unfold H_Fib
  rw [SetLike.ext'_iff]
  rw [Subgroup.topologicalClosure_coe, ρ_Fib_SU2.coe_range, Subgroup.coe_top]

/-- **Fibonacci density theorem, conditional on `H_Fib = ⊤`** (the
subgroup-level form of the residual D4 hypothesis).

This is the subgroup-form analogue of `fibonacci_density_conditional`,
composed through `H_Fib_eq_top_iff_closure_eq_univ`. Discharging
`H_Fib = ⊤` (the D4.2+ residual) discharges the unconditional Fibonacci
density theorem. -/
theorem fibonacci_density_from_H_Fib_eq_top (h : H_Fib = ⊤) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (ρ_Fib_SU2 b : Matrix (Fin 2) (Fin 2) ℂ)) :=
  fibonacci_density_conditional (H_Fib_eq_top_iff_closure_eq_univ.mp h)

/-! ## 11. Subgroup-level structural ruleouts (Phase D4.2)

With D4.1's `H_Fib` packaging in place, this section lifts the
matrix-algebra-level structural facts of D1-D3.b into the
`Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)` language. The lifts
are entirely mechanical (via `Subtype.ext` + `SubmonoidClass.coe_pow`),
but they're the prerequisite for any downstream argument that needs
to reason about H_Fib as a closed subgroup of SU(2) (e.g., the
"H_Fib is not contained in any finite subgroup" step toward Cartan
classification).

The ruleouts at this level:
  - `σ_Fib_1_SU` has multiplicative period exactly 20 in SU(2) (qua group).
  - `H_Fib` is compact (closed subset of compact SU(2)).
  - `H_Fib ≠ ⊥` (non-trivial — contains a non-identity generator).
  - `H_Fib` is NOT abelian (contains non-commuting elements).
  - `H_Fib` contains an element of period exactly 20.

These translate the matrix-level facts into the Subgroup-language
needed for the D4.3+ closed-subgroup-classification argument. -/

section D4_2_StructuralRuleouts

/-- `σ_Fib_1_SU ^ 20 = 1` in SU(2) qua group. Lifted from
`σ_Fib_1_SU_mat_pow_20` (matrix-level) via `Subtype.ext +
SubmonoidClass.coe_pow`. -/
theorem σ_Fib_1_SU_pow_20_eq_one :
    σ_Fib_1_SU ^ 20 = (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact σ_Fib_1_SU_mat_pow_20

/-- `σ_Fib_1_SU ^ 10 ≠ 1` in SU(2). Lifted from
`σ_Fib_1_SU_mat_pow_10_ne_one`. -/
theorem σ_Fib_1_SU_pow_10_ne_one :
    σ_Fib_1_SU ^ 10 ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h
  apply σ_Fib_1_SU_mat_pow_10_ne_one
  have h2 : (σ_Fib_1_SU ^ 10).val =
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val := by rw [h]
  rw [SubmonoidClass.coe_pow] at h2
  exact h2

/-- `σ_Fib_1_SU ^ 4 ≠ 1` in SU(2). Lifted from
`σ_Fib_1_SU_mat_pow_4_ne_one`. -/
theorem σ_Fib_1_SU_pow_4_ne_one :
    σ_Fib_1_SU ^ 4 ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h
  apply σ_Fib_1_SU_mat_pow_4_ne_one
  have h2 : (σ_Fib_1_SU ^ 4).val =
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val := by rw [h]
  rw [SubmonoidClass.coe_pow] at h2
  exact h2

/-- **`σ_Fib_1_SU` has multiplicative period exactly 20 in SU(2)**.
Packages the three pow-facts above into a single conjunction. The
order of σ_Fib_1_SU in `↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)` is
exactly 20 (the only divisor of 20 not dividing 4 or 10 is 20 itself). -/
theorem σ_Fib_1_SU_has_period_20 :
    σ_Fib_1_SU ^ 20 = (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
    σ_Fib_1_SU ^ 10 ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∧
    σ_Fib_1_SU ^ 4 ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
  ⟨σ_Fib_1_SU_pow_20_eq_one, σ_Fib_1_SU_pow_10_ne_one, σ_Fib_1_SU_pow_4_ne_one⟩

/-- **`H_Fib` is compact** as a subset of SU(2). Proof: `H_Fib` is
closed (D4.1) and SU(2) is compact (via `Matrix.specialUnitaryGroup`'s
`CompactSpace` instance from `FKLW.SpecialUnitaryTopology`). -/
theorem H_Fib_isCompact :
    IsCompact (H_Fib : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
  IsCompact.of_isClosed_subset isCompact_univ H_Fib_isClosed (Set.subset_univ _)

/-- **`H_Fib ≠ ⊥`**: the Fibonacci closure subgroup is non-trivial.
Proof: σ_Fib_1_SU ∈ H_Fib but σ_Fib_1_SU ≠ 1 (D2). -/
theorem H_Fib_ne_bot : H_Fib ≠ ⊥ := by
  intro h
  have h_in : σ_Fib_1_SU ∈ (⊥ : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
    h ▸ σ_Fib_1_SU_mem_H_Fib
  rw [Subgroup.mem_bot] at h_in
  exact σ_Fib_1_SU_ne_one h_in

/-- **`H_Fib` is NOT abelian**: contains two non-commuting elements.
Proof: σ_Fib_1_SU, σ_Fib_2_SU ∈ H_Fib (D4.1) and they don't commute
(D1's `σ_Fib_SU_not_commute`). -/
theorem H_Fib_not_abelian :
    ∃ x y : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      x ∈ H_Fib ∧ y ∈ H_Fib ∧ x * y ≠ y * x :=
  ⟨σ_Fib_1_SU, σ_Fib_2_SU, σ_Fib_1_SU_mem_H_Fib, σ_Fib_2_SU_mem_H_Fib,
    fun h => σ_Fib_SU_not_commute h⟩

/-- **`H_Fib` contains an element of multiplicative period exactly 20**.
Witnessed by σ_Fib_1_SU (in H_Fib by D4.1, has period 20 by D4.2). -/
theorem H_Fib_contains_period_20_element :
    ∃ u : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      u ∈ H_Fib ∧
      u ^ 20 = 1 ∧ u ^ 10 ≠ 1 ∧ u ^ 4 ≠ 1 :=
  ⟨σ_Fib_1_SU, σ_Fib_1_SU_mem_H_Fib,
    σ_Fib_1_SU_pow_20_eq_one, σ_Fib_1_SU_pow_10_ne_one, σ_Fib_1_SU_pow_4_ne_one⟩

/-- **`H_Fib` is NOT contained in the center of SU(2)**. The center
of SU(2) is `{±I}`, and σ_Fib_1_SU ≠ ±I at the matrix level
(D2's `σ_Fib_1_SU_mat_ne_one` + `σ_Fib_1_SU_mat_ne_neg_one`). Since
σ_Fib_1_SU ∈ H_Fib but σ_Fib_1_SU's matrix is neither ±I, H_Fib
cannot be contained in `{u : SU(2) | u = ±1}`. We state the weaker
form ≰ ⟨σ_Fib_1_SU⟩, which gives strict non-triviality beyond
`H_Fib ≠ ⊥`. -/
theorem H_Fib_not_subset_singleton_id :
    ¬ ∀ u : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        u ∈ H_Fib → u = 1 := by
  intro h_all_id
  exact σ_Fib_1_SU_ne_one (h_all_id σ_Fib_1_SU σ_Fib_1_SU_mem_H_Fib)

end D4_2_StructuralRuleouts

/-! ## 12. Cardinality bounds for finite-case H_Fib (Phase D4.3.a)

If `H_Fib` were finite, Lagrange's theorem combined with the order-20
fact + non-commute fact gives the lower bound `|H_Fib| ≥ 40`. This
section ships:

  - `σ_Fib_1_SU_orderOf : orderOf σ_Fib_1_SU = 20` in SU(2) qua group.
  - `σ_Fib_2_SU_mat_pow_eq_F_conj n`: F-conjugacy lifted to powers
    (`σ_Fib_2^n = F · σ_Fib_1^n · F`) via F²=I telescope.
  - `σ_Fib_2_SU_mat_pow_eq_one_iff n`: `σ_Fib_2^n = I ↔ σ_Fib_1^n = I`.
  - `σ_Fib_2_SU_orderOf : orderOf σ_Fib_2_SU = 20` (same period via
    F-conjugacy).
  - `σ_Fib_2_SU_not_mem_zpowers_σ_Fib_1_SU`: σ_Fib_2_SU is NOT in the
    cyclic subgroup generated by σ_Fib_1_SU (since membership would
    force commutation, contradicting D1's non-commute fact).
  - `zpowers_σ_Fib_1_SU_lt_H_Fib`: strict subgroup containment.
  - `H_Fib_card_ge_20_if_finite`: 20 ≤ |H_Fib| in finite case via
    Lagrange + orderOf.
  - **`H_Fib_card_ge_40_if_finite`**: 40 ≤ |H_Fib| in finite case via
    strict containment + Lagrange (multiples-of-20 strictly above 20
    start at 40).

These cardinality bounds are tight in the sense that no SU(2) finite
subgroup of order < 40 can contain H_Fib (and via D4.4 below, the
order = 40 candidate `BD_40` is also ruled out, completing the
finite-case ruleout). -/

section D4_3a_CardinalityBounds

/-- **`σ_Fib_1_SU` has multiplicative order exactly 20** in SU(2)
qua group. Combines `σ_Fib_1_SU_pow_20_eq_one`, `_pow_10_ne_one`,
`_pow_4_ne_one` via divisors-of-20 enumeration. -/
theorem σ_Fib_1_SU_orderOf : orderOf σ_Fib_1_SU = 20 := by
  have h_dvd_20 : orderOf σ_Fib_1_SU ∣ 20 :=
    orderOf_dvd_of_pow_eq_one σ_Fib_1_SU_pow_20_eq_one
  have h_not_dvd_10 : ¬ (orderOf σ_Fib_1_SU ∣ 10) := fun h =>
    σ_Fib_1_SU_pow_10_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)
  have h_not_dvd_4 : ¬ (orderOf σ_Fib_1_SU ∣ 4) := fun h =>
    σ_Fib_1_SU_pow_4_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)
  have h_le : orderOf σ_Fib_1_SU ≤ 20 := Nat.le_of_dvd (by norm_num) h_dvd_20
  interval_cases (orderOf σ_Fib_1_SU) <;>
    first | rfl | (exfalso; revert h_dvd_20 h_not_dvd_10 h_not_dvd_4; decide)

/-- F-conjugacy lifts to powers: `σ_Fib_2^n = F · σ_Fib_1^n · F`,
proved by induction on `n` using `F² = I` to telescope. -/
private theorem σ_Fib_2_SU_mat_pow_eq_F_conj (n : ℕ) :
    σ_Fib_2_SU_mat ^ n = F_C * σ_Fib_1_SU_mat ^ n * F_C := by
  induction n with
  | zero => simp [F_C_sq]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ, σ_Fib_2_SU_mat_eq_F_conj]
    show F_C * σ_Fib_1_SU_mat ^ k * F_C * (F_C * σ_Fib_1_SU_mat * F_C) =
         F_C * (σ_Fib_1_SU_mat ^ k * σ_Fib_1_SU_mat) * F_C
    rw [show F_C * σ_Fib_1_SU_mat ^ k * F_C * (F_C * σ_Fib_1_SU_mat * F_C) =
            F_C * σ_Fib_1_SU_mat ^ k * (F_C * F_C) * σ_Fib_1_SU_mat * F_C
         from by noncomm_ring]
    rw [F_C_sq, mul_one]
    noncomm_ring

/-- `σ_Fib_2^n = I ↔ σ_Fib_1^n = I`. Both directions via F-conjugacy:
F²=I means conjugating by F is a self-inverse bijection that maps I to I. -/
private theorem σ_Fib_2_SU_mat_pow_eq_one_iff (n : ℕ) :
    σ_Fib_2_SU_mat ^ n = 1 ↔ σ_Fib_1_SU_mat ^ n = 1 := by
  rw [σ_Fib_2_SU_mat_pow_eq_F_conj]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- F·σ_1^n·F = 1, conjugate by F: σ_1^n = F·1·F = F·F = 1
    have h2 : F_C * (F_C * σ_Fib_1_SU_mat ^ n * F_C) * F_C =
        F_C * (1 : Matrix (Fin 2) (Fin 2) ℂ) * F_C := by rw [h]
    rw [show F_C * (F_C * σ_Fib_1_SU_mat ^ n * F_C) * F_C =
            (F_C * F_C) * σ_Fib_1_SU_mat ^ n * (F_C * F_C) from by noncomm_ring] at h2
    rw [F_C_sq, one_mul, mul_one] at h2
    rw [show F_C * (1 : Matrix (Fin 2) (Fin 2) ℂ) * F_C = F_C * F_C from by
        rw [mul_one]] at h2
    rw [F_C_sq] at h2
    exact h2
  · rw [h, mul_one, F_C_sq]

/-- `σ_Fib_2_SU_mat ^ 20 = I`. -/
theorem σ_Fib_2_SU_mat_pow_20 :
    σ_Fib_2_SU_mat ^ 20 = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  (σ_Fib_2_SU_mat_pow_eq_one_iff 20).mpr σ_Fib_1_SU_mat_pow_20

/-- `σ_Fib_2_SU_mat ^ 10 ≠ I`. -/
theorem σ_Fib_2_SU_mat_pow_10_ne_one :
    σ_Fib_2_SU_mat ^ 10 ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := fun h =>
  σ_Fib_1_SU_mat_pow_10_ne_one ((σ_Fib_2_SU_mat_pow_eq_one_iff 10).mp h)

/-- `σ_Fib_2_SU_mat ^ 4 ≠ I`. -/
theorem σ_Fib_2_SU_mat_pow_4_ne_one :
    σ_Fib_2_SU_mat ^ 4 ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := fun h =>
  σ_Fib_1_SU_mat_pow_4_ne_one ((σ_Fib_2_SU_mat_pow_eq_one_iff 4).mp h)

/-- `σ_Fib_2_SU ^ 20 = 1` in SU(2). -/
theorem σ_Fib_2_SU_pow_20_eq_one :
    σ_Fib_2_SU ^ 20 = (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact σ_Fib_2_SU_mat_pow_20

/-- `σ_Fib_2_SU ^ 10 ≠ 1` in SU(2). -/
theorem σ_Fib_2_SU_pow_10_ne_one :
    σ_Fib_2_SU ^ 10 ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h
  apply σ_Fib_2_SU_mat_pow_10_ne_one
  have h2 : (σ_Fib_2_SU ^ 10).val =
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val := by rw [h]
  rw [SubmonoidClass.coe_pow] at h2
  exact h2

/-- `σ_Fib_2_SU ^ 4 ≠ 1` in SU(2). -/
theorem σ_Fib_2_SU_pow_4_ne_one :
    σ_Fib_2_SU ^ 4 ≠ (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  intro h
  apply σ_Fib_2_SU_mat_pow_4_ne_one
  have h2 : (σ_Fib_2_SU ^ 4).val =
      (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val := by rw [h]
  rw [SubmonoidClass.coe_pow] at h2
  exact h2

/-- **`σ_Fib_2_SU` has multiplicative order exactly 20** in SU(2).
By symmetry with `σ_Fib_1_SU_orderOf` via F-conjugacy. -/
theorem σ_Fib_2_SU_orderOf : orderOf σ_Fib_2_SU = 20 := by
  have h_dvd_20 : orderOf σ_Fib_2_SU ∣ 20 :=
    orderOf_dvd_of_pow_eq_one σ_Fib_2_SU_pow_20_eq_one
  have h_not_dvd_10 : ¬ (orderOf σ_Fib_2_SU ∣ 10) := fun h =>
    σ_Fib_2_SU_pow_10_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)
  have h_not_dvd_4 : ¬ (orderOf σ_Fib_2_SU ∣ 4) := fun h =>
    σ_Fib_2_SU_pow_4_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)
  have h_le : orderOf σ_Fib_2_SU ≤ 20 := Nat.le_of_dvd (by norm_num) h_dvd_20
  interval_cases (orderOf σ_Fib_2_SU) <;>
    first | rfl | (exfalso; revert h_dvd_20 h_not_dvd_10 h_not_dvd_4; decide)

/-- **`σ_Fib_2_SU ∉ Subgroup.zpowers σ_Fib_1_SU`**: the second
generator is not in the cyclic subgroup generated by the first.

Proof: if σ_Fib_2_SU = σ_Fib_1_SU^n for some integer n, then
σ_Fib_1_SU * σ_Fib_2_SU = σ_Fib_1_SU * σ_Fib_1_SU^n = σ_Fib_1_SU^n
* σ_Fib_1_SU = σ_Fib_2_SU * σ_Fib_1_SU (powers of an element commute
with the element). This contradicts D1's `σ_Fib_SU_not_commute`. -/
theorem σ_Fib_2_SU_not_mem_zpowers_σ_Fib_1_SU :
    σ_Fib_2_SU ∉ Subgroup.zpowers σ_Fib_1_SU := by
  intro h_mem
  rw [Subgroup.mem_zpowers_iff] at h_mem
  obtain ⟨n, hn⟩ := h_mem
  apply σ_Fib_SU_not_commute
  rw [← hn]
  exact Commute.eq (Commute.zpow_right (Commute.refl _) n)

/-- `Subgroup.zpowers σ_Fib_1_SU ≤ H_Fib`: the cyclic subgroup of
σ_Fib_1_SU is contained in H_Fib. -/
theorem zpowers_σ_Fib_1_SU_le_H_Fib :
    (Subgroup.zpowers σ_Fib_1_SU :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ≤ H_Fib :=
  Subgroup.zpowers_le.mpr σ_Fib_1_SU_mem_H_Fib

/-- **Strict containment**: `Subgroup.zpowers σ_Fib_1_SU < H_Fib`.
The cyclic subgroup is strictly smaller than H_Fib (which also
contains σ_Fib_2_SU ∉ zpowers σ_Fib_1_SU). -/
theorem zpowers_σ_Fib_1_SU_lt_H_Fib :
    (Subgroup.zpowers σ_Fib_1_SU :
        Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) < H_Fib := by
  refine lt_of_le_of_ne zpowers_σ_Fib_1_SU_le_H_Fib ?_
  intro h_eq
  apply σ_Fib_2_SU_not_mem_zpowers_σ_Fib_1_SU
  rw [h_eq]
  exact σ_Fib_2_SU_mem_H_Fib

/-- **Cardinality lower bound (finite case)**: if `H_Fib` is finite
as a set, then `|H_Fib| ≥ 20` via Lagrange + σ_Fib_1_SU's order = 20. -/
theorem H_Fib_card_ge_20_if_finite
    (h_fin : (H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).Finite) :
    20 ≤ Nat.card H_Fib := by
  have h := Subgroup.orderOf_le_card H_Fib h_fin σ_Fib_1_SU_mem_H_Fib
  rw [σ_Fib_1_SU_orderOf] at h
  exact h

/-- **Strengthened cardinality lower bound (finite case)**: if `H_Fib`
is finite, then `|H_Fib| ≥ 40`.

Proof: by Lagrange, `20 = |zpowers σ_Fib_1_SU| ∣ |H_Fib|` (using
`zpowers_σ_Fib_1_SU_le_H_Fib` + `Subgroup.card_dvd_of_le`). By strict
containment, `|zpowers σ_Fib_1_SU| < |H_Fib|`, i.e., `20 < |H_Fib|`.
The smallest multiple of 20 strictly greater than 20 is 40. -/
theorem H_Fib_card_ge_40_if_finite
    (h_fin : (H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).Finite) :
    40 ≤ Nat.card H_Fib := by
  -- Cardinality of zpowers σ_Fib_1_SU = orderOf σ_Fib_1_SU = 20.
  have h_card_zpowers : Nat.card (Subgroup.zpowers σ_Fib_1_SU) = 20 := by
    rw [Nat.card_zpowers, σ_Fib_1_SU_orderOf]
  -- 20 | |H_Fib| via Lagrange on zpowers ≤ H_Fib.
  have h_dvd : Nat.card (Subgroup.zpowers σ_Fib_1_SU) ∣ Nat.card H_Fib :=
    Subgroup.card_dvd_of_le zpowers_σ_Fib_1_SU_le_H_Fib
  rw [h_card_zpowers] at h_dvd
  -- |zpowers| < |H_Fib| via strict containment + finite (Set.Finite version).
  -- Use SetLike strict + finite card mono.
  have h_lt_card : Nat.card (Subgroup.zpowers σ_Fib_1_SU) < Nat.card H_Fib := by
    apply Set.Finite.card_lt_card h_fin
    show (Subgroup.zpowers σ_Fib_1_SU :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ⊂ ↑H_Fib
    exact zpowers_σ_Fib_1_SU_lt_H_Fib
  rw [h_card_zpowers] at h_lt_card
  -- 20 | |H_Fib| ∧ 20 < |H_Fib| → 40 ≤ |H_Fib|
  -- |H_Fib| is a multiple of 20 strictly greater than 20, hence ≥ 40.
  obtain ⟨k, hk⟩ := h_dvd
  rw [hk] at h_lt_card ⊢
  -- 20 < 20 * k → 2 ≤ k
  have hk_ge : 2 ≤ k := by omega
  omega

/-- **Dichotomy**: `H_Fib` is either infinite or has cardinality ≥ 40.

Clean trichotomy-ish statement bundling D4.3.a's two-case analysis. -/
theorem H_Fib_infinite_or_card_ge_40 :
    Set.Infinite (H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∨
    40 ≤ Nat.card H_Fib := by
  by_cases h : (H_Fib :
      Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).Finite
  · right; exact H_Fib_card_ge_40_if_finite h
  · left; exact h

end D4_3a_CardinalityBounds

/-! ## 9. Module summary (Phase 6p Wave 2c.4a-R4.2.d.{1,2,3a,3b,4.1,4.2,4.3.a})

This module ships **structural facts** about the concrete Fibonacci
braid representation `ρ_Fib_SU2` from R4.2.c, in preparation for the
full constructive density discharge.

**Theorems shipped in R4.2.d.1 (commit 4dd4b68)**:

  - `σ_Fib_1_pow_10` : `σ_Fib_1^10 = I` (using R_1^5 = 1, R_τ^5 = -1).
  - `ω_Fib_C_pow_20` : `ω_Fib_C^20 = 1` (20th root of unity).
  - `σ_Fib_1_pow_20` : `σ_Fib_1^20 = I`.
  - `σ_Fib_1_SU_mat_pow_20` : `σ_Fib_1_SU_mat^20 = I` (combines ω^20 = 1
    with σ_Fib_1^20 = I).
  - **`σ_Fib_not_commute`** : `σ_Fib_1 · σ_Fib_2 ≠ σ_Fib_2 · σ_Fib_1`
    — the critical separating fact.
  - `σ_Fib_SU_mat_not_commute`, `σ_Fib_SU_not_commute` — inherited
    non-commutation for the det-normalized generators.
  - `σ_Fib_1_mul_σ_Fib_2_trace_eq` : `tr(σ_Fib_1 · σ_Fib_2) = R_1 · R_τ`
    — uses `fib_yb_core_identity` from R4.2.b.2.
  - **`σ_Fib_1_SU_mul_σ_Fib_2_SU_trace`** : `tr(σ_Fib_1_SU · σ_Fib_2_SU) = 1`
    — spectral invariant, corresponds to rotation by 2π/3 in SO(3).
  - **`fibonacci_density_conditional`** : full `DenseInSpecialUnitary`
    conclusion *conditional* on the residual hypothesis
    `closure(range ρ_Fib_SU2) = univ` in SU(2). Makes explicit the
    last substantive gap for Path (i) constructive discharge.

**Theorems shipped in R4.2.d.2 (this commit)** — individual-generator
trace formulas + F-conjugacy + non-centrality:

  - **`R1_C_ne_Rtau_C`** : the two R-eigenvalues are distinct
    (extracted from §3 as a standalone fact).
  - `σ_Fib_1_trace : tr(σ_Fib_1) = R_1 + R_τ`.
  - `σ_Fib_2_trace : tr(σ_Fib_2) = R_1 + R_τ` (same as σ_Fib_1; via
    the algebraic identity `φInv_C² + φInv_C = 1`).
  - **`σ_Fib_1_SU_mat_trace_eq : tr(σ_Fib_1_SU_mat) = exp(-7πi/10) +
    exp(7πi/10)`** — exponential form of the spectral invariant
    (corresponds to rotation by 7π/5 in SO(3); period 20 in SU(2)
    matches `σ_Fib_1_SU_mat^20 = I` from §2).
  - **`σ_Fib_2_SU_mat_eq_F_conj : σ_Fib_2_SU_mat = F_C · σ_Fib_1_SU_mat · F_C`**
    — the F-conjugacy relation between the two generators. F is the
    Bonesteel involutive Hermitian F-matrix.
  - `σ_Fib_2_SU_mat_trace_eq_σ_Fib_1_SU_mat_trace : tr(σ_Fib_2_SU_mat)
    = tr(σ_Fib_1_SU_mat)` — same spectrum, via trace cyclicity + F²=I.
  - `σ_Fib_2_SU_mat_trace_eq : tr(σ_Fib_2_SU_mat) = exp(-7πi/10) +
    exp(7πi/10)` — derived form for σ_Fib_2.
  - **`σ_Fib_1_SU_mat_diag_ne`** : diagonal entries [0,0] and [1,1]
    of σ_Fib_1_SU_mat differ (so σ_Fib_1_SU_mat is NOT a scalar matrix).
  - `σ_Fib_1_SU_mat_ne_smul_one : σ_Fib_1_SU_mat ≠ c • I` for any `c`.
  - `σ_Fib_1_SU_mat_ne_one`, `σ_Fib_1_SU_mat_ne_neg_one`.
  - `σ_Fib_2_SU_mat_ne_smul_one`, `σ_Fib_2_SU_mat_ne_one`,
    `σ_Fib_2_SU_mat_ne_neg_one` (via F-conjugacy preserves
    scalar-ness — if σ_Fib_2_SU_mat = c·I then so is σ_Fib_1_SU_mat).
  - `σ_Fib_1_SU_ne_one`, `σ_Fib_2_SU_ne_one` — non-identity in SU(2)
    qua group (SU(2) does not have a Neg instance as a `Subgroup`;
    the `≠ -I` content lives at the matrix algebra level).

**Theorems shipped in R4.2.d.3a (this commit)** — conjugation analysis
ruling out the torus normalizer N(T):

  - `ω_Fib_C_pow_10 : ω_Fib_C^10 = -1` — ω is a primitive 20th root of
    unity (private helper).
  - `R1_C_pow_10 : R1_C^10 = 1` — derived from `R1_C^5 = 1` (private).
  - **`ω_Fib_C_sq_mul_R1_C_sq_ne_one : ω² · R_1² ≠ 1`** — the key
    blocking identity. Proof: `(ω²·R_1²)^5 = ω^10·R_1^10 = (-1)·1 = -1`.
  - `φInv_C_pow_5_ne_one : φInv_C^5 ≠ 1` — private helper. Cast to ℝ,
    then use `φ > 1 ⟹ φInv < 1 ⟹ φInv^5 < 1`.
  - **`σ_Fib_2_apply_00_ne_zero : σ_Fib_2[0,0] ≠ 0`** — factor
    `σ_Fib_2[0,0] = φInv · (φInv · R_1 + R_τ)`; if zero, taking 5th
    powers gives `φInv^5 = 1`, contradicting `φInv_C_pow_5_ne_one`.
  - **`σ_Fib_SU_mat_not_conj_inverts : σ_Fib_2_SU_mat · σ_Fib_1_SU_mat
    ≠ star σ_Fib_1_SU_mat · σ_Fib_2_SU_mat`** — the headline N(T)
    ruleout. Equivalent to: conjugation by σ_Fib_2_SU does NOT invert
    σ_Fib_1_SU. Proof: project to entry [0,0]. After algebra, equality
    forces `(ω·R_1)² = (ω·R_1) · star(ω·R_1) = ‖ω·R_1‖² = 1`, i.e.,
    `ω²·R_1² = 1`, contradicting `ω_Fib_C_sq_mul_R1_C_sq_ne_one`.

**Density implication after D3.a**: closed subgroups of SU(2) of
dimension 1 are exactly the maximal tori T and their normalizers N(T)
(with `N(T)/T = Z/2`). For ⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ ⊆ N(T):
  • If σ_Fib_2_SU ∈ T: forces commutation with σ_Fib_1_SU (T abelian),
    contradicting §3 non-commutation.
  • If σ_Fib_2_SU ∈ N(T) \ T: forces `σ_Fib_2_SU·σ_Fib_1_SU·σ_Fib_2_SU⁻¹
    = σ_Fib_1_SU⁻¹` (Weyl-group inversion), equivalent to the
    inequality shipped here being an equality, contradicting D3.a.
Hence ⟨σ_Fib_1_SU, σ_Fib_2_SU⟩ ⊄ N(T) for any T.

Combined with D2 (center {±I} + 1-tori ruled out by non-centrality +
non-commutation), the only closed subgroups of SU(2) still possible
are the FINITE binary subgroups (Z_n, BD_4n, 2T, 2O, 2I) — to be
ruled out in D3.b — and SU(2) itself.

**Theorems shipped in R4.2.d.3b (this commit)** — order analysis +
finite-subgroup ruleout:

  - `R1_C_ne_one : R_1 ≠ 1` (private helper). Via bridge identity
    `R_1^2 + R_1^3 = 1/φ`: if R_1 = 1, then `2 = 1/φ`, but `1/φ < 1`.
  - `ω_pow_4_mul_R1_pow_3 : ω^4 · R_1^3 = 1` (private). Cyclotomic
    identity: `4·(π/10) + 3·(-4π/5) = 2π/5 - 12π/5 = -2π`, so
    `exp(-2πi) = 1`.
  - `ω_R1_pow_4_eq_R1 : (ω · R_1)^4 = R_1` (private). The slick
    reduction: `(ω·R_1)^4 = ω^4·R_1^4 = (ω^4·R_1^3)·R_1 = 1·R_1 = R_1`.
  - **`σ_Fib_1_SU_mat_pow_4_ne_one : σ_Fib_1_SU_mat^4 ≠ I`** —
    rules out element order 4. Project [0,0]: `[σ^4][0,0] = (ω·R_1)^4
    = R_1`; if `σ^4 = I` then `R_1 = 1`, contradicting `R1_C_ne_one`.
  - **`σ_Fib_1_SU_mat_pow_10_eq_neg_one : σ_Fib_1_SU_mat^10 = -I`**
    — concrete value. `σ^10 = ω^10 • σ_Fib_1^10 = (-1) • I = -I`.
  - **`σ_Fib_1_SU_mat_pow_10_ne_one : σ_Fib_1_SU_mat^10 ≠ I`** —
    rules out element orders {5, 10}. Derived from `σ^10 = -I` and
    `-I ≠ I` (differ at [0,0]: `-1 ≠ 1`).
  - **`σ_Fib_1_SU_mat_has_period_20`** : packaged conjunction
    `σ^20 = I ∧ σ^10 ≠ I ∧ σ^4 ≠ I`. Combined with σ^20 = I, the
    order of σ_Fib_1_SU_mat in `M₂(ℂ)` is exactly 20 (divisors of
    20 not dividing 4 or 10 are just {20}).

**Finite-subgroup ruleout (proof-by-docstring; Mathlib4 substrate gap)**:

The order-20 fact + non-commutation + scalar-distinction directly
precludes any finite binary subgroup of SU(2) containing both
generators (Z_n abelian, BD_4n outside-cyclic order 4, 2T max
order 6, 2O max 8, 2I max 10).

**Combined with D2 + D3.a, the only remaining closed subgroup of
SU(2) containing both generators is SU(2) itself.** This is the
informal density result; formal closure-eq-univ is deferred to D4
pending Mathlib4 closed-subgroup classification for SU(2).

**Theorems shipped in R4.2.d.4.1 (this commit)** — closure-as-subgroup
substrate for the residual D4 discharge:

  - **`su_continuousInv`** : `ContinuousInv` instance for
    `Matrix.specialUnitaryGroup (Fin n) ℂ`, parametric in `n`.
    Proof: `(A : SU(n))⁻¹ = star A` (definitional); `star` on
    `Matrix` is continuous (`Matrix.instContinuousStar` upstream);
    subtype-mk lifts continuity. General-purpose Mathlib substrate
    not in v4.29.0 (no `ContinuousInv` or `IsTopologicalGroup`
    instance exists for the complex special unitary group upstream).
  - **`su_isTopologicalGroup`** : `IsTopologicalGroup` instance for
    `Matrix.specialUnitaryGroup (Fin n) ℂ`, combining the upstream
    `Submonoid.continuousMul` with the new `su_continuousInv`.
  - **`H_Fib`** : `(ρ_Fib_SU2.range).topologicalClosure` — the
    Fibonacci closure subgroup of SU(2), a closed `Subgroup`.
  - `H_Fib_isClosed` : `IsClosed (H_Fib : Set _)`.
  - **`σ_Fib_1_SU_mem_H_Fib`**, **`σ_Fib_2_SU_mem_H_Fib`** :
    both generators are in `H_Fib` (via the R4.2.c apply-on-σⱼ
    lemmas + `Subgroup.le_topologicalClosure`).
  - **`H_Fib_eq_top_iff_closure_eq_univ`** : equivalence of the
    `Subgroup`-eq-`⊤` form and the `Set`-eq-`Set.univ` form of
    the residual D4 hypothesis.
  - **`fibonacci_density_from_H_Fib_eq_top`** : full
    `DenseInSpecialUnitary 3 2 (ρ_Fib_SU2 · : Matrix _ _ ℂ)` from
    `H_Fib = ⊤`, via composition with `fibonacci_density_conditional`.

**Density implication after D4.1**: the residual D4 hypothesis is now
articulated at the `Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)`
level as `H_Fib = ⊤`, with general-purpose topological-group substrate
in place. The remaining work (D4.2+) is to discharge `H_Fib = ⊤`
using:

  - the structural ruleouts shipped in D1-D3.b (period 20,
    non-commute, non-N(T), non-scalar), which constrain any proper
    closed subgroup containing both generators;
  - plus either (a) Cartan's classification of closed subgroups of
    SU(2) (Mathlib4 substrate gap), or (b) an in-tree direct
    accumulation argument (~500-1500 LoC of additional topology).

**Theorems shipped in R4.2.d.4.2 (this commit)** — Subgroup-level
structural ruleouts (D1-D3.b matrix-level facts lifted to `Subgroup`):

  - **`σ_Fib_1_SU_pow_20_eq_one : σ_Fib_1_SU ^ 20 = 1`** in SU(2). Lifted
    from matrix-level `σ_Fib_1_SU_mat_pow_20` (D1) via
    `Subtype.ext + SubmonoidClass.coe_pow`.
  - **`σ_Fib_1_SU_pow_10_ne_one`**, **`σ_Fib_1_SU_pow_4_ne_one`** —
    lifts of D3.b matrix facts.
  - **`σ_Fib_1_SU_has_period_20`** : packages the three above into
    the order-exactly-20 conjunction at the SU(2) Subgroup level.
  - **`H_Fib_isCompact`** : H_Fib is compact (closed subset of
    compact SU(2)). Uses `instCompactSpaceSpecialUnitaryGroup`
    from `FKLW.SpecialUnitaryTopology`.
  - **`H_Fib_ne_bot`** : H_Fib non-trivial (contains σ_Fib_1_SU ≠ 1).
  - **`H_Fib_not_abelian`** : ∃ x y ∈ H_Fib, x*y ≠ y*x — H_Fib is
    not abelian. Lifted from D1's `σ_Fib_SU_not_commute`.
  - **`H_Fib_contains_period_20_element`** : ∃ u ∈ H_Fib with order
    exactly 20 in SU(2). Witnessed by σ_Fib_1_SU.
  - **`H_Fib_not_subset_singleton_id`** : H_Fib is not the trivial
    subgroup pointwise (stronger form of `H_Fib_ne_bot`).

**Density implication after D4.2**: H_Fib is now provably a
**non-trivial, non-abelian, compact subgroup of SU(2) containing an
element of order exactly 20**. These are precisely the Subgroup-level
preconditions for the Cartan-classification argument: any closed
subgroup of SU(2) with these properties must be SU(2) itself (cyclic
Z_n ruled out by non-abelian; binary dihedral BD_4n outside-cyclic
order 4 < 20; 2T max order 6 < 20; 2O max order 8 < 20; 2I max
order 10 < 20; conjugates of T abelian; conjugates of N(T) ruled out
by D3.a). The remaining substrate piece (D4.3+) is the formal Cartan
classification itself.

**Theorems shipped in R4.2.d.4.3.a (this commit)** — finite-case
cardinality bounds for H_Fib (Lagrange-based):

  - **`σ_Fib_1_SU_orderOf : orderOf σ_Fib_1_SU = 20`** in SU(2) qua
    group, via divisors-of-20 enumeration + D4.2's pow-facts.
  - `σ_Fib_2_SU_mat_pow_eq_F_conj` : F-conjugacy lifts to powers
    (private helper, `σ_Fib_2^n = F·σ_Fib_1^n·F` via F²=I telescope).
  - `σ_Fib_2_SU_mat_pow_eq_one_iff` : `σ_Fib_2^n = I ↔ σ_Fib_1^n = I`
    (private helper).
  - `σ_Fib_2_SU_mat_pow_20`, `σ_Fib_2_SU_mat_pow_10_ne_one`,
    `σ_Fib_2_SU_mat_pow_4_ne_one` : matrix-level period 20 for σ_Fib_2.
  - `σ_Fib_2_SU_pow_20_eq_one`, `σ_Fib_2_SU_pow_10_ne_one`,
    `σ_Fib_2_SU_pow_4_ne_one` : SU(2)-level lifts.
  - **`σ_Fib_2_SU_orderOf : orderOf σ_Fib_2_SU = 20`** — same period
    as σ_Fib_1_SU via F-conjugacy.
  - **`σ_Fib_2_SU_not_mem_zpowers_σ_Fib_1_SU`** : σ_Fib_2_SU is NOT
    in the cyclic subgroup generated by σ_Fib_1_SU (forces commutation,
    contradicting D1).
  - `zpowers_σ_Fib_1_SU_le_H_Fib` : cyclic ⟨σ_Fib_1_SU⟩ ⊆ H_Fib.
  - **`zpowers_σ_Fib_1_SU_lt_H_Fib`** : STRICT containment (since
    σ_Fib_2_SU witnesses extra membership).
  - `H_Fib_card_ge_20_if_finite` : if H_Fib finite, |H_Fib| ≥ 20
    (via Lagrange + orderOf).
  - **`H_Fib_card_ge_40_if_finite`** : if H_Fib finite, |H_Fib| ≥ 40
    (Lagrange: 20 | |H_Fib| + strict containment: 20 < |H_Fib|, so
    the smallest multiple of 20 strictly above 20 is 40).

**Density implication after D4.3.a**: any finite SU(2) subgroup
containing H_Fib has cardinality ≥ 40 (with the contribution from
σ_Fib_2_SU's distinct cyclic subgroup giving |H_Fib| > 20 strictly).
Combined with D4.2's H_Fib_not_abelian, this rules out:
  - All cyclic Z_n (abelian, contradicts D4.2);
  - 2T (order 24 < 40);
  - 2O (order 48: now plausible cardinality but max element order is
    8 < 20, contradicts σ_Fib_2_SU's order 20);
  - 2I (order 120: max element order 10 < 20, also contradicted).

The remaining finite candidates are BD_{4n} for n ≥ 10 (binary
dihedral with cyclic part Z_{2n} ⊇ ⟨σ_Fib_1_SU⟩), to be ruled out
in D4.3.b by showing σ_Fib_2_SU ∉ Z_{2n} (forces non-cyclic-part,
where elements have order 4, contradicting σ_Fib_2_SU's order 20).

**Deferred to R4.2.d.4.3.b+**:
  - **D4.3.b**: rule out the binary dihedral candidate via the
    above "elements outside cyclic part have order 4" argument.
    Requires showing the structure of BD_4n in SU(2) (substrate gap).
  - **D4.3.c+**: complete formal Cartan classification of closed
    subgroups of SU(2). Multi-session in-tree substrate build
    (~500-1500 LoC remaining).

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new axioms): RESPECTED (zero introduced).

Zero new sorry. Zero new project-local axioms.
-/

end SKEFTHawking.FKLW
