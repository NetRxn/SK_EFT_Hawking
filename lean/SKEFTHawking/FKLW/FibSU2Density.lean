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

/-! ## 6. Conditional density theorem (Phase D1 final)

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

/-! ## 7. Module summary (Phase 6p Wave 2c.4a-R4.2.d.{1,2})

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

**Deferred to R4.2.d.{3,4}**:
  - **D3**: rule out the remaining closed subgroups of SU(2) — finite
    binary subgroups (cyclic Z_n, binary dihedral BD_4n, binary
    tetrahedral 2T, binary octahedral 2O, binary icosahedral 2I) and
    normalizers of maximal tori. The non-commutation + non-centrality
    (D2) rules out the center and 1-tori; remaining work classifies
    against finite subgroups (e.g., via showing some braid word has
    infinite order or via discrete-vs-continuous-spectrum analysis)
    and against torus normalizers (which have dimension 1 + Z/2).
    Multi-session work; needs either closed-subgroup classification
    theorem for SU(2) in Mathlib4 (currently absent) or direct
    HBS-style accumulation argument.
  - **D4**: assemble `closure(range ρ_Fib_SU2) = univ`, then apply
    `bridge_FKLW_unitary_hom` (R2-soundness-audit-cleaned version)
    for `DenseInSpecialUnitary 3 2 (ρ_Fib_SU2 · : Matrix _ _ ℂ)`.

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new axioms): RESPECTED (zero introduced).

Zero new sorry. Zero new project-local axioms.
-/

end SKEFTHawking.FKLW
