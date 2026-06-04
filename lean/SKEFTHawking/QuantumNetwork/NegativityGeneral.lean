import SKEFTHawking.QuantumNetwork.LogNegativity

/-!
# Negativity convexity and general-density-operator strengthening (Phase 6AL, Wave 2, items B + E)

Matrix-level **negativity** `N(ρ) = ½(‖ρ^Γ‖₁ − 1)` for an arbitrary two-qubit operator, and:

- **B — convexity** `N(∑ₖ wₖ ρₖ) ≤ ∑ₖ wₖ N(ρₖ)`: classically mixing states cannot increase
  entanglement. Via partial-transpose linearity (`pt2_sum`/`pt2_smul`) + finite trace-norm subadditivity
  (`traceNorm_sum_le`, from `traceNorm_triangle`) + homogeneity (`traceNorm_smul_nonneg`). Together with the
  LOCC-monotonicity already shipped (`traceNorm_pt2_localKraus_le`) this makes negativity a verified
  bona-fide entanglement monotone.
- **E — drop side-conditions** for *arbitrary* density operators (not just Bell-diagonal):
  - `traceNorm_ge_abs_re_trace` `|Re tr A| ≤ ‖A‖₁` (Hermitian) — reusable.
  - `trace_pt2` / `pt2_isHermitian` — the partial transpose preserves trace and Hermiticity.
  - `negativity_nonneg` `0 ≤ N(ρ)` for any density operator (`‖ρ^Γ‖₁ ≥ |tr ρ^Γ| = 1`).
  - `one_le_traceNorm_pt2` / `traceNorm_pt2_ne_zero` ⟹ `logNegativity_density_add` (additivity of
    log-negativity with the `‖ρ^Γ‖₁ ≠ 0` side-condition discharged for density operators).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Finite trace-norm subadditivity:** `‖∑ₖ Mₖ‖₁ ≤ ∑ₖ ‖Mₖ‖₁`. -/
theorem traceNorm_sum_le {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι ℂ) :
    traceNorm (∑ k ∈ s, M k) ≤ ∑ k ∈ s, traceNorm (M k) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ht := traceNorm_triangle (M a) (∑ k ∈ s, M k)
    linarith

/-- **`|Re tr A| ≤ ‖A‖₁`** for a Hermitian operator (trace is dominated by the trace norm). -/
theorem traceNorm_ge_abs_re_trace {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    |A.trace.re| ≤ traceNorm A := by
  have hre : A.trace.re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  rw [traceNorm_hermitian hA, hre]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Matrix-level negativity** of a two-qubit operator, `N(ρ) = ½(‖ρ^Γ‖₁ − 1)`. -/
noncomputable def negativity (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  (traceNorm (pt2 ρ) - 1) / 2

/-- **Negativity is convex** (entanglement monotone under classical mixing):
`N(∑ₖ wₖ ρₖ) ≤ ∑ₖ wₖ N(ρₖ)` for nonnegative weights summing to `1`. -/
theorem negativity_convex {κ : Type*} [Fintype κ] (w : κ → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k = 1) (ρ : κ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    negativity (∑ k, (w k : ℂ) • ρ k) ≤ ∑ k, w k * negativity (ρ k) := by
  have hpt : pt2 (∑ k, (w k : ℂ) • ρ k) = ∑ k, (w k : ℂ) • pt2 (ρ k) := by
    rw [pt2_sum]; exact Finset.sum_congr rfl fun k _ => pt2_smul _ _
  have htn : traceNorm (pt2 (∑ k, (w k : ℂ) • ρ k)) ≤ ∑ k, w k * traceNorm (pt2 (ρ k)) := by
    rw [hpt]
    refine (traceNorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [traceNorm_smul_nonneg (hw0 k)]
  have hrhs : (∑ k, w k * negativity (ρ k)) = (∑ k, w k * traceNorm (pt2 (ρ k)) - 1) / 2 := by
    simp only [negativity]
    rw [show (∑ k, w k * ((traceNorm (pt2 (ρ k)) - 1) / 2))
          = (∑ k, (w k * traceNorm (pt2 (ρ k)) - w k)) / 2 from by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun k _ => by ring,
      Finset.sum_sub_distrib, hw1]
  rw [negativity, hrhs]
  linarith [htn]

/-- **The partial transpose preserves the trace** `tr(ρ^Γ) = tr ρ`. -/
theorem trace_pt2 (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : (pt2 ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, pt2, Matrix.of_apply, Prod.mk.eta]

/-- **The partial transpose preserves Hermiticity.** -/
theorem pt2_isHermitian {ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hρ : ρ.IsHermitian) :
    (pt2 ρ).IsHermitian := by
  show (pt2 ρ)ᴴ = pt2 ρ
  ext p q
  simp only [pt2, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact hρ.apply (p.1, q.2) (q.1, p.2)

/-- `‖ρ^Γ‖₁ ≥ 1` for any density operator (the partial transpose has trace `1`). -/
theorem one_le_traceNorm_pt2 {ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hρ : IsDensityOperator ρ) : 1 ≤ traceNorm (pt2 ρ) := by
  have htr : (pt2 ρ).trace = 1 := by rw [trace_pt2, hρ.2]
  calc (1 : ℝ) = |((pt2 ρ).trace.re)| := by rw [htr, Complex.one_re, abs_one]
    _ ≤ traceNorm (pt2 ρ) := traceNorm_ge_abs_re_trace (pt2_isHermitian hρ.1.isHermitian)

/-- **Negativity is nonnegative for any density operator** (general, not just Bell-diagonal). -/
theorem negativity_nonneg {ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hρ : IsDensityOperator ρ) : 0 ≤ negativity ρ := by
  rw [negativity]; linarith [one_le_traceNorm_pt2 hρ]

/-- `‖ρ^Γ‖₁ ≠ 0` for any density operator (discharges the `logNegativity_add` side-condition). -/
theorem traceNorm_pt2_ne_zero {ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hρ : IsDensityOperator ρ) : traceNorm (pt2 ρ) ≠ 0 := by
  have := one_le_traceNorm_pt2 hρ; linarith

/-- **Log-negativity additivity for arbitrary density operators** — the `‖ρ^Γ‖₁ ≠ 0` side-condition of
`logNegativity_add` is automatically discharged. -/
theorem logNegativity_density_add {ρ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    Real.logb 2 (traceNorm (pt2 ρ ⊗ₖ pt2 σ)) = logNegativity ρ + logNegativity σ :=
  logNegativity_add (traceNorm_pt2_ne_zero hρ) (traceNorm_pt2_ne_zero hσ)

end SKEFTHawking.QuantumNetwork
