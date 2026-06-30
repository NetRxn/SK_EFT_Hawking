import SKEFTHawking.NonHermitianBloch

/-!
# Phase 6CD, Wave 2 — PT-symmetry, real-spectrum criterion, and exceptional-point order

For the PT-symmetric non-Hermitian Bloch Hamiltonian `H(g) = [[ig, 1], [1, −ig]]`
(`NonHermitianBloch.ptBloch`), the characteristic polynomial is

  `det(H(g) − λ·I) = λ² + (g² − 1)`   (`ptBloch_secular_det`),

so the eigenvalues are `±√(1 − g²)`. This is the textbook **PT phase transition**:

* `|g| < 1` (PT-**unbroken**) — the spectrum is **real** (`±√(1−g²) ∈ ℝ`);
* `|g| = 1` — the **exceptional point**: both eigenvalues collapse to `0`;
* `|g| > 1` (PT-**broken**) — the eigenvalues are purely **imaginary** (`±i√(g²−1)`), no real eigenvalue.

## Wave-2 headlines

* `pt_symmetric_real_spectrum_iff` — `H(g)` has a **real** eigenvalue **iff** `g² ≤ 1`: a sharp
  biconditional criterion for the PT-unbroken phase.
* `ep_order_two` — at the exceptional point `g = 1` the characteristic polynomial is the perfect
  square `λ²`, so the degeneracy is a **second-order** EP (a double root) — consistent with `H(1)`
  being nilpotent (`NonHermitianBloch.ptBlochEP_nilpotent`).

**Two-layer honesty.** The spectral algebra and the PT criterion are Lean-verified; the mapping of `g`
to a physical gain/loss device stays literature-cited.
-/

namespace SKEFTHawking.NonHermitian

open Complex Matrix

/-- The characteristic polynomial of `H(g)`: `det(H(g) − λ·I) = λ² + (g² − 1)`. -/
lemma ptBloch_secular_det (g : ℝ) (lam : ℂ) :
    (ptBloch g - lam • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = lam ^ 2 + ((g : ℂ) ^ 2 - 1) := by
  rw [Matrix.det_fin_two]
  simp only [ptBloch, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.of_apply,
    Matrix.cons_val']
  rw [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  simp only [mul_zero, sub_zero]
  linear_combination (-(g : ℂ) ^ 2) * Complex.I_sq

/-- **PT real-spectrum criterion (Phase 6CD W2).** The non-Hermitian Bloch Hamiltonian `H(g)` has a
real eigenvalue **iff** `g² ≤ 1` — i.e. the spectrum is real exactly in the PT-unbroken phase. The
witness in the forward direction is `±√(1 − g²)`. -/
theorem pt_symmetric_real_spectrum_iff (g : ℝ) :
    (∃ lam : ℝ, (ptBloch g - (lam : ℂ) • 1).det = 0) ↔ g ^ 2 ≤ 1 := by
  constructor
  · rintro ⟨lam, hlam⟩
    rw [ptBloch_secular_det] at hlam
    have hreal : (lam : ℝ) ^ 2 + (g ^ 2 - 1) = 0 := by
      have : ((lam ^ 2 + (g ^ 2 - 1) : ℝ) : ℂ) = 0 := by push_cast; linear_combination hlam
      exact_mod_cast this
    nlinarith [sq_nonneg lam, hreal]
  · intro hg
    refine ⟨Real.sqrt (1 - g ^ 2), ?_⟩
    rw [ptBloch_secular_det]
    have hsq : Real.sqrt (1 - g ^ 2) ^ 2 = 1 - g ^ 2 := Real.sq_sqrt (by linarith)
    have : ((Real.sqrt (1 - g ^ 2)) : ℂ) ^ 2 + ((g : ℂ) ^ 2 - 1) = 0 := by
      rw [show ((Real.sqrt (1 - g ^ 2)) : ℂ) ^ 2 = ((Real.sqrt (1 - g ^ 2) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        hsq]
      push_cast; ring
    exact this

/-- **Second-order exceptional point (Phase 6CD W2).** At the EP `g = 1` the characteristic polynomial
collapses to the perfect square `λ²`: the two eigenvalues meet at `0` as a double root, so the EP has
order 2 (EP2). This matches `H(1)` being nilpotent (`ptBlochEP_nilpotent`). -/
theorem ep_order_two (lam : ℂ) :
    (ptBlochEP - lam • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = lam ^ 2 := by
  rw [ptBlochEP, ptBloch_secular_det]
  norm_num

end SKEFTHawking.NonHermitian
