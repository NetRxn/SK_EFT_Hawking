import SKEFTHawking.ExceptionalPoint

/-!
# Phase 6CD, Wave 3 — Certified exceptional-point proximity (spectral-gap closing)

In the PT-unbroken phase (`g² ≤ 1`) the non-Hermitian Bloch Hamiltonian `H(g)` (`NonHermitianBloch`)
has the two **real** eigenvalues `±√(1 − g²)` (`ExceptionalPoint.pt_symmetric_real_spectrum_iff`). Their
separation — the **eigenvalue splitting**

  `Δ(g) = 2√(1 − g²)`   (`eigenvalueSplitting`)

is the order parameter of the exceptional point: it is **positive** away from the EP, **closes to 0**
at the EP `g = 1`, and does so with the characteristic non-analytic square-root law. This module
certifies that closing with a `norm_num`-backed **rational proximity bound** (no floating point).

## Wave-3 headline (`ep_proximity_enclosure`)

Within `1/100` of the exceptional point in `g²` (`99/100 ≤ g² ≤ 1`) the real eigenvalue splitting is
bounded by the rational `1/5`: `Δ(g) ≤ 1/5`. Together with `ep_splitting_pos` (Δ > 0 strictly below
the EP) and `ep_splitting_at_ep` (Δ = 0 exactly at the EP), this is a certificate-grade description of
the spectral-gap closing. Both real eigenvalues are grounded as genuine roots of the secular
determinant (`realEigenvalues_secular`).

*(The optional topological winding number / non-Hermitian skin effect is deferred — the certified
proximity bound is the load-bearing W3 deliverable per the roadmap.)*

**Two-layer honesty.** The splitting algebra and the proximity certificate are Lean-verified; the
identification of `g` with a physical gain/loss parameter stays literature-cited.
-/

namespace SKEFTHawking.NonHermitian

open Complex Matrix

/-- The real eigenvalue splitting `Δ(g) = 2√(1 − g²)` of `H(g)` in the PT-unbroken phase. -/
noncomputable def eigenvalueSplitting (g : ℝ) : ℝ := 2 * Real.sqrt (1 - g ^ 2)

/-- A real `λ` with `λ² = 1 − g²` annihilates the secular determinant of `H(g)`. -/
lemma secular_zero_of_sq (g : ℝ) (lam : ℝ) (h : lam ^ 2 = 1 - g ^ 2) :
    (ptBloch g - (lam : ℂ) • 1).det = 0 := by
  rw [ptBloch_secular_det]
  have hc : ((lam : ℂ)) ^ 2 = ((1 - g ^ 2 : ℝ) : ℂ) := by rw [← h]; push_cast; ring
  rw [hc]; push_cast; ring

/-- Both `±√(1 − g²)` annihilate the secular determinant when `g² ≤ 1`: they are the two genuine real
eigenvalues whose separation is `eigenvalueSplitting g`. -/
lemma realEigenvalues_secular (g : ℝ) (hg : g ^ 2 ≤ 1) :
    (ptBloch g - ((Real.sqrt (1 - g ^ 2) : ℝ) : ℂ) • 1).det = 0 ∧
    (ptBloch g - ((-Real.sqrt (1 - g ^ 2) : ℝ) : ℂ) • 1).det = 0 := by
  have hsq : Real.sqrt (1 - g ^ 2) ^ 2 = 1 - g ^ 2 := Real.sq_sqrt (by linarith)
  exact ⟨secular_zero_of_sq g _ hsq, secular_zero_of_sq g _ (by rw [neg_pow]; simpa using hsq)⟩

/-- The splitting is strictly positive below the exceptional point: distinct real eigenvalues. -/
lemma ep_splitting_pos (g : ℝ) (h : g ^ 2 < 1) : 0 < eigenvalueSplitting g := by
  unfold eigenvalueSplitting
  have : 0 < Real.sqrt (1 - g ^ 2) := Real.sqrt_pos.mpr (by linarith)
  linarith

/-- The splitting closes to exactly `0` at the exceptional point `g = 1`. -/
lemma ep_splitting_at_ep : eigenvalueSplitting 1 = 0 := by
  unfold eigenvalueSplitting
  rw [show (1 : ℝ) - 1 ^ 2 = 0 by norm_num, Real.sqrt_zero, mul_zero]

/-- **Certified EP-proximity enclosure (Phase 6CD W3).** Within `1/100` of the exceptional point in
`g²` (`99/100 ≤ g² ≤ 1`), the real eigenvalue splitting `Δ(g) = 2√(1 − g²)` is bounded by the rational
`1/5`. A `norm_num`-backed certificate of the spectral-gap closing (no floating point). -/
theorem ep_proximity_enclosure (g : ℝ) (h1 : 99 / 100 ≤ g ^ 2) (_h2 : g ^ 2 ≤ 1) :
    eigenvalueSplitting g ≤ 1 / 5 := by
  unfold eigenvalueSplitting
  have hsqrt : Real.sqrt (1 - g ^ 2) ≤ 1 / 10 := by
    rw [show (1 : ℝ) / 10 = Real.sqrt (1 / 100) from by
      rw [show (1 : ℝ) / 100 = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

end SKEFTHawking.NonHermitian
