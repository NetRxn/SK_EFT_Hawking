import Mathlib

/-!
# Phase 6CA, Wave 1 — The gapped two-band Bloch Hamiltonian (Bloch-bundle substrate)

Every two-band Bloch Hamiltonian is, up to an overall energy shift, a real linear combination of Pauli
matrices — the **`d`-vector model**

  `H(d) = d₁ σˣ + d₂ σʸ + d₃ σᶻ = [[d₃, d₁ − i d₂], [d₁ + i d₂, −d₃]]`   (`blochPauli`),

parameterised by `d = (d₁, d₂, d₃) : ℝ³` (which over a Brillouin zone is a map `d(k)`). This module
establishes the spectral substrate that the Berry curvature (W1 cont.) and the Chern number (W2)
are built on:

* `blochPauli_isHermitian` — `H(d)` is Hermitian.
* `blochPauli_sq` — `H(d)² = ‖d‖² · I` (the Pauli identity `(d·σ)² = |d|²`).
* `blochPauli_secular_det` — `det(H(d) − λI) = λ² − ‖d‖²`, so the two bands are `±‖d‖`
  (`blochPauli_band_secular`).
* `blochPauli_gap_pos` — `d ≠ 0` implies the bands are separated by a gap `2‖d‖ > 0`, away from the
  band-touching point `d = 0` that the Chern number is defined around.
  ⚠️ **Forward direction only.** This docstring previously said "**iff**"; the shipped statement is
  the single implication `(hd : d ≠ 0) → 0 < √(dNormSq d)` and no converse is formalized. Corrected
  2026-07-30 after the D11 Stage-10 claims review found the draft had inherited the false "iff" from
  here. Do not restate it as a biconditional without shipping the converse.

## Scope (honest)

This wave ships the *gapped Bloch-bundle substrate*, and only that.

⚠️ **Corrected 2026-07-31 (Stage-13 BLOCKER).** This block previously said, in the present tense,
that the Berry connection/curvature differential geometry, the Chern-number integral
`C = (1/2π)∫_BZ F ∈ ℤ` (W2) and bulk–boundary correspondence (W3, deep → conditional) "are built on
top of" this `‖d‖`-gap structure. **None of those three exists in the tree.** The wording described
a plan as though it were shipped — under a heading titled "Scope (honest)", in the module supplying
five of the declarations the D11 bundle paper cites by name, so a referee following those citations
landed here.

What is actually built on this substrate is the **finite-lattice** Fukui–Hatsugai–Suzuki invariant
(`TopologicalBand/`), reached via `blochProj` and `blochFrameOfD`. It is an invariant of sampled link
data on a discrete torus; `FHSLatticeGauge.lean`'s own scope note disclaims equality to any continuum
first Chern class.

**Deferred, not conditional:** Berry connection/curvature (`berryCurvature`/`berryConnection` have
zero occurrences project-wide), the continuum integral above (route-C deferred — Mathlib has no
manifold form-integration, Stokes, de Rham or Brouwer degree), and bulk–boundary correspondence
(never executed; no `H_BulkBoundaryLandmark` Prop exists). Do not describe any of the three as
shipped, conditional, or in progress.

**Two-layer honesty.** The Pauli algebra and the gap structure are Lean-verified; the identification of
`d(k)` with a specific lattice model (Qi–Wu–Zhang, BHZ, …) stays literature-cited.
-/

namespace SKEFTHawking.Topological

open Complex Matrix

/-- The squared norm `‖d‖² = d₁² + d₂² + d₃²` of the `d`-vector. -/
def dNormSq (d : Fin 3 → ℝ) : ℝ := d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2

lemma dNormSq_nonneg (d : Fin 3 → ℝ) : 0 ≤ dNormSq d := by
  unfold dNormSq; positivity

/-- The two-band `d`-vector Bloch Hamiltonian `H(d) = d·σ`. -/
noncomputable def blochPauli (d : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(d 2 : ℂ), (d 0 : ℂ) - I * (d 1 : ℂ); (d 0 : ℂ) + I * (d 1 : ℂ), -(d 2 : ℂ)]

/-- `H(d)` is Hermitian (real eigenvalues — the two bands). -/
lemma blochPauli_isHermitian (d : Fin 3 → ℝ) : (blochPauli d).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochPauli, Matrix.conjTranspose_apply, Complex.conj_ofReal, sub_eq_add_neg]

/-- **The Pauli identity** `H(d)² = ‖d‖² · I`. The square of the `d·σ` Hamiltonian is a scalar matrix;
this is what forces the two bands to `±‖d‖`. -/
lemma blochPauli_sq (d : Fin 3 → ℝ) :
    blochPauli d * blochPauli d = (dNormSq d : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [blochPauli, dNormSq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val', smul_eq_mul] <;>
    push_cast <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- **The secular polynomial** `det(H(d) − λI) = λ² − ‖d‖²`. -/
lemma blochPauli_secular_det (d : Fin 3 → ℝ) (lam : ℂ) :
    (blochPauli d - lam • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = lam ^ 2 - (dNormSq d : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [blochPauli, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.of_apply,
    Matrix.cons_val']
  rw [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  simp only [mul_zero, sub_zero]
  rw [dNormSq]
  push_cast
  linear_combination ((d 1 : ℂ) ^ 2) * Complex.I_sq

/-- A real `λ` with `λ² = ‖d‖²` annihilates the secular determinant. -/
lemma blochPauli_secular_zero_of_sq (d : Fin 3 → ℝ) (lam : ℝ) (h : lam ^ 2 = dNormSq d) :
    (blochPauli d - (lam : ℂ) • 1).det = 0 := by
  rw [blochPauli_secular_det]
  have hc : ((lam : ℂ)) ^ 2 = ((dNormSq d : ℝ) : ℂ) := by rw [← h]; push_cast; ring
  rw [hc]; ring

/-- **The two bands** `±‖d‖` annihilate the secular determinant: the genuine eigenvalues of `H(d)`. -/
lemma blochPauli_band_secular (d : Fin 3 → ℝ) :
    (blochPauli d - ((Real.sqrt (dNormSq d) : ℝ) : ℂ) • 1).det = 0 ∧
    (blochPauli d - ((-Real.sqrt (dNormSq d) : ℝ) : ℂ) • 1).det = 0 := by
  have hsq : Real.sqrt (dNormSq d) ^ 2 = dNormSq d := Real.sq_sqrt (dNormSq_nonneg d)
  exact ⟨blochPauli_secular_zero_of_sq d _ hsq,
    blochPauli_secular_zero_of_sq d _ (by rw [neg_pow]; simpa using hsq)⟩

/-- **`d ≠ 0` implies the model is gapped.** The half-gap `‖d‖` (bands `±‖d‖`, separation `2‖d‖`) is
strictly positive away from the band-touching point `d = 0` — the degeneracy the Chern number is
defined around.

This is the forward direction; the converse is `blochPauli_gap_zero_of_eq_zero`, and the
biconditional a consumer should cite is `blochPauli_gap_pos_iff`.

*(History: this docstring read "gapped iff `d ≠ 0`" while only the forward implication was shipped,
and the D11 draft inherited the false attribution. Corrected 2026-07-30 by narrowing the docstring;
**superseded 2026-07-31 by shipping the converse**, which is four lines — narrowing the claim was
the wrong remedy when the missing half was this cheap to prove.)* -/
lemma blochPauli_gap_pos (d : Fin 3 → ℝ) (hd : d ≠ 0) : 0 < Real.sqrt (dNormSq d) := by
  rw [Real.sqrt_pos]
  by_contra hle
  rw [not_lt] at hle
  have h0 : dNormSq d = 0 := le_antisymm hle (dNormSq_nonneg d)
  unfold dNormSq at h0
  apply hd
  funext i
  have e0 : d 0 = 0 := by
    have h : d 0 ^ 2 = 0 := by nlinarith [sq_nonneg (d 0), sq_nonneg (d 1), sq_nonneg (d 2)]
    exact pow_eq_zero_iff (by norm_num) |>.mp h
  have e1 : d 1 = 0 := by
    have h : d 1 ^ 2 = 0 := by nlinarith [sq_nonneg (d 0), sq_nonneg (d 1), sq_nonneg (d 2)]
    exact pow_eq_zero_iff (by norm_num) |>.mp h
  have e2 : d 2 = 0 := by
    have h : d 2 ^ 2 = 0 := by nlinarith [sq_nonneg (d 0), sq_nonneg (d 1), sq_nonneg (d 2)]
    exact pow_eq_zero_iff (by norm_num) |>.mp h
  fin_cases i <;> simp_all

/-- **The converse: the band-touching point is gapless.** At `d = 0` the two bands coincide at
`0`, so the half-gap vanishes. -/
lemma blochPauli_gap_zero_of_eq_zero : Real.sqrt (dNormSq (0 : Fin 3 → ℝ)) = 0 := by
  have h : dNormSq (0 : Fin 3 → ℝ) = 0 := by unfold dNormSq; simp
  rw [h, Real.sqrt_zero]

/-- **The model is gapped IFF `d ≠ 0`.** The biconditional the `d`-vector picture is usually stated
with, and the form a consumer should cite. The forward direction is `blochPauli_gap_pos`; the
converse is the contrapositive of `blochPauli_gap_zero_of_eq_zero`.

Shipped 2026-07-31. The converse had previously been *disclaimed* in a docstring rather than
proved — but it is four lines, so the disclaimer cost more than the proof. -/
lemma blochPauli_gap_pos_iff (d : Fin 3 → ℝ) : 0 < Real.sqrt (dNormSq d) ↔ d ≠ 0 := by
  constructor
  · intro hpos hd
    rw [hd, blochPauli_gap_zero_of_eq_zero] at hpos
    exact lt_irrefl 0 hpos
  · exact blochPauli_gap_pos d

end SKEFTHawking.Topological
