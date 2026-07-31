import Mathlib

/-!
# Phase 6CB, Wave 1 — The acoustic Bloch operator of a diatomic phononic crystal

A periodic 1D **diatomic mass-spring chain** (two alternating masses `m₁, m₂ > 0`, a single
nearest-neighbour spring constant `κ > 0`, lattice constant `a > 0`) — the minimal model whose
Bloch–Floquet spectrum has a **band gap** (a feature absent from the single-band PhysLib
`CondensedMatter.TightBindingChain`, whose dispersion `E₀ − 2t·cos(ka)` is one gapless cosine band).

The mass-normalised **Bloch dynamical matrix** at crystal momentum `k` is the `2×2` Hermitian matrix

  `D(k) = ⎡ 2κ/m₁                         −(κ/√(m₁m₂))·(1 + e^{−ika}) ⎤`
  `       ⎣ −(κ/√(m₁m₂))·(1 + e^{+ika})    2κ/m₂                      ⎦`

whose two eigenvalues are the squared acoustic / optical phonon frequencies

  `ω²±(k) = κ(1/m₁ + 1/m₂) ± √( (κ(1/m₁ − 1/m₂))² + 2κ²(1 + cos ka)/(m₁m₂) )`.

## Wave-1 headline (`acousticBloch_spectrum`)

The two closed-form branches `branchMinus ≤ branchPlus` are **real** (the discriminant is a sum of a
square and a non-negative term) and **bounded below by 0** (`0 ≤ branchMinus`, the acoustic branch is a
non-negative squared frequency — the `k=0` Goldstone mode touches 0), and each branch **solves the
secular equation** `det(D(k) − ω²·I) = 0` (`acousticBloch_branch_secular`), i.e. they are genuine
eigenvalues of the Hermitian Bloch operator. This is the spectral object whose gaps Wave 2 certifies.

**Two-layer honesty.** The dynamical-matrix algebra and the branch spectrum are Lean-verified here.
The identification of a *physical* phononic crystal (which masses / spring constants realise a given
material) stays literature-cited at the point of use; this module fixes only the Bloch operator and
its spectrum. Cf. Kittel, *Introduction to Solid State Physics*, ch. 4 (diatomic linear chain).
-/

namespace SKEFTHawking.Phononic

open Complex Matrix

/-- Physical parameters of a 1D diatomic (two-sublattice) mass-spring chain. -/
structure DiatomicChain where
  /-- First sublattice mass. -/
  m₁ : ℝ
  /-- Second sublattice mass. -/
  m₂ : ℝ
  /-- Nearest-neighbour spring constant. -/
  κ : ℝ
  /-- Lattice constant (period of the diatomic cell). -/
  a : ℝ
  m₁_pos : 0 < m₁
  m₂_pos : 0 < m₂
  κ_pos : 0 < κ
  a_pos : 0 < a

namespace DiatomicChain

variable (D : DiatomicChain)

/-- On-site (diagonal) entry on the first sublattice, `2κ/m₁`. -/
noncomputable def diag₁ : ℝ := 2 * D.κ / D.m₁

/-- On-site (diagonal) entry on the second sublattice, `2κ/m₂`. -/
noncomputable def diag₂ : ℝ := 2 * D.κ / D.m₂

/-- The complex off-diagonal entry `D(k)₀₁ = −(κ/√(m₁m₂))·(1 + e^{−ika})`. -/
noncomputable def off (k : ℝ) : ℂ :=
  (-(D.κ) / Real.sqrt (D.m₁ * D.m₂) : ℝ) * (1 + Complex.exp (-(I * (k : ℂ) * (D.a : ℂ))))

/-- The `2×2` mass-normalised Bloch dynamical matrix `D(k)`. -/
noncomputable def blochMatrix (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(D.diag₁ : ℂ), D.off k; (starRingEnd ℂ) (D.off k), (D.diag₂ : ℂ)]

/-- The squared modulus of the off-diagonal entry, `|D(k)₀₁|² = 2κ²(1 + cos ka)/(m₁m₂)`. -/
noncomputable def normSqOff (k : ℝ) : ℝ :=
  2 * D.κ ^ 2 * (1 + Real.cos (k * D.a)) / (D.m₁ * D.m₂)

/-- Centre of the band pair, `κ(1/m₁ + 1/m₂)`. -/
noncomputable def mid : ℝ := D.κ * (1 / D.m₁ + 1 / D.m₂)

/-- Half the splitting at the diagonal level, `gap := diag₁ − mid = κ(1/m₁ − 1/m₂)`. -/
noncomputable def gap : ℝ := D.κ * (1 / D.m₁ - 1 / D.m₂)

/-- Discriminant under the square root, `(κ(1/m₁ − 1/m₂))² + 2κ²(1 + cos ka)/(m₁m₂)`. -/
noncomputable def disc (k : ℝ) : ℝ := D.gap ^ 2 + D.normSqOff k

/-- The optical (upper) squared-frequency branch `ω²₊(k)`. -/
noncomputable def branchPlus (k : ℝ) : ℝ := D.mid + Real.sqrt (D.disc k)

/-- The acoustic (lower) squared-frequency branch `ω²₋(k)`. -/
noncomputable def branchMinus (k : ℝ) : ℝ := D.mid - Real.sqrt (D.disc k)

/-! ### Evenness in the crystal momentum

Both branches depend on `k` only through `Real.cos (k * a)`, so the dispersion is even: the band
structure on `[-π/a, 0]` is the mirror of the one on `[0, π/a]`. Added 2026-07-31 (D11 Stage-13
round-7 finding 5.6): D11's Fig. 1 marks the gap edges as *attained* at `k = ±π` and its caption
justifies the negative endpoint "by evenness of the branches in `k`", but no evenness statement was
formalized anywhere in the acoustic modules — the one step in that figure a referee could not
follow into the kernel. These four lemmas close it in general, not only at `±π`. -/

@[simp] lemma normSqOff_neg (k : ℝ) : D.normSqOff (-k) = D.normSqOff k := by
  unfold normSqOff
  rw [neg_mul, Real.cos_neg]

@[simp] lemma disc_neg (k : ℝ) : D.disc (-k) = D.disc k := by
  unfold disc
  rw [normSqOff_neg]

/-- **The optical branch is even in `k`.** -/
@[simp] lemma branchPlus_neg (k : ℝ) : D.branchPlus (-k) = D.branchPlus k := by
  unfold branchPlus
  rw [disc_neg]

/-- **The acoustic branch is even in `k`.** -/
@[simp] lemma branchMinus_neg (k : ℝ) : D.branchMinus (-k) = D.branchMinus k := by
  unfold branchMinus
  rw [disc_neg]

/-! ### Basic positivity / sign facts -/

lemma m₁m₂_pos : 0 < D.m₁ * D.m₂ := mul_pos D.m₁_pos D.m₂_pos

lemma normSqOff_nonneg (k : ℝ) : 0 ≤ D.normSqOff k := by
  unfold normSqOff
  apply div_nonneg
  · exact mul_nonneg (by positivity)
      (by have := Real.neg_one_le_cos (k * D.a); linarith)
  · exact le_of_lt D.m₁m₂_pos

lemma disc_nonneg (k : ℝ) : 0 ≤ D.disc k := by
  unfold disc
  have h := D.normSqOff_nonneg k
  have : (0 : ℝ) ≤ D.gap ^ 2 := sq_nonneg _
  linarith

/-! ### The off-diagonal modulus -/

/-- `D(k)₀₁ · conj(D(k)₀₁) = |D(k)₀₁|²` evaluates to `2κ²(1 + cos ka)/(m₁m₂)` (as a complex scalar). -/
lemma off_mul_conj (k : ℝ) :
    D.off k * (starRingEnd ℂ) (D.off k) = (D.normSqOff k : ℂ) := by
  have hw : Complex.normSq (1 + Complex.exp (-(I * (k : ℂ) * (D.a : ℂ)))) =
      2 + 2 * Real.cos (k * D.a) := by
    have hz : (-(I * (k : ℂ) * (D.a : ℂ))) = ((-(k * D.a) : ℝ) : ℂ) * I := by push_cast; ring
    rw [hz, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
    nlinarith [Real.sin_sq_add_cos_sq (k * D.a)]
  have hm : D.m₁ * D.m₂ ≠ 0 := ne_of_gt D.m₁m₂_pos
  rw [Complex.mul_conj]
  norm_cast
  unfold off normSqOff
  rw [Complex.normSq_mul, hw, Complex.normSq_ofReal,
    show (-(D.κ) / Real.sqrt (D.m₁ * D.m₂)) * (-(D.κ) / Real.sqrt (D.m₁ * D.m₂))
      = D.κ * D.κ / (Real.sqrt (D.m₁ * D.m₂) * Real.sqrt (D.m₁ * D.m₂)) from by ring,
    Real.mul_self_sqrt (le_of_lt D.m₁m₂_pos)]
  field_simp

/-! ### The diagonal-to-centre identities -/

lemma diag₁_sub_mid : D.diag₁ - D.mid = D.gap := by
  simp only [diag₁, mid, gap]; ring

lemma diag₂_sub_mid : D.diag₂ - D.mid = -D.gap := by
  simp only [diag₂, mid, gap]; ring

/-! ### Hermiticity -/

/-- The Bloch dynamical matrix is Hermitian, so its spectrum is real. -/
lemma blochMatrix_isHermitian (k : ℝ) : (D.blochMatrix k).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochMatrix, Matrix.conjTranspose_apply, Complex.conj_ofReal]

/-! ### The secular equation -/

/-- The two real branches each annihilate the real characteristic polynomial
`(diag₁ − ω²)(diag₂ − ω²) − |off|²`. -/
lemma secular_real (k : ℝ) {lam : ℝ} (hlam : lam = D.branchPlus k ∨ lam = D.branchMinus k) :
    (D.diag₁ - lam) * (D.diag₂ - lam) - D.normSqOff k = 0 := by
  have hs2 : Real.sqrt (D.disc k) ^ 2 = D.gap ^ 2 + D.normSqOff k := by
    rw [Real.sq_sqrt (D.disc_nonneg k)]; rfl
  have e1 : D.diag₁ = D.mid + D.gap := by have := D.diag₁_sub_mid; linarith
  have e2 : D.diag₂ = D.mid - D.gap := by have := D.diag₂_sub_mid; linarith
  rcases hlam with h | h <;> subst h <;>
    simp only [branchPlus, branchMinus, e1, e2] <;>
    linear_combination hs2

/-- Each branch solves the secular equation `det(D(k) − ω²·I) = 0`: the closed-form acoustic and
optical squared frequencies are genuine eigenvalues of the Hermitian Bloch operator. -/
lemma acousticBloch_branch_secular (k : ℝ) {lam : ℝ}
    (hlam : lam = D.branchPlus k ∨ lam = D.branchMinus k) :
    (D.blochMatrix k - (lam : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
  have hsec := D.secular_real k hlam
  have hoff := D.off_mul_conj k
  rw [Matrix.det_fin_two]
  simp only [blochMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.of_apply,
    Matrix.cons_val']
  rw [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  simp only [mul_zero, sub_zero]
  rw [hoff]
  have hcast : ((D.diag₁ : ℂ) - ↑lam) * ((D.diag₂ : ℂ) - ↑lam) - ↑(D.normSqOff k)
      = (((D.diag₁ - lam) * (D.diag₂ - lam) - D.normSqOff k : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, hsec, Complex.ofReal_zero]

/-! ### Completeness: the two branches exhaust the spectrum -/

/-- Vieta sum: the two branches sum to the trace `diag₁ + diag₂`. -/
lemma branchMinus_add_branchPlus (k : ℝ) : D.branchMinus k + D.branchPlus k = D.diag₁ + D.diag₂ := by
  simp only [DiatomicChain.branchMinus, DiatomicChain.branchPlus, DiatomicChain.mid,
    DiatomicChain.diag₁, DiatomicChain.diag₂]; ring

/-- Vieta product: the two branches multiply to `diag₁·diag₂ − |off|²` (the determinant of `D(k)`). -/
lemma branchMinus_mul_branchPlus (k : ℝ) :
    D.branchMinus k * D.branchPlus k = D.diag₁ * D.diag₂ - D.normSqOff k := by
  have hs2 : Real.sqrt (D.disc k) ^ 2 = D.gap ^ 2 + D.normSqOff k := by
    rw [Real.sq_sqrt (D.disc_nonneg k)]; rfl
  have hmg : D.mid ^ 2 - D.gap ^ 2 = D.diag₁ * D.diag₂ := by
    simp only [DiatomicChain.mid, DiatomicChain.gap, DiatomicChain.diag₁, DiatomicChain.diag₂]; ring
  simp only [DiatomicChain.branchMinus, DiatomicChain.branchPlus]
  linear_combination hmg - hs2

/-- **The characteristic polynomial factors over the two branches:**
`det(D(k) − λ·I) = (λ − ω²₋(k))(λ − ω²₊(k))` for *every* `λ`. Hence the two branches are not merely
*some* eigenvalues — they are the **complete** spectrum: any `λ` with `det(D(k) − λ·I) = 0` equals
one of them (`acousticBloch_eigenvalue_iff`). -/
lemma acousticBloch_charpoly_factor (k : ℝ) (lam : ℂ) :
    (D.blochMatrix k - lam • 1).det = (lam - (D.branchMinus k : ℂ)) * (lam - (D.branchPlus k : ℂ)) := by
  have hoff := D.off_mul_conj k
  have hsumC : (D.diag₁ : ℂ) + (D.diag₂ : ℂ) = (D.branchMinus k : ℂ) + (D.branchPlus k : ℂ) := by
    exact_mod_cast (D.branchMinus_add_branchPlus k).symm
  have hprodC : (D.diag₁ : ℂ) * (D.diag₂ : ℂ) - (D.normSqOff k : ℂ)
      = (D.branchMinus k : ℂ) * (D.branchPlus k : ℂ) := by
    exact_mod_cast (D.branchMinus_mul_branchPlus k).symm
  rw [Matrix.det_fin_two]
  simp only [blochMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.of_apply,
    Matrix.cons_val']
  rw [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  simp only [mul_zero, sub_zero]
  rw [hoff]
  linear_combination (-lam) * hsumC + hprodC

/-- **Spectral completeness.** A real `λ` is an eigenvalue of `D(k)` (annihilates the secular
determinant) **iff** it is one of the two branches — the diatomic Bloch operator has exactly the
acoustic and optical squared-frequency eigenvalues, no others. -/
lemma acousticBloch_eigenvalue_iff (k : ℝ) (lam : ℝ) :
    (D.blochMatrix k - (lam : ℂ) • 1).det = 0 ↔ lam = D.branchMinus k ∨ lam = D.branchPlus k := by
  rw [D.acousticBloch_charpoly_factor k, mul_eq_zero, sub_eq_zero, sub_eq_zero,
    Complex.ofReal_inj, Complex.ofReal_inj]

/-! ### Branch ordering and lower bound -/

lemma branchMinus_le_branchPlus (k : ℝ) : D.branchMinus k ≤ D.branchPlus k := by
  unfold branchMinus branchPlus
  have := Real.sqrt_nonneg (D.disc k); linarith

lemma mid_pos : 0 < D.mid := by
  unfold mid
  exact mul_pos D.κ_pos (add_pos (one_div_pos.mpr D.m₁_pos) (one_div_pos.mpr D.m₂_pos))

/-- The acoustic branch is non-negative — the spectrum is bounded below by `0`. -/
lemma branchMinus_nonneg (k : ℝ) : 0 ≤ D.branchMinus k := by
  have hmid : 0 ≤ D.mid := le_of_lt D.mid_pos
  have hcos : Real.cos (k * D.a) ≤ 1 := Real.cos_le_one _
  have hm₁ := D.m₁_pos
  have hm₂ := D.m₂_pos
  have hkey : D.disc k ≤ D.mid ^ 2 := by
    have hexp : D.mid ^ 2 - D.disc k
        = 2 * D.κ ^ 2 * (1 - Real.cos (k * D.a)) / (D.m₁ * D.m₂) := by
      unfold disc normSqOff mid gap
      field_simp
      ring
    have hnn : 0 ≤ 2 * D.κ ^ 2 * (1 - Real.cos (k * D.a)) / (D.m₁ * D.m₂) := by
      apply div_nonneg
      · exact mul_nonneg (by positivity) (by linarith)
      · exact le_of_lt D.m₁m₂_pos
    linarith [hexp, hnn]
  have hsqrt : Real.sqrt (D.disc k) ≤ D.mid := by
    rw [show D.mid = Real.sqrt (D.mid ^ 2) from (Real.sqrt_sq hmid).symm]
    exact Real.sqrt_le_sqrt hkey
  unfold branchMinus; linarith

/-! ### Wave-1 headline -/

/-- **Acoustic Bloch spectrum (Phase 6CB W1).** For every crystal momentum `k`, the diatomic chain's
Bloch operator is Hermitian; its two closed-form squared-frequency branches are ordered
`0 ≤ ω²₋(k) ≤ ω²₊(k)` (real and bounded below), and each solves the secular equation
`det(D(k) − ω²·I) = 0` — i.e. they are the genuine acoustic/optical eigenvalues. -/
theorem acousticBloch_spectrum (k : ℝ) :
    (D.blochMatrix k).IsHermitian ∧
    0 ≤ D.branchMinus k ∧ D.branchMinus k ≤ D.branchPlus k ∧
    (D.blochMatrix k - (D.branchMinus k : ℂ) • 1).det = 0 ∧
    (D.blochMatrix k - (D.branchPlus k : ℂ) • 1).det = 0 := by
  refine ⟨D.blochMatrix_isHermitian k, D.branchMinus_nonneg k, D.branchMinus_le_branchPlus k,
    D.acousticBloch_branch_secular k (Or.inr rfl), D.acousticBloch_branch_secular k (Or.inl rfl)⟩

end DiatomicChain
end SKEFTHawking.Phononic
