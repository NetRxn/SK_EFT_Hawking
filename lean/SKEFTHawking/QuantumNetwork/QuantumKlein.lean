import SKEFTHawking.QuantumNetwork.QuantumRelativeEntropy
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Klein's inequality: nonnegativity of the quantum relative entropy (Phase 6AK, Wave FU-8)

`S(ρ ‖ σ) ≥ 0` for a density operator `ρ` and a positive-definite density operator `σ`. The proof is
the standard two-eigenbasis spectral argument, built from first principles:

* write `ρ = U_ρ Dρ U_ρᴴ`, `log σ = U_σ D_L U_σᴴ` (spectral theorem / matrix logarithm), and reduce
  `tr(ρ log σ)` to `tr(Mᴴ Dρ M D_L)` with `M = U_ρᴴ U_σ` unitary (`trace_rho_mul_matrixLog_eq`);
* the pure-algebra identity `tr(Mᴴ diag a M diag b) = ∑ⱼ ∑ᵢ aᵢ |Mᵢⱼ|² bⱼ`
  (`trace_conjTranspose_diag_mul_diag`) turns this into `∑ᵢⱼ pᵢ Pᵢⱼ log qⱼ`, where `Pᵢⱼ = |Mᵢⱼ|²` is
  **doubly stochastic** (`sum_normSq_row`, `sum_normSq_col`, from `M Mᴴ = Mᴴ M = 1`);
* Jensen for the concave `log` (`overlap_jensen`) bounds `∑ⱼ Pᵢⱼ log qⱼ ≤ log(∑ⱼ Pᵢⱼ qⱼ) = log rᵢ`,
  reducing `S(ρ‖σ)` to the classical Gibbs/KL nonnegativity `∑ᵢ pᵢ(log pᵢ − log rᵢ) ≥ 0`
  (`classical_gibbs`, shipped in `QuantumRelativeEntropy.lean`).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Pure-algebra trace identity:** `tr(Mᴴ · diag a · M · diag b) = ∑ⱼ ∑ᵢ aᵢ · (conj Mᵢⱼ · Mᵢⱼ) · bⱼ`.
The quadratic-form core of the Klein spectral expansion. -/
theorem trace_conjTranspose_diag_mul_diag (M : Matrix ι ι ℂ) (a b : ι → ℂ) :
    (Mᴴ * Matrix.diagonal a * M * Matrix.diagonal b).trace
      = ∑ j, ∑ i, a i * (star (M i j) * M i j) * b j := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  ring

/-- **Row sums of `|Mᵢⱼ|²` are `1`** when `M Mᴴ = 1`: `∑ⱼ |Mᵢⱼ|² = 1`. -/
theorem sum_normSq_row {M : Matrix ι ι ℂ} (hM : M * Mᴴ = 1) (i : ι) :
    ∑ j, ((Complex.normSq (M i j) : ℝ)) = 1 := by
  have h := congrFun (congrFun hM i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ j, Complex.normSq (M i j) : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply]
    exact (Complex.mul_conj (M i j)).symm
  exact_mod_cast h2

/-- **Column sums of `|Mᵢⱼ|²` are `1`** when `Mᴴ M = 1`: `∑ᵢ |Mᵢⱼ|² = 1`. -/
theorem sum_normSq_col {M : Matrix ι ι ℂ} (hM : Mᴴ * M = 1) (j : ι) :
    ∑ i, ((Complex.normSq (M i j) : ℝ)) = 1 := by
  have h := congrFun (congrFun hM j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ i, Complex.normSq (M i j) : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply]
    exact Complex.normSq_eq_conj_mul_self
  exact_mod_cast h2

omit [DecidableEq ι] in
/-- **Jensen for `log` over a doubly-stochastic row:** if `w j ≥ 0`, `∑ⱼ w j = 1`, and `q j > 0`, then
`∑ⱼ w j · log(q j) ≤ log(∑ⱼ w j · q j)`. -/
theorem overlap_jensen {w q : ι → ℝ} (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (hq : ∀ j, 0 < q j) :
    ∑ j, w j * Real.log (q j) ≤ Real.log (∑ j, w j * q j) := by
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
    (t := Finset.univ) (w := w) (p := q) (fun j _ => hw j) hw1 (fun j _ => Set.mem_Ioi.mpr (hq j))
  simpa only [smul_eq_mul] using hconc

/-- The overlap unitary `M = U_ρᴴ U_σ` between the two eigenbases. -/
noncomputable def overlapUnitary {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Matrix ι ι ℂ :=
  (↑(star hρ.eigenvectorUnitary) : Matrix ι ι ℂ) * (↑hσ.eigenvectorUnitary : Matrix ι ι ℂ)

/-- `M = ↑(star U_ρ · U_σ)` as the coercion of a single product unitary. -/
theorem overlapUnitary_eq_coe {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    overlapUnitary hρ hσ
      = ((star hρ.eigenvectorUnitary * hσ.eigenvectorUnitary : unitaryGroup ι ℂ)
          : Matrix ι ι ℂ) := by
  rw [overlapUnitary, Submonoid.coe_mul]

/-- `Mᴴ = U_σᴴ U_ρ`. -/
theorem overlapUnitary_conjTranspose {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (overlapUnitary hρ hσ)ᴴ
      = (↑(star hσ.eigenvectorUnitary) : Matrix ι ι ℂ) * (↑hρ.eigenvectorUnitary : Matrix ι ι ℂ) := by
  rw [overlapUnitary_eq_coe, ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, StarMul.star_mul,
    star_star, Submonoid.coe_mul]

/-- `M Mᴴ = 1` (M is unitary). -/
theorem overlapUnitary_mul_conjTranspose {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) : overlapUnitary hρ hσ * (overlapUnitary hρ hσ)ᴴ = 1 := by
  rw [overlapUnitary_eq_coe, ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star,
    Unitary.coe_mul_star_self]

/-- `Mᴴ M = 1` (M is unitary). -/
theorem overlapUnitary_conjTranspose_mul {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) : (overlapUnitary hρ hσ)ᴴ * overlapUnitary hρ hσ = 1 := by
  rw [overlapUnitary_eq_coe, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self]

/-- **Spectral expansion of the cross term** `Re tr(ρ log σ) = ∑ⱼ ∑ᵢ pᵢ |Mᵢⱼ|² log qⱼ`,
where `M = U_ρᴴ U_σ` is the eigenbasis overlap unitary. -/
theorem re_trace_mul_matrixLog_cross {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ * matrixLog hσ).trace.re
      = ∑ j, ∑ i, hρ.eigenvalues i * Complex.normSq (overlapUnitary hρ hσ i j)
          * Real.log (hσ.eigenvalues j) := by
  have hred : (ρ * matrixLog hσ).trace
      = ((overlapUnitary hρ hσ)ᴴ
          * Matrix.diagonal (fun i => (RCLike.ofReal (hρ.eigenvalues i) : ℂ))
          * overlapUnitary hρ hσ
          * Matrix.diagonal (fun j => (RCLike.ofReal (Real.log (hσ.eigenvalues j)) : ℂ))).trace := by
    rw [overlapUnitary_conjTranspose, overlapUnitary]
    conv_lhs => rw [hρ.spectral_theorem, matrixLog, Matrix.IsHermitian.cfc,
      Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
    simp only [Function.comp_def, Unitary.coe_star, ← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
  rw [hred, trace_conjTranspose_diag_mul_diag]
  have hcast : (∑ j, ∑ i, (RCLike.ofReal (hρ.eigenvalues i) : ℂ)
        * (star (overlapUnitary hρ hσ i j) * overlapUnitary hρ hσ i j)
        * (RCLike.ofReal (Real.log (hσ.eigenvalues j)) : ℂ))
      = ((∑ j, ∑ i, hρ.eigenvalues i * Complex.normSq (overlapUnitary hρ hσ i j)
          * Real.log (hσ.eigenvalues j) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show star (overlapUnitary hρ hσ i j)
          = (starRingEnd ℂ) (overlapUnitary hρ hσ i j) from rfl,
      ← Complex.normSq_eq_conj_mul_self]
    push_cast [RCLike.ofReal_eq_complex_ofReal]
    ring
  rw [hcast, Complex.ofReal_re]

/-- **Klein's inequality:** the quantum relative entropy is nonnegative, `S(ρ ‖ σ) ≥ 0`, for a density
operator `ρ` and a positive-definite density operator `σ`. Proof: the eigenbasis-overlap matrix
`Pᵢⱼ = |⟨eᵢ|fⱼ⟩|²` is doubly stochastic, so `tr(ρ log σ) = ∑ᵢ pᵢ ∑ⱼ Pᵢⱼ log qⱼ ≤ ∑ᵢ pᵢ log rᵢ`
(Jensen, `rᵢ = ∑ⱼ Pᵢⱼ qⱼ`), and `S(ρ‖σ) ≥ ∑ᵢ pᵢ(log pᵢ − log rᵢ) ≥ 0` (classical Gibbs). -/
theorem relativeEntropy_nonneg {ρ σ : Matrix ι ι ℂ}
    (hρ : IsDensityOperator ρ) (hσ : σ.PosDef) (hσtr : σ.trace = 1) :
    0 ≤ relativeEntropy hρ.1.isHermitian hσ.1 := by
  have hp0 : ∀ i, 0 ≤ hρ.1.isHermitian.eigenvalues i := fun i => hρ.1.eigenvalues_nonneg i
  have hq0 : ∀ j, 0 < hσ.1.eigenvalues j := fun j => hσ.eigenvalues_pos j
  set P : ι → ι → ℝ := fun i j => Complex.normSq (overlapUnitary hρ.1.isHermitian hσ.1 i j) with hP
  have hP0 : ∀ i j, 0 ≤ P i j := fun i j => Complex.normSq_nonneg _
  have hrow : ∀ i, ∑ j, P i j = 1 := fun i =>
    sum_normSq_row (overlapUnitary_mul_conjTranspose hρ.1.isHermitian hσ.1) i
  have hcol : ∀ j, ∑ i, P i j = 1 := fun j =>
    sum_normSq_col (overlapUnitary_conjTranspose_mul hρ.1.isHermitian hσ.1) j
  have hpsum : ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := sum_eigenvalues_density hρ
  have hqsum : ∑ j, hσ.1.eigenvalues j = 1 := by
    have h := hσ.1.trace_eq_sum_eigenvalues
    have hsum : ∑ j, (↑(hσ.1.eigenvalues j) : ℂ) = 1 := h.symm.trans hσtr
    have h2 : ((∑ j, hσ.1.eigenvalues j : ℝ) : ℂ) = 1 := by push_cast; exact hsum
    exact_mod_cast h2
  set r : ι → ℝ := fun i => ∑ j, P i j * hσ.1.eigenvalues j with hr
  have hr0 : ∀ i, 0 < r i := by
    intro i
    apply Finset.sum_pos'
    · exact fun j _ => mul_nonneg (hP0 i j) (le_of_lt (hq0 j))
    · obtain ⟨j, hj⟩ : ∃ j, P i j ≠ 0 := by
        by_contra h
        exact one_ne_zero
          ((hrow i).symm.trans (Finset.sum_eq_zero fun j _ => not_not.mp (not_exists.mp h j)))
      exact ⟨j, Finset.mem_univ j, mul_pos (lt_of_le_of_ne (hP0 i j) (Ne.symm hj)) (hq0 j)⟩
  have hrsum : ∑ i, r i = 1 := by
    simp only [hr]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hcol j, one_mul]]
    exact hqsum
  have hjensen : ∀ i, hρ.1.isHermitian.eigenvalues i
      * (∑ j, P i j * Real.log (hσ.1.eigenvalues j))
      ≤ hρ.1.isHermitian.eigenvalues i * Real.log (r i) := by
    intro i
    simp only [hr]
    exact mul_le_mul_of_nonneg_left (overlap_jensen (hP0 i) (hrow i) hq0) (hp0 i)
  have hcross : (ρ * matrixLog hσ.1).trace.re
      = ∑ i, hρ.1.isHermitian.eigenvalues i * ∑ j, P i j * Real.log (hσ.1.eigenvalues j) := by
    rw [re_trace_mul_matrixLog_cross hρ.1.isHermitian hσ.1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hP]; ring
  rw [relativeEntropy, re_trace_mul_matrixLog hρ.1.isHermitian, hcross, vonNeumannEntropy]
  have expand : -(∑ i, Real.negMulLog (hρ.1.isHermitian.eigenvalues i))
        - ∑ i, hρ.1.isHermitian.eigenvalues i * ∑ j, P i j * Real.log (hσ.1.eigenvalues j)
      = ∑ i, (hρ.1.isHermitian.eigenvalues i * Real.log (hρ.1.isHermitian.eigenvalues i)
          - hρ.1.isHermitian.eigenvalues i * (∑ j, P i j * Real.log (hσ.1.eigenvalues j))) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.negMulLog]
    ring
  rw [expand]
  refine le_trans (classical_gibbs hp0 hr0 hpsum hrsum) (Finset.sum_le_sum fun i _ => ?_)
  rw [mul_sub]
  linarith [hjensen i]

end SKEFTHawking.QuantumNetwork
