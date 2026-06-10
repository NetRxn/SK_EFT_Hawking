/-
Phase 5c Wave 4 (+ review-2026-06-05 I2 fix-pass extension): SU(2)_k
S-matrices and Verlinde Formula at ALL levels k = 1, ..., 5.

Explicit S-matrices for SU(2) at levels k = 1, 2, 3, 4, 5.
Unitarity (S * S^T = I), modularity (det S != 0), and Verlinde formula
verification — the FULL fusion table N_{ij}^m at k = 3 (64 identities),
k = 4 (125), and k = 5 (216), each verified against su2kFusion.

For k=1: S = (1/sqrt(2)) * Hadamard (2x2)
For k=2: 3x3 Ising S-matrix with entries in Q(sqrt(2))
For k=3: 4x4 with entries in Q(phi) = Q(sqrt(5)) (golden ratio)
For k=4: 5x5 with entries in Q(sqrt(3))
For k=5: 6x6 with entries in Q(2cos(pi/7)) — the degree-3 totally real
         subfield of Q(zeta_7); the cubic minimal polynomial is PROVED
         from cos(4pi/7) = -cos(3pi/7) (no axioms, no native_decide)

k=1,2 entries are radical-algebraic; k=3,4 scales are radical-algebraic with
row-0 tied to the trig form by S_k3_row0_sin / S_k4_row0_sin; k=5 is defined
directly through 2cos(pi/7) and sin(pi/7) with proven minimal polynomial.
The Verlinde formula N_{ij}^m = sum_l S_{il} S_{jl} conj(S_{ml}) / S_{0l}
(S real symmetric here, so conj(S) = S) reproduces the fusion rules from
SU2kFusion.lean.

Non-degeneracy (det(S) != 0) is the MODULARITY condition:
this makes SU(2)_k a modular tensor category, not just a fusion category.

References:
  Verlinde, Nucl. Phys. B 300, 360 (1988)
  Lit-Search/Phase-5c/Verlinde formula, SU(2)_k modularity...
-/

import Mathlib
import SKEFTHawking.SU2kFusion

open Matrix Finset Real

namespace SKEFTHawking

/-! ## 1. SU(2)_1 S-matrix (2x2 Hadamard) -/

section Level1

/-- The S-matrix for SU(2)_1: (1/sqrt(2)) * [[1, 1], [1, -1]]. -/
noncomputable def S_k1 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / √2,  1 / √2;
     1 / √2, -1 / √2]

/-- S_{00} = 1/sqrt(2). -/
theorem S_k1_00 : S_k1 0 0 = 1 / √2 := by
  simp [S_k1, Matrix.of_apply, Matrix.cons_val_zero]

/-- S_{11} = -1/sqrt(2). -/
theorem S_k1_11 : S_k1 1 1 = -(1 / √2) := by
  simp [S_k1, Matrix.of_apply]; ring

/-- S is symmetric: S_{ij} = S_{ji}. -/
theorem S_k1_symmetric : S_k1.transpose = S_k1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S_k1, Matrix.transpose_apply]

/-
Unitarity: S * S^T = I for SU(2)_1.
-/
theorem S_k1_unitary : S_k1 * S_k1.transpose = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, S_k1 ] ; ring ; norm_num;
  · ring;
  · grind;
  · ring_nf; norm_num;

/-
det(S) != 0 for SU(2)_1 (modularity condition).
-/
theorem S_k1_det_ne_zero : S_k1.det ≠ 0 := by
  unfold S_k1; norm_num [ Matrix.det_fin_two ] ; ring_nf;
  norm_num

/-
Verlinde formula verification for SU(2)_1:
N_{11}^0 = sum_l S_{1l} S_{1l} S_{0l} / S_{0l} = S_{10}^2 + S_{11}^2 = 1/2 + 1/2 = 1.
This matches su2kFusion 1 1 1 0 = 1 (Z/2 fusion: V_1 tensor V_1 = V_0).
-/
theorem verlinde_k1_11_0 :
    ∑ l : Fin 2, S_k1 1 l * S_k1 1 l * S_k1 0 l / S_k1 0 l = 1 := by
  unfold S_k1; norm_num [ Fin.sum_univ_succ ] ; ring_nf ; norm_num;

/-
Verlinde: N_{11}^1 = 0 (V_1 tensor V_1 has no V_1).
-/
theorem verlinde_k1_11_1 :
    ∑ l : Fin 2, S_k1 1 l * S_k1 1 l * S_k1 1 l / S_k1 0 l = 0 := by
  unfold S_k1; norm_num [ Fin.sum_univ_succ ] ; ring;
  grind

end Level1

/-! ## 2. SU(2)_2 S-matrix (3x3, Ising) -/

section Level2

/-- The S-matrix for SU(2)_2 (Ising):
  [[1/2,    1/sqrt(2),  1/2],
   [1/sqrt(2),  0,    -1/sqrt(2)],
   [1/2,   -1/sqrt(2),  1/2]]
-/
noncomputable def S_k2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2,     1/√2,  1/2;
     1/√2,    0,    -(1/√2);
     1/2,    -(1/√2), 1/2]

/-- S_{11} = 0 for Ising (the sigma-sigma entry vanishes). -/
theorem S_k2_11_zero : S_k2 1 1 = 0 := by
  simp [S_k2, Matrix.of_apply]

/-- S is symmetric. -/
theorem S_k2_symmetric : S_k2.transpose = S_k2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S_k2, Matrix.transpose_apply]

/-
Unitarity: S * S^T = I for SU(2)_2.
-/
theorem S_k2_unitary : S_k2 * S_k2.transpose = 1 := by
  ext i j;
  fin_cases i <;> fin_cases j <;> norm_num [ Fin.sum_univ_succ, Matrix.mul_apply, S_k2 ];
  · norm_num [ ← sq ];
  · norm_num [ ← sq ];
  · norm_num [ ← sq ];
  · ring ; norm_num;
  · norm_num [ ← sq ]

/-
det(S) != 0 for SU(2)_2 (modularity condition).
-/
theorem S_k2_det_ne_zero : S_k2.det ≠ 0 := by
  norm_num [ Matrix.det_fin_three ];
  simp +decide [ S_k2 ];
  ring ; norm_num

/-
Verlinde for Ising: N_{11}^0 = 1 (sigma tensor sigma contains vacuum).
-/
theorem verlinde_k2_sigma_sq_vacuum :
    ∑ l : Fin 3, S_k2 1 l * S_k2 1 l * S_k2 0 l / S_k2 0 l = 1 := by
  norm_num [ Fin.sum_univ_succ, S_k2 ];
  norm_num [ ← sq ]

/-
Verlinde for Ising: N_{11}^1 = 0 (sigma^2 has no sigma).
-/
theorem verlinde_k2_sigma_sq_no_sigma :
    ∑ l : Fin 3, S_k2 1 l * S_k2 1 l * S_k2 1 l / S_k2 0 l = 0 := by
  unfold S_k2; norm_num [ Fin.sum_univ_succ ] ; ring;

/-
Verlinde for Ising: N_{11}^2 = 1 (sigma^2 contains psi).
-/
theorem verlinde_k2_sigma_sq_psi :
    ∑ l : Fin 3, S_k2 1 l * S_k2 1 l * S_k2 2 l / S_k2 0 l = 1 := by
  unfold S_k2; norm_num [ Fin.sum_univ_succ ] ; ring_nf ; norm_num;
  erw [ Matrix.cons_val_succ' ] ; norm_num

/-
Verlinde for Ising: N_{22}^0 = 1 (psi^2 = vacuum).
-/
theorem verlinde_k2_psi_sq_vacuum :
    ∑ l : Fin 3, S_k2 2 l * S_k2 2 l * S_k2 0 l / S_k2 0 l = 1 := by
  simp +decide [ Fin.sum_univ_three ];
  unfold S_k2;
  simp +zetaDelta at *;
  ring_nf; norm_num;

end Level2

/-! ## 3. SU(2)_3 S-matrix (4×4, golden-ratio entries) and full Verlinde formula

`S_{ab} = √(2/5)·sin((a+1)(b+1)π/5)` for `a, b = 0..3`. Factoring out the
overall scale `λ₃ = √(2/5)·sin(π/5) = √((5-√5)/20)` leaves the ratio matrix
`M_k3` with entries `±1, ±φ` (`φ` = the golden ratio `Real.goldenRatio`):
the Chebyshev recursion `sin((n+1)θ)/sin(θ) = U_n(cos θ)` at `θ = π/5` gives
`U₀ = 1`, `U₁ = 2cos(π/5) = φ`, `U₂ = φ² - 1 = φ`, `U₃ = 1`, with signs from
`sin` reflection/periodicity (`sin(x + π) = -sin x`). All Verlinde arithmetic
then lives in `ℚ(φ) = ℚ(√5)`, reduced by `φ² = φ + 1` (`Real.goldenRatio_sq`).
The first row is tied back to the literal trigonometric form by
`S_k3_row0_sin`. -/

section Level3

/-- Overall scale of the SU(2)₃ S-matrix: `λ₃ = √((5-√5)/20) = √(2/5)·sin(π/5)`
(see `lam_k3_eq_sin`). -/
noncomputable def lam_k3 : ℝ := √((5 - √5) / 20)

/-- Ratio matrix at k=3: `M_k3 a b = sin((a+1)(b+1)π/5)/sin(π/5) ∈ {±1, ±φ}`. -/
noncomputable def M_k3 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,           goldenRatio,  goldenRatio,  1;
     goldenRatio, 1,            -1,           -goldenRatio;
     goldenRatio, -1,           -1,           goldenRatio;
     1,           -goldenRatio, goldenRatio,  -1]

/-- The SU(2)₃ modular S-matrix: `S = λ₃ • M_k3`. -/
noncomputable def S_k3 : Matrix (Fin 4) (Fin 4) ℝ := lam_k3 • M_k3

/-- `√5 < 5` (radicand bound used for positivity of `λ₃`). -/
theorem sqrt5_lt_five : √5 < 5 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

theorem lam_k3_pos : 0 < lam_k3 :=
  Real.sqrt_pos.mpr (by nlinarith [sqrt5_lt_five])

/-- `λ₃² = (3 - φ)/10` (the radical form `(5-√5)/20` rewritten in the φ-atom,
so that all downstream reduction happens in the single atom `φ`). -/
theorem lam_k3_sq : lam_k3 ^ 2 = (3 - goldenRatio) / 10 := by
  unfold lam_k3
  rw [Real.sq_sqrt (by nlinarith [sqrt5_lt_five] : (0:ℝ) ≤ (5 - √5) / 20),
      show goldenRatio = (1 + √5) / 2 from rfl]
  ring

/-- Power-reduction ladder for `√5` (the fiber closers unfold `φ` to
`(1+√5)/2` and reduce in the `√5`-atom). -/
theorem sqrt5_sq : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem sqrt5_pow3 : (√5 : ℝ) ^ 3 = 5 * √5 := by
  linear_combination (√5 : ℝ) * sqrt5_sq

theorem sqrt5_pow4 : (√5 : ℝ) ^ 4 = 25 := by
  linear_combination ((√5 : ℝ) ^ 2 + 5) * sqrt5_sq

theorem sqrt5_pow5 : (√5 : ℝ) ^ 5 = 25 * √5 := by
  linear_combination ((√5 : ℝ) ^ 3 + 5 * √5) * sqrt5_sq

/-- `φ·(φ - 1) = 1`: the golden-ratio inverse, used to eliminate the
`1/S_{0l}` column denominators. -/
theorem phi_mul_phi_sub_one : goldenRatio * (goldenRatio - 1) = 1 := by
  linear_combination Real.goldenRatio_sq

/-- Column quotient through a vacuum-row entry `1`. -/
theorem verlinde_quot_k3_one (x y z : ℝ) :
    lam_k3 * x * (lam_k3 * y) * (lam_k3 * z) / (lam_k3 * 1) =
    (3 - goldenRatio) / 10 * (x * y * z * 1) := by
  rw [div_eq_iff (mul_pos lam_k3_pos one_pos).ne']
  linear_combination (lam_k3 * x * y * z) * lam_k3_sq

/-- Column quotient through a vacuum-row entry `φ` (exact inverse `φ - 1`). -/
theorem verlinde_quot_k3_phi (x y z : ℝ) :
    lam_k3 * x * (lam_k3 * y) * (lam_k3 * z) / (lam_k3 * goldenRatio) =
    (3 - goldenRatio) / 10 * (x * y * z * (goldenRatio - 1)) := by
  rw [div_eq_iff (mul_pos lam_k3_pos Real.goldenRatio_pos).ne']
  linear_combination (lam_k3 * x * y * z) * lam_k3_sq -
    ((3 - goldenRatio) / 10 * x * y * z * lam_k3) * phi_mul_phi_sub_one

/-! Entry projection `rfl`-lemmas for `M_k3` (the QCyc5 `powerTable` pattern):
    registering each literal entry once lets every fiber proof below run on
    cheap named rewrites instead of matrix-literal `cons` unfolding. -/

theorem M_k3_0_0 : M_k3 0 0 = 1 := rfl
theorem M_k3_0_1 : M_k3 0 1 = goldenRatio := rfl
theorem M_k3_0_2 : M_k3 0 2 = goldenRatio := rfl
theorem M_k3_0_3 : M_k3 0 3 = 1 := rfl
theorem M_k3_1_0 : M_k3 1 0 = goldenRatio := rfl
theorem M_k3_1_1 : M_k3 1 1 = 1 := rfl
theorem M_k3_1_2 : M_k3 1 2 = -1 := rfl
theorem M_k3_1_3 : M_k3 1 3 = -goldenRatio := rfl
theorem M_k3_2_0 : M_k3 2 0 = goldenRatio := rfl
theorem M_k3_2_1 : M_k3 2 1 = -1 := rfl
theorem M_k3_2_2 : M_k3 2 2 = -1 := rfl
theorem M_k3_2_3 : M_k3 2 3 = goldenRatio := rfl
theorem M_k3_3_0 : M_k3 3 0 = 1 := rfl
theorem M_k3_3_1 : M_k3 3 1 = -goldenRatio := rfl
theorem M_k3_3_2 : M_k3 3 2 = goldenRatio := rfl
theorem M_k3_3_3 : M_k3 3 3 = -1 := rfl

/-- Factorization of the Verlinde sum at k=3: every column quotient
`S_(i l) S_(j l) S_(m l) / S_(0 l)` carries exactly two powers of the overall
scale `lam_k3`, so the whole sum reduces to `lam_k3^2` times a polynomial in
the ratio-matrix entries, with the column inverses `1 / M_k3 0 l` replaced by
their exact algebraic forms. This is the single lemma through which all
64 fiber identities below are routed. -/
theorem verlinde_sum_k3 (i j m : Fin 4) :
    ∑ l : Fin 4, S_k3 i l * S_k3 j l * S_k3 m l / S_k3 0 l =
    (3 - goldenRatio) / 10 *
    (      M_k3 i 0 * M_k3 j 0 * M_k3 m 0 * 1 +
      M_k3 i 1 * M_k3 j 1 * M_k3 m 1 * (goldenRatio - 1) +
      M_k3 i 2 * M_k3 j 2 * M_k3 m 2 * (goldenRatio - 1) +
      M_k3 i 3 * M_k3 j 3 * M_k3 m 3 * 1) := by
  simp only [S_k3, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  rw [show M_k3 0 0 = 1 from rfl,
      show M_k3 0 1 = goldenRatio from rfl,
      show M_k3 0 2 = goldenRatio from rfl,
      show M_k3 0 3 = 1 from rfl]
  rw [verlinde_quot_k3_one, verlinde_quot_k3_phi, verlinde_quot_k3_phi, verlinde_quot_k3_one]
  ring

/-- Verlinde formula at k=3, fiber (i,j) = (0,0):
`N_(00)^m = Σ_l S_(0l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_0 = V_0), verified against `su2kFusion 3 0 0 m`. -/
theorem verlinde_k3_0_0 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 0 l * S_k3 0 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 0 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (0,1):
`N_(01)^m = Σ_l S_(0l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_1 = V_1), verified against `su2kFusion 3 0 1 m`. -/
theorem verlinde_k3_0_1 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 0 l * S_k3 1 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 0 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (0,2):
`N_(02)^m = Σ_l S_(0l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_2 = V_2), verified against `su2kFusion 3 0 2 m`. -/
theorem verlinde_k3_0_2 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 0 l * S_k3 2 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 0 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (0,3):
`N_(03)^m = Σ_l S_(0l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_3 = V_3), verified against `su2kFusion 3 0 3 m`. -/
theorem verlinde_k3_0_3 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 0 l * S_k3 3 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 0 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (1,0):
`N_(10)^m = Σ_l S_(1l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_0 = V_1), verified against `su2kFusion 3 1 0 m`. -/
theorem verlinde_k3_1_0 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 1 l * S_k3 0 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 1 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (1,1):
`N_(11)^m = Σ_l S_(1l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_1 = V_0 ⊕ V_2), verified against `su2kFusion 3 1 1 m`. -/
theorem verlinde_k3_1_1 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 1 l * S_k3 1 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 1 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (1,2):
`N_(12)^m = Σ_l S_(1l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_2 = V_1 ⊕ V_3), verified against `su2kFusion 3 1 2 m`. -/
theorem verlinde_k3_1_2 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 1 l * S_k3 2 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 1 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (1,3):
`N_(13)^m = Σ_l S_(1l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_3 = V_2), verified against `su2kFusion 3 1 3 m`. -/
theorem verlinde_k3_1_3 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 1 l * S_k3 3 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 1 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (2,0):
`N_(20)^m = Σ_l S_(2l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_0 = V_2), verified against `su2kFusion 3 2 0 m`. -/
theorem verlinde_k3_2_0 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 2 l * S_k3 0 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 2 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (2,1):
`N_(21)^m = Σ_l S_(2l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_1 = V_1 ⊕ V_3), verified against `su2kFusion 3 2 1 m`. -/
theorem verlinde_k3_2_1 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 2 l * S_k3 1 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 2 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (2,2):
`N_(22)^m = Σ_l S_(2l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_2 = V_0 ⊕ V_2), verified against `su2kFusion 3 2 2 m`. -/
theorem verlinde_k3_2_2 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 2 l * S_k3 2 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 2 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (2,3):
`N_(23)^m = Σ_l S_(2l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_3 = V_1), verified against `su2kFusion 3 2 3 m`. -/
theorem verlinde_k3_2_3 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 2 l * S_k3 3 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 2 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (3,0):
`N_(30)^m = Σ_l S_(3l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_0 = V_3), verified against `su2kFusion 3 3 0 m`. -/
theorem verlinde_k3_3_0 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 3 l * S_k3 0 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 3 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (3,1):
`N_(31)^m = Σ_l S_(3l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_1 = V_2), verified against `su2kFusion 3 3 1 m`. -/
theorem verlinde_k3_3_1 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 3 l * S_k3 1 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 3 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (3,2):
`N_(32)^m = Σ_l S_(3l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_2 = V_1), verified against `su2kFusion 3 3 2 m`. -/
theorem verlinde_k3_3_2 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 3 l * S_k3 2 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 3 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=3, fiber (i,j) = (3,3):
`N_(33)^m = Σ_l S_(3l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_3 = V_0), verified against `su2kFusion 3 3 3 m`. -/
theorem verlinde_k3_3_3 (m' : Fin 4) :
    ∑ l : Fin 4, S_k3 3 l * S_k3 3 l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 3 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 := by revert m'; decide
  rw [verlinde_sum_k3]
  rcases hm with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- **Verlinde formula at k = 3, full fusion table** (4³ = 64 identities):
the modular S-matrix diagonalizes the fusion rules,
`N_(ij)^m = Σ_l S_(il) S_(jl) conj(S_(ml)) / S_(0l)` (S real symmetric here, so
conj(S) = S), verified for ALL (i, j, m) against the `su2kFusion` coefficients
of `SU2kFusion.lean`. Assembled from the 16 fiber theorems above. -/
theorem verlinde_k3_full (i j m' : Fin 4) :
    ∑ l : Fin 4, S_k3 i l * S_k3 j l * S_k3 m' l / S_k3 0 l =
    (su2kFusion 3 i j m' : ℝ) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
  · exact verlinde_k3_0_0 m'
  · exact verlinde_k3_0_1 m'
  · exact verlinde_k3_0_2 m'
  · exact verlinde_k3_0_3 m'
  · exact verlinde_k3_1_0 m'
  · exact verlinde_k3_1_1 m'
  · exact verlinde_k3_1_2 m'
  · exact verlinde_k3_1_3 m'
  · exact verlinde_k3_2_0 m'
  · exact verlinde_k3_2_1 m'
  · exact verlinde_k3_2_2 m'
  · exact verlinde_k3_2_3 m'
  · exact verlinde_k3_3_0 m'
  · exact verlinde_k3_3_1 m'
  · exact verlinde_k3_3_2 m'
  · exact verlinde_k3_3_3 m'

/-- Pair-product factorization for unitarity at k=3. -/
theorem unitary_sum_k3 (i j : Fin 4) :
    ∑ l : Fin 4, S_k3 i l * S_k3 j l =
    (3 - goldenRatio) / 10 *
    (M_k3 i 0 * M_k3 j 0 +
      M_k3 i 1 * M_k3 j 1 +
      M_k3 i 2 * M_k3 j 2 +
      M_k3 i 3 * M_k3 j 3) := by
  simp only [S_k3, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  linear_combination
    (M_k3 i 0 * M_k3 j 0 + M_k3 i 1 * M_k3 j 1 + M_k3 i 2 * M_k3 j 2 + M_k3 i 3 * M_k3 j 3) * lam_k3_sq

theorem S_k3_unitary_row0 (j : Fin 4) :
    ∑ l : Fin 4, S_k3 0 l * S_k3 j l = if (0 : Fin 4) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
  rw [unitary_sum_k3]
  rcases hj with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k3_unitary_row1 (j : Fin 4) :
    ∑ l : Fin 4, S_k3 1 l * S_k3 j l = if (1 : Fin 4) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
  rw [unitary_sum_k3]
  rcases hj with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k3_unitary_row2 (j : Fin 4) :
    ∑ l : Fin 4, S_k3 2 l * S_k3 j l = if (2 : Fin 4) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
  rw [unitary_sum_k3]
  rcases hj with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k3_unitary_row3 (j : Fin 4) :
    ∑ l : Fin 4, S_k3 3 l * S_k3 j l = if (3 : Fin 4) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
  rw [unitary_sum_k3]
  rcases hj with rfl | rfl | rfl | rfl <;>
    (simp only [M_k3_0_0, M_k3_0_1, M_k3_0_2, M_k3_0_3, M_k3_1_0, M_k3_1_1, M_k3_1_2, M_k3_1_3, M_k3_2_0, M_k3_2_1, M_k3_2_2, M_k3_2_3, M_k3_3_0, M_k3_3_1, M_k3_3_2, M_k3_3_3, show goldenRatio = (1 + √5) / 2 from rfl];
     ring_nf;
     try simp only [sqrt5_sq, sqrt5_pow3, sqrt5_pow4, sqrt5_pow5];
     try ring_nf;
     norm_num;
     try decide)

/-- Unitarity at k=3: S Sᵀ = I (4×4). Together with `S_k3_det_ne_zero`
this is the modularity (non-degeneracy) condition for the SU(2)_3 MTC. -/
theorem S_k3_unitary : S_k3 * S_k3.transpose = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl
  · exact S_k3_unitary_row0 j
  · exact S_k3_unitary_row1 j
  · exact S_k3_unitary_row2 j
  · exact S_k3_unitary_row3 j

/-- Modularity at k=3: det S ≠ 0 (follows from unitarity: (det S)² = 1). -/
theorem S_k3_det_ne_zero : S_k3.det ≠ 0 := by
  intro h
  have h1 : S_k3.det * S_k3.det = 1 := by
    have h2 := congrArg Matrix.det S_k3_unitary
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  rw [h] at h1
  norm_num at h1

/-- The k=3 S-matrix is symmetric. -/
theorem S_k3_symmetric : S_k3.transpose = S_k3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `λ₃ = √(2/5)·sin(π/5)`: the radical scale equals the literal trigonometric
scale of the Kac–Peterson formula (both sides are nonnegative and have square
`(5-√5)/20`, using `cos(π/5) = (1+√5)/4`). -/
theorem lam_k3_eq_sin : lam_k3 = √(2 / 5) * Real.sin (π / 5) := by
  have hpos : 0 ≤ √(2 / 5) * Real.sin (π / 5) := by
    have hs : 0 < Real.sin (π / 5) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    positivity
  have hsq : (√(2 / 5) * Real.sin (π / 5)) ^ 2 = (5 - √5) / 20 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2 / 5), Real.sin_sq,
        Real.cos_pi_div_five]
    linear_combination (-(1 : ℝ) / 40) * sqrt5_sq
  rw [lam_k3, ← hsq, Real.sqrt_sq hpos]

/-- **Row-0 faithfulness at k=3**: the quantum-dimension row of `S_k3` equals
the literal trigonometric values `√(2/5)·sin((b+1)π/5)` of the Kac–Peterson
S-matrix. (Row 0 pins the normalization and the quantum dimensions
`d_b = S_{0b}/S_{00}`; the remaining rows reduce by the same `sin`
periodicity/reflection identities.) -/
theorem S_k3_row0_sin (b : Fin 4) :
    S_k3 0 b = √(2 / 5) * Real.sin (((b.val : ℝ) + 1) * (π / 5)) := by
  have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by revert b; decide
  rcases hb with rfl | rfl | rfl | rfl
  · simp only [S_k3, Matrix.smul_apply, smul_eq_mul, M_k3_0_0]
    rw [show (((0 : Fin 4).val : ℝ) + 1) * (π / 5) = π / 5 by norm_num, mul_one,
        lam_k3_eq_sin]
  · simp only [S_k3, Matrix.smul_apply, smul_eq_mul, M_k3_0_1]
    rw [show (((1 : Fin 4).val : ℝ) + 1) * (π / 5) = 2 * (π / 5) by norm_num,
        Real.sin_two_mul, Real.cos_pi_div_five, lam_k3_eq_sin,
        show goldenRatio = (1 + √5) / 2 from rfl]
    ring
  · simp only [S_k3, Matrix.smul_apply, smul_eq_mul, M_k3_0_2]
    rw [show (((2 : Fin 4).val : ℝ) + 1) * (π / 5) = π - 2 * (π / 5) by
          rw [show ((2 : Fin 4).val) = 2 from rfl]; push_cast; ring,
        Real.sin_pi_sub, Real.sin_two_mul, Real.cos_pi_div_five, lam_k3_eq_sin,
        show goldenRatio = (1 + √5) / 2 from rfl]
    ring
  · simp only [S_k3, Matrix.smul_apply, smul_eq_mul, M_k3_0_3]
    rw [show (((3 : Fin 4).val : ℝ) + 1) * (π / 5) = π - π / 5 by
          rw [show ((3 : Fin 4).val) = 3 from rfl]; push_cast; ring,
        Real.sin_pi_sub, mul_one, lam_k3_eq_sin]

end Level3

/-! ## 4. SU(2)_4 S-matrix (5×5, ℚ(√3) entries) and full Verlinde formula

`S_{ab} = √(2/6)·sin((a+1)(b+1)π/6)` for `a, b = 0..4`; the scale is
`λ₄ = √(2/6)·sin(π/6) = 1/(2√3)` and the ratio matrix `M_k4` has entries in
`{0, ±1, ±2, ±√3}` (Chebyshev values `U_n(cos π/6)`: `1, √3, 2, √3, 1`).
All Verlinde arithmetic lives in `ℚ(√3)`, reduced by `(√3)² = 3`.
This directly extends the k=2 Ising pattern (`ℚ(√2)` entries) one level up.
The first row is tied to the trigonometric form by `S_k4_row0_sin`. -/

section Level4

/-- Overall scale of the SU(2)₄ S-matrix: `λ₄ = 1/(2√3) = √(2/6)·sin(π/6)`
(see `lam_k4_eq_sin`). -/
noncomputable def lam_k4 : ℝ := 1 / (2 * √3)

/-- Ratio matrix at k=4: `M_k4 a b = sin((a+1)(b+1)π/6)/sin(π/6)`. -/
noncomputable def M_k4 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1,   √3,  2,  √3,  1;
     √3,  √3,  0,  -√3, -√3;
     2,   0,   -2, 0,   2;
     √3,  -√3, 0,  √3,  -√3;
     1,   -√3, 2,  -√3, 1]

/-- The SU(2)₄ modular S-matrix: `S = λ₄ • M_k4`. -/
noncomputable def S_k4 : Matrix (Fin 5) (Fin 5) ℝ := lam_k4 • M_k4

theorem sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt3_pow3 : (√3 : ℝ) ^ 3 = 3 * √3 := by rw [pow_succ, sqrt3_sq]

theorem sqrt3_pow4 : (√3 : ℝ) ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sqrt3_sq]; norm_num

theorem sqrt3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)

theorem lam_k4_pos : 0 < lam_k4 := by unfold lam_k4; positivity

/-- `λ₄² = 1/12` — rational, since `sin(π/6) = 1/2` is rational. -/
theorem lam_k4_sq : lam_k4 ^ 2 = 1 / 12 := by
  unfold lam_k4; rw [div_pow, mul_pow, sqrt3_sq]; norm_num

/-- Column quotient through a vacuum-row entry `1`. -/
theorem verlinde_quot_k4_one (x y z : ℝ) :
    lam_k4 * x * (lam_k4 * y) * (lam_k4 * z) / (lam_k4 * 1) =
    1 / 12 * (x * y * z * 1) := by
  rw [div_eq_iff (mul_pos lam_k4_pos one_pos).ne']
  linear_combination (lam_k4 * x * y * z) * lam_k4_sq

/-- Column quotient through a vacuum-row entry `√3` (exact inverse `√3/3`). -/
theorem verlinde_quot_k4_sqrt3 (x y z : ℝ) :
    lam_k4 * x * (lam_k4 * y) * (lam_k4 * z) / (lam_k4 * √3) =
    1 / 12 * (x * y * z * (√3 / 3)) := by
  rw [div_eq_iff (mul_pos lam_k4_pos sqrt3_pos).ne']
  linear_combination (lam_k4 * x * y * z) * lam_k4_sq -
    (1 / 36 * x * y * z * lam_k4) * sqrt3_sq

/-- Column quotient through a vacuum-row entry `2`. -/
theorem verlinde_quot_k4_two (x y z : ℝ) :
    lam_k4 * x * (lam_k4 * y) * (lam_k4 * z) / (lam_k4 * 2) =
    1 / 12 * (x * y * z * (1 / 2)) := by
  rw [div_eq_iff (mul_pos lam_k4_pos two_pos).ne']
  linear_combination (lam_k4 * x * y * z) * lam_k4_sq

/-! Entry projection `rfl`-lemmas for `M_k4` (the QCyc5 `powerTable` pattern):
    registering each literal entry once lets every fiber proof below run on
    cheap named rewrites instead of matrix-literal `cons` unfolding. -/

theorem M_k4_0_0 : M_k4 0 0 = 1 := rfl
theorem M_k4_0_1 : M_k4 0 1 = √3 := rfl
theorem M_k4_0_2 : M_k4 0 2 = 2 := rfl
theorem M_k4_0_3 : M_k4 0 3 = √3 := rfl
theorem M_k4_0_4 : M_k4 0 4 = 1 := rfl
theorem M_k4_1_0 : M_k4 1 0 = √3 := rfl
theorem M_k4_1_1 : M_k4 1 1 = √3 := rfl
theorem M_k4_1_2 : M_k4 1 2 = 0 := rfl
theorem M_k4_1_3 : M_k4 1 3 = -√3 := rfl
theorem M_k4_1_4 : M_k4 1 4 = -√3 := rfl
theorem M_k4_2_0 : M_k4 2 0 = 2 := rfl
theorem M_k4_2_1 : M_k4 2 1 = 0 := rfl
theorem M_k4_2_2 : M_k4 2 2 = -2 := rfl
theorem M_k4_2_3 : M_k4 2 3 = 0 := rfl
theorem M_k4_2_4 : M_k4 2 4 = 2 := rfl
theorem M_k4_3_0 : M_k4 3 0 = √3 := rfl
theorem M_k4_3_1 : M_k4 3 1 = -√3 := rfl
theorem M_k4_3_2 : M_k4 3 2 = 0 := rfl
theorem M_k4_3_3 : M_k4 3 3 = √3 := rfl
theorem M_k4_3_4 : M_k4 3 4 = -√3 := rfl
theorem M_k4_4_0 : M_k4 4 0 = 1 := rfl
theorem M_k4_4_1 : M_k4 4 1 = -√3 := rfl
theorem M_k4_4_2 : M_k4 4 2 = 2 := rfl
theorem M_k4_4_3 : M_k4 4 3 = -√3 := rfl
theorem M_k4_4_4 : M_k4 4 4 = 1 := rfl

/-- Factorization of the Verlinde sum at k=4: every column quotient
`S_(i l) S_(j l) S_(m l) / S_(0 l)` carries exactly two powers of the overall
scale `lam_k4`, so the whole sum reduces to `lam_k4^2` times a polynomial in
the ratio-matrix entries, with the column inverses `1 / M_k4 0 l` replaced by
their exact algebraic forms. This is the single lemma through which all
125 fiber identities below are routed. -/
theorem verlinde_sum_k4 (i j m : Fin 5) :
    ∑ l : Fin 5, S_k4 i l * S_k4 j l * S_k4 m l / S_k4 0 l =
    1 / 12 *
    (      M_k4 i 0 * M_k4 j 0 * M_k4 m 0 * 1 +
      M_k4 i 1 * M_k4 j 1 * M_k4 m 1 * (√3 / 3) +
      M_k4 i 2 * M_k4 j 2 * M_k4 m 2 * (1 / 2) +
      M_k4 i 3 * M_k4 j 3 * M_k4 m 3 * (√3 / 3) +
      M_k4 i 4 * M_k4 j 4 * M_k4 m 4 * 1) := by
  simp only [S_k4, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_five]
  rw [show M_k4 0 0 = 1 from rfl,
      show M_k4 0 1 = √3 from rfl,
      show M_k4 0 2 = 2 from rfl,
      show M_k4 0 3 = √3 from rfl,
      show M_k4 0 4 = 1 from rfl]
  rw [verlinde_quot_k4_one, verlinde_quot_k4_sqrt3, verlinde_quot_k4_two, verlinde_quot_k4_sqrt3, verlinde_quot_k4_one]
  ring

/-- Verlinde formula at k=4, fiber (i,j) = (0,0):
`N_(00)^m = Σ_l S_(0l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_0 = V_0), verified against `su2kFusion 4 0 0 m`. -/
theorem verlinde_k4_0_0 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 0 l * S_k4 0 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 0 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (0,1):
`N_(01)^m = Σ_l S_(0l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_1 = V_1), verified against `su2kFusion 4 0 1 m`. -/
theorem verlinde_k4_0_1 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 0 l * S_k4 1 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 0 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (0,2):
`N_(02)^m = Σ_l S_(0l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_2 = V_2), verified against `su2kFusion 4 0 2 m`. -/
theorem verlinde_k4_0_2 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 0 l * S_k4 2 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 0 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (0,3):
`N_(03)^m = Σ_l S_(0l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_3 = V_3), verified against `su2kFusion 4 0 3 m`. -/
theorem verlinde_k4_0_3 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 0 l * S_k4 3 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 0 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (0,4):
`N_(04)^m = Σ_l S_(0l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_4 = V_4), verified against `su2kFusion 4 0 4 m`. -/
theorem verlinde_k4_0_4 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 0 l * S_k4 4 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 0 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (1,0):
`N_(10)^m = Σ_l S_(1l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_0 = V_1), verified against `su2kFusion 4 1 0 m`. -/
theorem verlinde_k4_1_0 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 1 l * S_k4 0 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 1 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (1,1):
`N_(11)^m = Σ_l S_(1l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_1 = V_0 ⊕ V_2), verified against `su2kFusion 4 1 1 m`. -/
theorem verlinde_k4_1_1 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 1 l * S_k4 1 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 1 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (1,2):
`N_(12)^m = Σ_l S_(1l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_2 = V_1 ⊕ V_3), verified against `su2kFusion 4 1 2 m`. -/
theorem verlinde_k4_1_2 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 1 l * S_k4 2 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 1 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (1,3):
`N_(13)^m = Σ_l S_(1l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_3 = V_2 ⊕ V_4), verified against `su2kFusion 4 1 3 m`. -/
theorem verlinde_k4_1_3 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 1 l * S_k4 3 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 1 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (1,4):
`N_(14)^m = Σ_l S_(1l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_4 = V_3), verified against `su2kFusion 4 1 4 m`. -/
theorem verlinde_k4_1_4 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 1 l * S_k4 4 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 1 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (2,0):
`N_(20)^m = Σ_l S_(2l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_0 = V_2), verified against `su2kFusion 4 2 0 m`. -/
theorem verlinde_k4_2_0 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 2 l * S_k4 0 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 2 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (2,1):
`N_(21)^m = Σ_l S_(2l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_1 = V_1 ⊕ V_3), verified against `su2kFusion 4 2 1 m`. -/
theorem verlinde_k4_2_1 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 2 l * S_k4 1 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 2 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (2,2):
`N_(22)^m = Σ_l S_(2l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_2 = V_0 ⊕ V_2 ⊕ V_4), verified against `su2kFusion 4 2 2 m`. -/
theorem verlinde_k4_2_2 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 2 l * S_k4 2 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 2 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (2,3):
`N_(23)^m = Σ_l S_(2l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_3 = V_1 ⊕ V_3), verified against `su2kFusion 4 2 3 m`. -/
theorem verlinde_k4_2_3 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 2 l * S_k4 3 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 2 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (2,4):
`N_(24)^m = Σ_l S_(2l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_4 = V_2), verified against `su2kFusion 4 2 4 m`. -/
theorem verlinde_k4_2_4 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 2 l * S_k4 4 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 2 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (3,0):
`N_(30)^m = Σ_l S_(3l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_0 = V_3), verified against `su2kFusion 4 3 0 m`. -/
theorem verlinde_k4_3_0 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 3 l * S_k4 0 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 3 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (3,1):
`N_(31)^m = Σ_l S_(3l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_1 = V_2 ⊕ V_4), verified against `su2kFusion 4 3 1 m`. -/
theorem verlinde_k4_3_1 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 3 l * S_k4 1 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 3 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (3,2):
`N_(32)^m = Σ_l S_(3l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_2 = V_1 ⊕ V_3), verified against `su2kFusion 4 3 2 m`. -/
theorem verlinde_k4_3_2 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 3 l * S_k4 2 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 3 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (3,3):
`N_(33)^m = Σ_l S_(3l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_3 = V_0 ⊕ V_2), verified against `su2kFusion 4 3 3 m`. -/
theorem verlinde_k4_3_3 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 3 l * S_k4 3 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 3 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (3,4):
`N_(34)^m = Σ_l S_(3l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_4 = V_1), verified against `su2kFusion 4 3 4 m`. -/
theorem verlinde_k4_3_4 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 3 l * S_k4 4 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 3 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (4,0):
`N_(40)^m = Σ_l S_(4l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_0 = V_4), verified against `su2kFusion 4 4 0 m`. -/
theorem verlinde_k4_4_0 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 4 l * S_k4 0 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 4 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (4,1):
`N_(41)^m = Σ_l S_(4l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_1 = V_3), verified against `su2kFusion 4 4 1 m`. -/
theorem verlinde_k4_4_1 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 4 l * S_k4 1 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 4 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (4,2):
`N_(42)^m = Σ_l S_(4l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_2 = V_2), verified against `su2kFusion 4 4 2 m`. -/
theorem verlinde_k4_4_2 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 4 l * S_k4 2 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 4 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (4,3):
`N_(43)^m = Σ_l S_(4l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_3 = V_1), verified against `su2kFusion 4 4 3 m`. -/
theorem verlinde_k4_4_3 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 4 l * S_k4 3 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 4 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=4, fiber (i,j) = (4,4):
`N_(44)^m = Σ_l S_(4l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_4 = V_0), verified against `su2kFusion 4 4 4 m`. -/
theorem verlinde_k4_4_4 (m' : Fin 5) :
    ∑ l : Fin 5, S_k4 4 l * S_k4 4 l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 4 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 := by revert m'; decide
  rw [verlinde_sum_k4]
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- **Verlinde formula at k = 4, full fusion table** (5³ = 125 identities):
the modular S-matrix diagonalizes the fusion rules,
`N_(ij)^m = Σ_l S_(il) S_(jl) conj(S_(ml)) / S_(0l)` (S real symmetric here, so
conj(S) = S), verified for ALL (i, j, m) against the `su2kFusion` coefficients
of `SU2kFusion.lean`. Assembled from the 25 fiber theorems above. -/
theorem verlinde_k4_full (i j m' : Fin 5) :
    ∑ l : Fin 5, S_k4 i l * S_k4 j l * S_k4 m' l / S_k4 0 l =
    (su2kFusion 4 i j m' : ℝ) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact verlinde_k4_0_0 m'
  · exact verlinde_k4_0_1 m'
  · exact verlinde_k4_0_2 m'
  · exact verlinde_k4_0_3 m'
  · exact verlinde_k4_0_4 m'
  · exact verlinde_k4_1_0 m'
  · exact verlinde_k4_1_1 m'
  · exact verlinde_k4_1_2 m'
  · exact verlinde_k4_1_3 m'
  · exact verlinde_k4_1_4 m'
  · exact verlinde_k4_2_0 m'
  · exact verlinde_k4_2_1 m'
  · exact verlinde_k4_2_2 m'
  · exact verlinde_k4_2_3 m'
  · exact verlinde_k4_2_4 m'
  · exact verlinde_k4_3_0 m'
  · exact verlinde_k4_3_1 m'
  · exact verlinde_k4_3_2 m'
  · exact verlinde_k4_3_3 m'
  · exact verlinde_k4_3_4 m'
  · exact verlinde_k4_4_0 m'
  · exact verlinde_k4_4_1 m'
  · exact verlinde_k4_4_2 m'
  · exact verlinde_k4_4_3 m'
  · exact verlinde_k4_4_4 m'

/-- Pair-product factorization for unitarity at k=4. -/
theorem unitary_sum_k4 (i j : Fin 5) :
    ∑ l : Fin 5, S_k4 i l * S_k4 j l =
    1 / 12 *
    (M_k4 i 0 * M_k4 j 0 +
      M_k4 i 1 * M_k4 j 1 +
      M_k4 i 2 * M_k4 j 2 +
      M_k4 i 3 * M_k4 j 3 +
      M_k4 i 4 * M_k4 j 4) := by
  simp only [S_k4, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_five]
  linear_combination
    (M_k4 i 0 * M_k4 j 0 + M_k4 i 1 * M_k4 j 1 + M_k4 i 2 * M_k4 j 2 + M_k4 i 3 * M_k4 j 3 + M_k4 i 4 * M_k4 j 4) * lam_k4_sq

theorem S_k4_unitary_row0 (j : Fin 5) :
    ∑ l : Fin 5, S_k4 0 l * S_k4 j l = if (0 : Fin 5) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rw [unitary_sum_k4]
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k4_unitary_row1 (j : Fin 5) :
    ∑ l : Fin 5, S_k4 1 l * S_k4 j l = if (1 : Fin 5) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rw [unitary_sum_k4]
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k4_unitary_row2 (j : Fin 5) :
    ∑ l : Fin 5, S_k4 2 l * S_k4 j l = if (2 : Fin 5) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rw [unitary_sum_k4]
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k4_unitary_row3 (j : Fin 5) :
    ∑ l : Fin 5, S_k4 3 l * S_k4 j l = if (3 : Fin 5) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rw [unitary_sum_k4]
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k4_unitary_row4 (j : Fin 5) :
    ∑ l : Fin 5, S_k4 4 l * S_k4 j l = if (4 : Fin 5) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rw [unitary_sum_k4]
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k4_0_0, M_k4_0_1, M_k4_0_2, M_k4_0_3, M_k4_0_4, M_k4_1_0, M_k4_1_1, M_k4_1_2, M_k4_1_3, M_k4_1_4, M_k4_2_0, M_k4_2_1, M_k4_2_2, M_k4_2_3, M_k4_2_4, M_k4_3_0, M_k4_3_1, M_k4_3_2, M_k4_3_3, M_k4_3_4, M_k4_4_0, M_k4_4_1, M_k4_4_2, M_k4_4_3, M_k4_4_4];
     ring_nf;
     try simp only [sqrt3_sq, sqrt3_pow3, sqrt3_pow4];
     try ring_nf;
     norm_num;
     try decide)

/-- Unitarity at k=4: S Sᵀ = I (5×5). Together with `S_k4_det_ne_zero`
this is the modularity (non-degeneracy) condition for the SU(2)_4 MTC. -/
theorem S_k4_unitary : S_k4 * S_k4.transpose = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact S_k4_unitary_row0 j
  · exact S_k4_unitary_row1 j
  · exact S_k4_unitary_row2 j
  · exact S_k4_unitary_row3 j
  · exact S_k4_unitary_row4 j

/-- Modularity at k=4: det S ≠ 0 (follows from unitarity: (det S)² = 1). -/
theorem S_k4_det_ne_zero : S_k4.det ≠ 0 := by
  intro h
  have h1 : S_k4.det * S_k4.det = 1 := by
    have h2 := congrArg Matrix.det S_k4_unitary
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  rw [h] at h1
  norm_num at h1

/-- The k=4 S-matrix is symmetric. -/
theorem S_k4_symmetric : S_k4.transpose = S_k4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `λ₄ = √(2/6)·sin(π/6)`: the radical scale equals the literal trigonometric
scale of the Kac–Peterson formula. -/
theorem lam_k4_eq_sin : lam_k4 = √(2 / 6) * Real.sin (π / 6) := by
  rw [Real.sin_pi_div_six, lam_k4,
      show (2 : ℝ) / 6 = (3 : ℝ)⁻¹ by norm_num, Real.sqrt_inv]
  field_simp

/-- **Row-0 faithfulness at k=4**: the quantum-dimension row of `S_k4` equals
the literal trigonometric values `√(2/6)·sin((b+1)π/6)` of the Kac–Peterson
S-matrix. -/
theorem S_k4_row0_sin (b : Fin 5) :
    S_k4 0 b = √(2 / 6) * Real.sin (((b.val : ℝ) + 1) * (π / 6)) := by
  have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by revert b; decide
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · simp only [S_k4, Matrix.smul_apply, smul_eq_mul, M_k4_0_0]
    rw [show (((0 : Fin 5).val : ℝ) + 1) * (π / 6) = π / 6 by norm_num, mul_one,
        lam_k4_eq_sin]
  · simp only [S_k4, Matrix.smul_apply, smul_eq_mul, M_k4_0_1]
    rw [show (((1 : Fin 5).val : ℝ) + 1) * (π / 6) = π / 3 by
          rw [show ((1 : Fin 5).val) = 1 from rfl]; push_cast; ring,
        Real.sin_pi_div_three, lam_k4_eq_sin, Real.sin_pi_div_six]
    ring
  · simp only [S_k4, Matrix.smul_apply, smul_eq_mul, M_k4_0_2]
    rw [show (((2 : Fin 5).val : ℝ) + 1) * (π / 6) = π / 2 by
          rw [show ((2 : Fin 5).val) = 2 from rfl]; push_cast; ring,
        Real.sin_pi_div_two, lam_k4_eq_sin, Real.sin_pi_div_six]
    ring
  · simp only [S_k4, Matrix.smul_apply, smul_eq_mul, M_k4_0_3]
    rw [show (((3 : Fin 5).val : ℝ) + 1) * (π / 6) = π - π / 3 by
          rw [show ((3 : Fin 5).val) = 3 from rfl]; push_cast; ring,
        Real.sin_pi_sub, Real.sin_pi_div_three, lam_k4_eq_sin, Real.sin_pi_div_six]
    ring
  · simp only [S_k4, Matrix.smul_apply, smul_eq_mul, M_k4_0_4]
    rw [show (((4 : Fin 5).val : ℝ) + 1) * (π / 6) = π - π / 6 by
          rw [show ((4 : Fin 5).val) = 4 from rfl]; push_cast; ring,
        Real.sin_pi_sub, lam_k4_eq_sin, Real.sin_pi_div_six]
    ring

end Level4

/-! ## 5. SU(2)_5 exact S-matrix (6×6, ℚ(2cos(π/7)) entries) and full Verlinde formula

`S_{ab} = √(2/7)·sin((a+1)(b+1)π/7)` for `a, b = 0..5`. The entries live in
the degree-3 totally real subfield `ℚ(ζ₇)⁺ = ℚ(c₇)` with `c₇ = 2cos(π/7)` —
no quadratic radical form exists (casus irreducibilis), so the generator is
DEFINED as the trigonometric value and its cubic minimal polynomial
`c₇³ = c₇² + 2c₇ - 1` is PROVED from `cos(4π/7) = -cos(3π/7)` via the
double/triple-angle formulas and the factorization
`8y⁴ + 4y³ - 8y² - 3y + 1 = (y+1)(8y³ - 4y² - 4y + 1)`. The scale is
`λ₅ = √(2/7)·sin(π/7)` and the ratio matrix `M_k5` has the Chebyshev entries
`U_n(cos π/7) ∈ {±1, ±c₇, ±(c₇²-1)}`. Every Verlinde identity reduces modulo
the cubic by the power ladder `c7_pow4 … c7_pow10` (sympy-checked remainders;
each step is a one-line `linear_combination`, kernel-verified by `ring`).
The first row is tied to the trigonometric form by `S_k5_row0_sin`.

This complements the integer character-sum unitarity proof of Section 6
(`su2k5_unitarity`): here unitarity is re-proven for the literal real
S-matrix, and the full 216-entry Verlinde table is verified exactly. -/

section Level5Exact

/-- `c₇ = 2cos(π/7)`: generator of the totally real cubic subfield `ℚ(ζ₇)⁺`. -/
noncomputable def c7 : ℝ := 2 * Real.cos (π / 7)

/-- Overall scale of the SU(2)₅ S-matrix: `λ₅ = √(2/7)·sin(π/7)`. -/
noncomputable def lam_k5 : ℝ := √(2 / 7) * Real.sin (π / 7)

/-- Ratio matrix at k=5: `M_k5 a b = sin((a+1)(b+1)π/7)/sin(π/7)`, entries in
`{±1, ±c₇, ±(c₇²-1)}` via the Chebyshev recursion and sin reflection. -/
noncomputable def M_k5 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,        c7,           c7^2 - 1, c7^2 - 1,    c7,           1;
     c7,       c7^2 - 1,     1,        -1,          -(c7^2 - 1),  -c7;
     c7^2 - 1, 1,            -c7,      -c7,         1,            c7^2 - 1;
     c7^2 - 1, -1,           -c7,      c7,          1,            -(c7^2 - 1);
     c7,       -(c7^2 - 1),  1,        1,           -(c7^2 - 1),  c7;
     1,        -c7,          c7^2 - 1, -(c7^2 - 1), c7,           -1]

/-- The SU(2)₅ modular S-matrix: `S = λ₅ • M_k5`. -/
noncomputable def S_k5 : Matrix (Fin 6) (Fin 6) ℝ := lam_k5 • M_k5

/-- **Minimal polynomial of `c₇ = 2cos(π/7)`**: `c₇³ = c₇² + 2c₇ - 1`.
Proof: `cos(4θ) = cos(π - 3θ) = -cos(3θ)` at `θ = π/7`; expanding via
double/triple-angle gives the quartic `8y⁴ + 4y³ - 8y² - 3y + 1 = 0` for
`y = cos(π/7)`, which factors as `(y + 1)(8y³ - 4y² - 4y + 1)`; since
`cos(π/7) ≠ -1` the cubic factor vanishes. -/
theorem c7_cubed : c7 ^ 3 = c7 ^ 2 + 2 * c7 - 1 := by
  have hy : Real.cos (4 * (π / 7)) = -Real.cos (3 * (π / 7)) := by
    rw [show 4 * (π / 7) = π - 3 * (π / 7) by ring, Real.cos_pi_sub]
  rw [show 4 * (π / 7) = 2 * (2 * (π / 7)) by ring, Real.cos_two_mul,
      Real.cos_two_mul, Real.cos_three_mul] at hy
  have hyne : Real.cos (π / 7) + 1 ≠ 0 := by
    have : 0 < Real.cos (π / 7) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    linarith
  have hcubic : 8 * Real.cos (π / 7) ^ 3 - 4 * Real.cos (π / 7) ^ 2 -
      4 * Real.cos (π / 7) + 1 = 0 := by
    have hfac : (Real.cos (π / 7) + 1) *
        (8 * Real.cos (π / 7) ^ 3 - 4 * Real.cos (π / 7) ^ 2 -
          4 * Real.cos (π / 7) + 1) = 0 := by
      linear_combination hy
    exact (mul_eq_zero.mp hfac).resolve_left hyne
  unfold c7
  linear_combination hcubic

theorem c7_pos : 0 < c7 := by
  unfold c7
  have : 0 < Real.cos (π / 7) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  linarith

/-- `c₇ > 1` (from `cos(π/7) > cos(π/3) = 1/2` by strict antitonicity). -/
theorem one_lt_c7 : 1 < c7 := by
  unfold c7
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by positivity : (0:ℝ) ≤ π / 7) (by linarith [Real.pi_pos] : π / 3 ≤ π)
    (by linarith [Real.pi_pos] : π / 7 < π / 3)
  rw [Real.cos_pi_div_three] at h
  linarith

theorem c7sq_sub_one_pos : 0 < c7 ^ 2 - 1 := by nlinarith [one_lt_c7]

theorem lam_k5_pos : 0 < lam_k5 := by
  unfold lam_k5
  have hs : 0 < Real.sin (π / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hs

/-- `λ₅² = (4 - c₇²)/14` (from `sin² = 1 - cos²`; keeps all downstream
arithmetic in the single atom `c₇`). -/
theorem lam_k5_sq : lam_k5 ^ 2 = (4 - c7 ^ 2) / 14 := by
  unfold lam_k5 c7
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2 / 7), Real.sin_sq]
  ring

/-! Power-reduction ladder modulo `c₇³ = c₇² + 2c₇ - 1` (remainders
sympy-checked; each cofactor verified by the `ring` kernel check inside
`linear_combination`). Degree 10 suffices: fiber polynomials have degree
≤ 8 and the `λ₅²`-prefactor adds 2. -/

theorem c7_pow4 : c7 ^ 4 = 3 * c7 ^ 2 + c7 - 1 := by
  linear_combination (c7 + 1) * c7_cubed
theorem c7_pow5 : c7 ^ 5 = 4 * c7 ^ 2 + 5 * c7 - 3 := by
  linear_combination (c7 ^ 2 + c7 + 3) * c7_cubed
theorem c7_pow6 : c7 ^ 6 = 9 * c7 ^ 2 + 5 * c7 - 4 := by
  linear_combination (c7 ^ 3 + c7 ^ 2 + 3 * c7 + 4) * c7_cubed
theorem c7_pow7 : c7 ^ 7 = 14 * c7 ^ 2 + 14 * c7 - 9 := by
  linear_combination (c7 ^ 4 + c7 ^ 3 + 3 * c7 ^ 2 + 4 * c7 + 9) * c7_cubed
theorem c7_pow8 : c7 ^ 8 = 28 * c7 ^ 2 + 19 * c7 - 14 := by
  linear_combination (c7 ^ 5 + c7 ^ 4 + 3 * c7 ^ 3 + 4 * c7 ^ 2 + 9 * c7 + 14) * c7_cubed
theorem c7_pow9 : c7 ^ 9 = 47 * c7 ^ 2 + 42 * c7 - 28 := by
  linear_combination (c7 ^ 6 + c7 ^ 5 + 3 * c7 ^ 4 + 4 * c7 ^ 3 + 9 * c7 ^ 2 +
    14 * c7 + 28) * c7_cubed
theorem c7_pow10 : c7 ^ 10 = 89 * c7 ^ 2 + 66 * c7 - 47 := by
  linear_combination (c7 ^ 7 + c7 ^ 6 + 3 * c7 ^ 5 + 4 * c7 ^ 4 + 9 * c7 ^ 3 +
    14 * c7 ^ 2 + 28 * c7 + 47) * c7_cubed

/-- `c₇·(2 + c₇ - c₇²) = 1`: exact inverse of `c₇` in `ℚ(c₇)`. -/
theorem c7_inv : c7 * (2 + c7 - c7 ^ 2) = 1 := by linear_combination -c7_cubed

/-- `(c₇² - 1)·(c₇² - c₇ - 1) = 1`: exact inverse of `c₇² - 1` in `ℚ(c₇)`. -/
theorem c7sq_sub_one_inv : (c7 ^ 2 - 1) * (c7 ^ 2 - c7 - 1) = 1 := by
  linear_combination c7 * c7_cubed

/-- Column quotient through a vacuum-row entry `1`. -/
theorem verlinde_quot_k5_one (x y z : ℝ) :
    lam_k5 * x * (lam_k5 * y) * (lam_k5 * z) / (lam_k5 * 1) =
    (4 - c7 ^ 2) / 14 * (x * y * z * 1) := by
  rw [div_eq_iff (mul_pos lam_k5_pos one_pos).ne']
  linear_combination (lam_k5 * x * y * z) * lam_k5_sq

/-- Column quotient through a vacuum-row entry `c₇`. -/
theorem verlinde_quot_k5_c (x y z : ℝ) :
    lam_k5 * x * (lam_k5 * y) * (lam_k5 * z) / (lam_k5 * c7) =
    (4 - c7 ^ 2) / 14 * (x * y * z * (2 + c7 - c7 ^ 2)) := by
  rw [div_eq_iff (mul_pos lam_k5_pos c7_pos).ne']
  linear_combination (lam_k5 * x * y * z) * lam_k5_sq -
    ((4 - c7 ^ 2) / 14 * x * y * z * lam_k5) * c7_inv

/-- Column quotient through a vacuum-row entry `c₇² - 1`. -/
theorem verlinde_quot_k5_csq (x y z : ℝ) :
    lam_k5 * x * (lam_k5 * y) * (lam_k5 * z) / (lam_k5 * (c7 ^ 2 - 1)) =
    (4 - c7 ^ 2) / 14 * (x * y * z * (c7 ^ 2 - c7 - 1)) := by
  rw [div_eq_iff (mul_pos lam_k5_pos c7sq_sub_one_pos).ne']
  linear_combination (lam_k5 * x * y * z) * lam_k5_sq -
    ((4 - c7 ^ 2) / 14 * x * y * z * lam_k5) * c7sq_sub_one_inv

/-! Entry projection `rfl`-lemmas for `M_k5` (the QCyc5 `powerTable` pattern):
    registering each literal entry once lets every fiber proof below run on
    cheap named rewrites instead of matrix-literal `cons` unfolding. -/

theorem M_k5_0_0 : M_k5 0 0 = 1 := rfl
theorem M_k5_0_1 : M_k5 0 1 = c7 := rfl
theorem M_k5_0_2 : M_k5 0 2 = c7^2 - 1 := rfl
theorem M_k5_0_3 : M_k5 0 3 = c7^2 - 1 := rfl
theorem M_k5_0_4 : M_k5 0 4 = c7 := rfl
theorem M_k5_0_5 : M_k5 0 5 = 1 := rfl
theorem M_k5_1_0 : M_k5 1 0 = c7 := rfl
theorem M_k5_1_1 : M_k5 1 1 = c7^2 - 1 := rfl
theorem M_k5_1_2 : M_k5 1 2 = 1 := rfl
theorem M_k5_1_3 : M_k5 1 3 = -1 := rfl
theorem M_k5_1_4 : M_k5 1 4 = -(c7^2 - 1) := rfl
theorem M_k5_1_5 : M_k5 1 5 = -c7 := rfl
theorem M_k5_2_0 : M_k5 2 0 = c7^2 - 1 := rfl
theorem M_k5_2_1 : M_k5 2 1 = 1 := rfl
theorem M_k5_2_2 : M_k5 2 2 = -c7 := rfl
theorem M_k5_2_3 : M_k5 2 3 = -c7 := rfl
theorem M_k5_2_4 : M_k5 2 4 = 1 := rfl
theorem M_k5_2_5 : M_k5 2 5 = c7^2 - 1 := rfl
theorem M_k5_3_0 : M_k5 3 0 = c7^2 - 1 := rfl
theorem M_k5_3_1 : M_k5 3 1 = -1 := rfl
theorem M_k5_3_2 : M_k5 3 2 = -c7 := rfl
theorem M_k5_3_3 : M_k5 3 3 = c7 := rfl
theorem M_k5_3_4 : M_k5 3 4 = 1 := rfl
theorem M_k5_3_5 : M_k5 3 5 = -(c7^2 - 1) := rfl
theorem M_k5_4_0 : M_k5 4 0 = c7 := rfl
theorem M_k5_4_1 : M_k5 4 1 = -(c7^2 - 1) := rfl
theorem M_k5_4_2 : M_k5 4 2 = 1 := rfl
theorem M_k5_4_3 : M_k5 4 3 = 1 := rfl
theorem M_k5_4_4 : M_k5 4 4 = -(c7^2 - 1) := rfl
theorem M_k5_4_5 : M_k5 4 5 = c7 := rfl
theorem M_k5_5_0 : M_k5 5 0 = 1 := rfl
theorem M_k5_5_1 : M_k5 5 1 = -c7 := rfl
theorem M_k5_5_2 : M_k5 5 2 = c7^2 - 1 := rfl
theorem M_k5_5_3 : M_k5 5 3 = -(c7^2 - 1) := rfl
theorem M_k5_5_4 : M_k5 5 4 = c7 := rfl
theorem M_k5_5_5 : M_k5 5 5 = -1 := rfl

/-- Factorization of the Verlinde sum at k=5: every column quotient
`S_(i l) S_(j l) S_(m l) / S_(0 l)` carries exactly two powers of the overall
scale `lam_k5`, so the whole sum reduces to `lam_k5^2` times a polynomial in
the ratio-matrix entries, with the column inverses `1 / M_k5 0 l` replaced by
their exact algebraic forms. This is the single lemma through which all
216 fiber identities below are routed. -/
theorem verlinde_sum_k5 (i j m : Fin 6) :
    ∑ l : Fin 6, S_k5 i l * S_k5 j l * S_k5 m l / S_k5 0 l =
    (4 - c7 ^ 2) / 14 *
    (      M_k5 i 0 * M_k5 j 0 * M_k5 m 0 * 1 +
      M_k5 i 1 * M_k5 j 1 * M_k5 m 1 * (2 + c7 - c7 ^ 2) +
      M_k5 i 2 * M_k5 j 2 * M_k5 m 2 * (c7 ^ 2 - c7 - 1) +
      M_k5 i 3 * M_k5 j 3 * M_k5 m 3 * (c7 ^ 2 - c7 - 1) +
      M_k5 i 4 * M_k5 j 4 * M_k5 m 4 * (2 + c7 - c7 ^ 2) +
      M_k5 i 5 * M_k5 j 5 * M_k5 m 5 * 1) := by
  simp only [S_k5, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_six]
  rw [show M_k5 0 0 = 1 from rfl,
      show M_k5 0 1 = c7 from rfl,
      show M_k5 0 2 = c7^2 - 1 from rfl,
      show M_k5 0 3 = c7^2 - 1 from rfl,
      show M_k5 0 4 = c7 from rfl,
      show M_k5 0 5 = 1 from rfl]
  rw [verlinde_quot_k5_one, verlinde_quot_k5_c, verlinde_quot_k5_csq, verlinde_quot_k5_csq, verlinde_quot_k5_c, verlinde_quot_k5_one]
  ring

/-- Verlinde formula at k=5, fiber (i,j) = (0,0):
`N_(00)^m = Σ_l S_(0l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_0 = V_0), verified against `su2kFusion 5 0 0 m`. -/
theorem verlinde_k5_0_0 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 0 l * S_k5 0 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 0 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (0,1):
`N_(01)^m = Σ_l S_(0l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_1 = V_1), verified against `su2kFusion 5 0 1 m`. -/
theorem verlinde_k5_0_1 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 0 l * S_k5 1 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 0 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (0,2):
`N_(02)^m = Σ_l S_(0l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_2 = V_2), verified against `su2kFusion 5 0 2 m`. -/
theorem verlinde_k5_0_2 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 0 l * S_k5 2 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 0 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (0,3):
`N_(03)^m = Σ_l S_(0l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_3 = V_3), verified against `su2kFusion 5 0 3 m`. -/
theorem verlinde_k5_0_3 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 0 l * S_k5 3 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 0 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (0,4):
`N_(04)^m = Σ_l S_(0l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_4 = V_4), verified against `su2kFusion 5 0 4 m`. -/
theorem verlinde_k5_0_4 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 0 l * S_k5 4 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 0 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (0,5):
`N_(05)^m = Σ_l S_(0l) S_(5l) S_(ml) / S_(0l)` for every m
(here V_0 ⊗ V_5 = V_5), verified against `su2kFusion 5 0 5 m`. -/
theorem verlinde_k5_0_5 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 0 l * S_k5 5 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 0 5 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (1,0):
`N_(10)^m = Σ_l S_(1l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_0 = V_1), verified against `su2kFusion 5 1 0 m`. -/
theorem verlinde_k5_1_0 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 1 l * S_k5 0 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 1 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (1,1):
`N_(11)^m = Σ_l S_(1l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_1 = V_0 ⊕ V_2), verified against `su2kFusion 5 1 1 m`. -/
theorem verlinde_k5_1_1 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 1 l * S_k5 1 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 1 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (1,2):
`N_(12)^m = Σ_l S_(1l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_2 = V_1 ⊕ V_3), verified against `su2kFusion 5 1 2 m`. -/
theorem verlinde_k5_1_2 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 1 l * S_k5 2 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 1 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (1,3):
`N_(13)^m = Σ_l S_(1l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_3 = V_2 ⊕ V_4), verified against `su2kFusion 5 1 3 m`. -/
theorem verlinde_k5_1_3 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 1 l * S_k5 3 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 1 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (1,4):
`N_(14)^m = Σ_l S_(1l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_4 = V_3 ⊕ V_5), verified against `su2kFusion 5 1 4 m`. -/
theorem verlinde_k5_1_4 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 1 l * S_k5 4 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 1 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (1,5):
`N_(15)^m = Σ_l S_(1l) S_(5l) S_(ml) / S_(0l)` for every m
(here V_1 ⊗ V_5 = V_4), verified against `su2kFusion 5 1 5 m`. -/
theorem verlinde_k5_1_5 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 1 l * S_k5 5 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 1 5 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (2,0):
`N_(20)^m = Σ_l S_(2l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_0 = V_2), verified against `su2kFusion 5 2 0 m`. -/
theorem verlinde_k5_2_0 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 2 l * S_k5 0 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 2 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (2,1):
`N_(21)^m = Σ_l S_(2l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_1 = V_1 ⊕ V_3), verified against `su2kFusion 5 2 1 m`. -/
theorem verlinde_k5_2_1 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 2 l * S_k5 1 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 2 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (2,2):
`N_(22)^m = Σ_l S_(2l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_2 = V_0 ⊕ V_2 ⊕ V_4), verified against `su2kFusion 5 2 2 m`. -/
theorem verlinde_k5_2_2 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 2 l * S_k5 2 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 2 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (2,3):
`N_(23)^m = Σ_l S_(2l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_3 = V_1 ⊕ V_3 ⊕ V_5), verified against `su2kFusion 5 2 3 m`. -/
theorem verlinde_k5_2_3 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 2 l * S_k5 3 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 2 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (2,4):
`N_(24)^m = Σ_l S_(2l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_4 = V_2 ⊕ V_4), verified against `su2kFusion 5 2 4 m`. -/
theorem verlinde_k5_2_4 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 2 l * S_k5 4 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 2 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (2,5):
`N_(25)^m = Σ_l S_(2l) S_(5l) S_(ml) / S_(0l)` for every m
(here V_2 ⊗ V_5 = V_3), verified against `su2kFusion 5 2 5 m`. -/
theorem verlinde_k5_2_5 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 2 l * S_k5 5 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 2 5 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (3,0):
`N_(30)^m = Σ_l S_(3l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_0 = V_3), verified against `su2kFusion 5 3 0 m`. -/
theorem verlinde_k5_3_0 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 3 l * S_k5 0 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 3 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (3,1):
`N_(31)^m = Σ_l S_(3l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_1 = V_2 ⊕ V_4), verified against `su2kFusion 5 3 1 m`. -/
theorem verlinde_k5_3_1 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 3 l * S_k5 1 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 3 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (3,2):
`N_(32)^m = Σ_l S_(3l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_2 = V_1 ⊕ V_3 ⊕ V_5), verified against `su2kFusion 5 3 2 m`. -/
theorem verlinde_k5_3_2 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 3 l * S_k5 2 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 3 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (3,3):
`N_(33)^m = Σ_l S_(3l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_3 = V_0 ⊕ V_2 ⊕ V_4), verified against `su2kFusion 5 3 3 m`. -/
theorem verlinde_k5_3_3 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 3 l * S_k5 3 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 3 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (3,4):
`N_(34)^m = Σ_l S_(3l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_4 = V_1 ⊕ V_3), verified against `su2kFusion 5 3 4 m`. -/
theorem verlinde_k5_3_4 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 3 l * S_k5 4 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 3 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (3,5):
`N_(35)^m = Σ_l S_(3l) S_(5l) S_(ml) / S_(0l)` for every m
(here V_3 ⊗ V_5 = V_2), verified against `su2kFusion 5 3 5 m`. -/
theorem verlinde_k5_3_5 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 3 l * S_k5 5 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 3 5 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (4,0):
`N_(40)^m = Σ_l S_(4l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_0 = V_4), verified against `su2kFusion 5 4 0 m`. -/
theorem verlinde_k5_4_0 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 4 l * S_k5 0 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 4 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (4,1):
`N_(41)^m = Σ_l S_(4l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_1 = V_3 ⊕ V_5), verified against `su2kFusion 5 4 1 m`. -/
theorem verlinde_k5_4_1 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 4 l * S_k5 1 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 4 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (4,2):
`N_(42)^m = Σ_l S_(4l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_2 = V_2 ⊕ V_4), verified against `su2kFusion 5 4 2 m`. -/
theorem verlinde_k5_4_2 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 4 l * S_k5 2 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 4 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (4,3):
`N_(43)^m = Σ_l S_(4l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_3 = V_1 ⊕ V_3), verified against `su2kFusion 5 4 3 m`. -/
theorem verlinde_k5_4_3 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 4 l * S_k5 3 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 4 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (4,4):
`N_(44)^m = Σ_l S_(4l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_4 = V_0 ⊕ V_2), verified against `su2kFusion 5 4 4 m`. -/
theorem verlinde_k5_4_4 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 4 l * S_k5 4 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 4 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (4,5):
`N_(45)^m = Σ_l S_(4l) S_(5l) S_(ml) / S_(0l)` for every m
(here V_4 ⊗ V_5 = V_1), verified against `su2kFusion 5 4 5 m`. -/
theorem verlinde_k5_4_5 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 4 l * S_k5 5 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 4 5 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (5,0):
`N_(50)^m = Σ_l S_(5l) S_(0l) S_(ml) / S_(0l)` for every m
(here V_5 ⊗ V_0 = V_5), verified against `su2kFusion 5 5 0 m`. -/
theorem verlinde_k5_5_0 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 5 l * S_k5 0 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 5 0 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (5,1):
`N_(51)^m = Σ_l S_(5l) S_(1l) S_(ml) / S_(0l)` for every m
(here V_5 ⊗ V_1 = V_4), verified against `su2kFusion 5 5 1 m`. -/
theorem verlinde_k5_5_1 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 5 l * S_k5 1 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 5 1 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (5,2):
`N_(52)^m = Σ_l S_(5l) S_(2l) S_(ml) / S_(0l)` for every m
(here V_5 ⊗ V_2 = V_3), verified against `su2kFusion 5 5 2 m`. -/
theorem verlinde_k5_5_2 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 5 l * S_k5 2 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 5 2 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (5,3):
`N_(53)^m = Σ_l S_(5l) S_(3l) S_(ml) / S_(0l)` for every m
(here V_5 ⊗ V_3 = V_2), verified against `su2kFusion 5 5 3 m`. -/
theorem verlinde_k5_5_3 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 5 l * S_k5 3 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 5 3 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (5,4):
`N_(54)^m = Σ_l S_(5l) S_(4l) S_(ml) / S_(0l)` for every m
(here V_5 ⊗ V_4 = V_1), verified against `su2kFusion 5 5 4 m`. -/
theorem verlinde_k5_5_4 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 5 l * S_k5 4 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 5 4 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- Verlinde formula at k=5, fiber (i,j) = (5,5):
`N_(55)^m = Σ_l S_(5l) S_(5l) S_(ml) / S_(0l)` for every m
(here V_5 ⊗ V_5 = V_0), verified against `su2kFusion 5 5 5 m`. -/
theorem verlinde_k5_5_5 (m' : Fin 6) :
    ∑ l : Fin 6, S_k5 5 l * S_k5 5 l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 5 5 m' : ℝ) := by
  have hm : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3 ∨ m' = 4 ∨ m' = 5 := by revert m'; decide
  rw [verlinde_sum_k5]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num [su2kFusion];
     try decide)

/-- **Verlinde formula at k = 5, full fusion table** (6³ = 216 identities):
the modular S-matrix diagonalizes the fusion rules,
`N_(ij)^m = Σ_l S_(il) S_(jl) conj(S_(ml)) / S_(0l)` (S real symmetric here, so
conj(S) = S), verified for ALL (i, j, m) against the `su2kFusion` coefficients
of `SU2kFusion.lean`. Assembled from the 36 fiber theorems above. -/
theorem verlinde_k5_full (i j m' : Fin 6) :
    ∑ l : Fin 6, S_k5 i l * S_k5 j l * S_k5 m' l / S_k5 0 l =
    (su2kFusion 5 i j m' : ℝ) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · exact verlinde_k5_0_0 m'
  · exact verlinde_k5_0_1 m'
  · exact verlinde_k5_0_2 m'
  · exact verlinde_k5_0_3 m'
  · exact verlinde_k5_0_4 m'
  · exact verlinde_k5_0_5 m'
  · exact verlinde_k5_1_0 m'
  · exact verlinde_k5_1_1 m'
  · exact verlinde_k5_1_2 m'
  · exact verlinde_k5_1_3 m'
  · exact verlinde_k5_1_4 m'
  · exact verlinde_k5_1_5 m'
  · exact verlinde_k5_2_0 m'
  · exact verlinde_k5_2_1 m'
  · exact verlinde_k5_2_2 m'
  · exact verlinde_k5_2_3 m'
  · exact verlinde_k5_2_4 m'
  · exact verlinde_k5_2_5 m'
  · exact verlinde_k5_3_0 m'
  · exact verlinde_k5_3_1 m'
  · exact verlinde_k5_3_2 m'
  · exact verlinde_k5_3_3 m'
  · exact verlinde_k5_3_4 m'
  · exact verlinde_k5_3_5 m'
  · exact verlinde_k5_4_0 m'
  · exact verlinde_k5_4_1 m'
  · exact verlinde_k5_4_2 m'
  · exact verlinde_k5_4_3 m'
  · exact verlinde_k5_4_4 m'
  · exact verlinde_k5_4_5 m'
  · exact verlinde_k5_5_0 m'
  · exact verlinde_k5_5_1 m'
  · exact verlinde_k5_5_2 m'
  · exact verlinde_k5_5_3 m'
  · exact verlinde_k5_5_4 m'
  · exact verlinde_k5_5_5 m'

/-- Pair-product factorization for unitarity at k=5. -/
theorem unitary_sum_k5 (i j : Fin 6) :
    ∑ l : Fin 6, S_k5 i l * S_k5 j l =
    (4 - c7 ^ 2) / 14 *
    (M_k5 i 0 * M_k5 j 0 +
      M_k5 i 1 * M_k5 j 1 +
      M_k5 i 2 * M_k5 j 2 +
      M_k5 i 3 * M_k5 j 3 +
      M_k5 i 4 * M_k5 j 4 +
      M_k5 i 5 * M_k5 j 5) := by
  simp only [S_k5, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_six]
  linear_combination
    (M_k5 i 0 * M_k5 j 0 + M_k5 i 1 * M_k5 j 1 + M_k5 i 2 * M_k5 j 2 + M_k5 i 3 * M_k5 j 3 + M_k5 i 4 * M_k5 j 4 + M_k5 i 5 * M_k5 j 5) * lam_k5_sq

theorem S_k5_unitary_row0 (j : Fin 6) :
    ∑ l : Fin 6, S_k5 0 l * S_k5 j l = if (0 : Fin 6) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
  rw [unitary_sum_k5]
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k5_unitary_row1 (j : Fin 6) :
    ∑ l : Fin 6, S_k5 1 l * S_k5 j l = if (1 : Fin 6) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
  rw [unitary_sum_k5]
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k5_unitary_row2 (j : Fin 6) :
    ∑ l : Fin 6, S_k5 2 l * S_k5 j l = if (2 : Fin 6) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
  rw [unitary_sum_k5]
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k5_unitary_row3 (j : Fin 6) :
    ∑ l : Fin 6, S_k5 3 l * S_k5 j l = if (3 : Fin 6) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
  rw [unitary_sum_k5]
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k5_unitary_row4 (j : Fin 6) :
    ∑ l : Fin 6, S_k5 4 l * S_k5 j l = if (4 : Fin 6) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
  rw [unitary_sum_k5]
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num;
     try decide)

theorem S_k5_unitary_row5 (j : Fin 6) :
    ∑ l : Fin 6, S_k5 5 l * S_k5 j l = if (5 : Fin 6) = j then 1 else 0 := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
  rw [unitary_sum_k5]
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [M_k5_0_0, M_k5_0_1, M_k5_0_2, M_k5_0_3, M_k5_0_4, M_k5_0_5, M_k5_1_0, M_k5_1_1, M_k5_1_2, M_k5_1_3, M_k5_1_4, M_k5_1_5, M_k5_2_0, M_k5_2_1, M_k5_2_2, M_k5_2_3, M_k5_2_4, M_k5_2_5, M_k5_3_0, M_k5_3_1, M_k5_3_2, M_k5_3_3, M_k5_3_4, M_k5_3_5, M_k5_4_0, M_k5_4_1, M_k5_4_2, M_k5_4_3, M_k5_4_4, M_k5_4_5, M_k5_5_0, M_k5_5_1, M_k5_5_2, M_k5_5_3, M_k5_5_4, M_k5_5_5];
     ring_nf;
     try simp only [c7_cubed, c7_pow4, c7_pow5, c7_pow6, c7_pow7, c7_pow8, c7_pow9, c7_pow10];
     try ring_nf;
     norm_num;
     try decide)

/-- Unitarity at k=5: S Sᵀ = I (6×6). Together with `S_k5_det_ne_zero`
this is the modularity (non-degeneracy) condition for the SU(2)_5 MTC. -/
theorem S_k5_unitary : S_k5 * S_k5.transpose = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact S_k5_unitary_row0 j
  · exact S_k5_unitary_row1 j
  · exact S_k5_unitary_row2 j
  · exact S_k5_unitary_row3 j
  · exact S_k5_unitary_row4 j
  · exact S_k5_unitary_row5 j

/-- Modularity at k=5: det S ≠ 0 (follows from unitarity: (det S)² = 1). -/
theorem S_k5_det_ne_zero : S_k5.det ≠ 0 := by
  intro h
  have h1 : S_k5.det * S_k5.det = 1 := by
    have h2 := congrArg Matrix.det S_k5_unitary
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  rw [h] at h1
  norm_num at h1

/-- The k=5 S-matrix is symmetric. -/
theorem S_k5_symmetric : S_k5.transpose = S_k5 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **Row-0 faithfulness at k=5**: the quantum-dimension row of `S_k5` equals
the literal trigonometric values `√(2/7)·sin((b+1)π/7)` of the Kac–Peterson
S-matrix. Here the scale `λ₅ = √(2/7)·sin(π/7)` is trigonometric BY
DEFINITION, so the content is the Chebyshev ratio reduction:
`sin(2θ) = c₇·sin(θ)` and `sin(3θ) = (c₇²-1)·sin(θ)` at `θ = π/7`
(via `sin²θ = 1 - cos²θ`), plus the reflection `sin(π-x) = sin x` for
`b = 3, 4, 5`. -/
theorem S_k5_row0_sin (b : Fin 6) :
    S_k5 0 b = √(2 / 7) * Real.sin (((b.val : ℝ) + 1) * (π / 7)) := by
  have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by revert b; decide
  have hsin3 : √(2 / 7) * Real.sin (π / 7) * (c7 ^ 2 - 1) =
      √(2 / 7) * Real.sin (3 * (π / 7)) := by
    rw [Real.sin_three_mul, show c7 = 2 * Real.cos (π / 7) from rfl]
    linear_combination (4 * √(2 / 7) * Real.sin (π / 7)) * Real.sin_sq (π / 7)
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [S_k5, Matrix.smul_apply, smul_eq_mul, M_k5_0_0]
    rw [show (((0 : Fin 6).val : ℝ) + 1) * (π / 7) = π / 7 by norm_num, mul_one]
    rfl
  · simp only [S_k5, Matrix.smul_apply, smul_eq_mul, M_k5_0_1]
    rw [show (((1 : Fin 6).val : ℝ) + 1) * (π / 7) = 2 * (π / 7) by
          rw [show ((1 : Fin 6).val) = 1 from rfl]; push_cast; ring,
        Real.sin_two_mul, show lam_k5 = √(2 / 7) * Real.sin (π / 7) from rfl,
        show c7 = 2 * Real.cos (π / 7) from rfl]
    ring
  · simp only [S_k5, Matrix.smul_apply, smul_eq_mul, M_k5_0_2]
    rw [show (((2 : Fin 6).val : ℝ) + 1) * (π / 7) = 3 * (π / 7) by
          rw [show ((2 : Fin 6).val) = 2 from rfl]; push_cast; ring,
        ← hsin3, show lam_k5 = √(2 / 7) * Real.sin (π / 7) from rfl]
  · simp only [S_k5, Matrix.smul_apply, smul_eq_mul, M_k5_0_3]
    rw [show (((3 : Fin 6).val : ℝ) + 1) * (π / 7) = π - 3 * (π / 7) by
          rw [show ((3 : Fin 6).val) = 3 from rfl]; push_cast; ring,
        Real.sin_pi_sub, ← hsin3, show lam_k5 = √(2 / 7) * Real.sin (π / 7) from rfl]
  · simp only [S_k5, Matrix.smul_apply, smul_eq_mul, M_k5_0_4]
    rw [show (((4 : Fin 6).val : ℝ) + 1) * (π / 7) = π - 2 * (π / 7) by
          rw [show ((4 : Fin 6).val) = 4 from rfl]; push_cast; ring,
        Real.sin_pi_sub, Real.sin_two_mul, show lam_k5 = √(2 / 7) * Real.sin (π / 7) from rfl,
        show c7 = 2 * Real.cos (π / 7) from rfl]
    ring
  · simp only [S_k5, Matrix.smul_apply, smul_eq_mul, M_k5_0_5]
    rw [show (((5 : Fin 6).val : ℝ) + 1) * (π / 7) = π - π / 7 by
          rw [show ((5 : Fin 6).val) = 5 from rfl]; push_cast; ring,
        Real.sin_pi_sub, mul_one]
    rfl

end Level5Exact

/-! ## 6. SU(2)_5 S-matrix Unitarity (Phase 5s: Rational Character Sum)

Integer character-sum encoding (no algebraic number field needed). The exact
real-matrix counterpart, including the full Verlinde table, is Section 5
above; this section is kept as the independent integer-arithmetic cross-check. -/

section Level5CharSum

/-- Character sum for S-matrix unitarity over ℤ.
    For any level k, (k+2)·(SS^T)_{ij} = charSum(i-j, k+2) - charSum(i+j+2, k+2)
    where charSum(n, m) = Σ_{l=1}^{m-1} cos(πln/m).
    This sum evaluates to: (m-1) if n≡0 mod 2m; -1 if n even, n≢0 mod m; 0 if n odd.
    No algebraic number field needed — pure integer arithmetic. -/
def charSumVal (n m : ℤ) : ℤ :=
  let n_mod := n % (2 * m)
  let n_mod_pos := if n_mod < 0 then n_mod + 2 * m else n_mod
  if n_mod_pos = 0 then m - 1
  else if n_mod_pos % 2 = 0 then -1
  else 0

/-- The unitarity matrix (k+2)·SS^T for k=5 (7 objects → 6×6 matrix).
    Should equal 7·I₆. -/
def unitarityK5 : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of fun i j =>
  charSumVal (↑i.val - ↑j.val) 7 - charSumVal (↑i.val + ↑j.val + 2) 7

/-- SU(2)₅ S-matrix unitarity: 7·SS^T = 7·I (over ℤ).
    Verified by decide on 36 integer entries. -/
theorem su2k5_unitarity : unitarityK5 = 7 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide

end Level5CharSum

/-! ## 7. Module summary -/

/-! ## Module summary

SU2kSMatrix module: S-matrices and Verlinde formula for SU(2) at k=1,...,5.
  - k=1: 2x2 Hadamard, unitarity, det ≠ 0 (modularity)
  - k=2: 3x3 Ising (Q(√2)), unitarity, det ≠ 0
  - k=3: 4x4 (Q(φ)=Q(√5)), unitarity, det ≠ 0, FULL Verlinde table (64)
  - k=4: 5x5 (Q(√3)), unitarity, det ≠ 0, FULL Verlinde table (125)
  - k=5: 6x6 (Q(2cos(π/7)), proven cubic minimal polynomial), unitarity,
         det ≠ 0, FULL Verlinde table (216)
  - k=5 ALSO: unitarity via rational character sums (Phase 5s, Section 6)
  - Verlinde formula: k=1,2 representative cases; k=3,4,5 full tables
    (verlinde_k3_full / verlinde_k4_full / verlinde_k5_full), all verified
    against su2kFusion from SU2kFusion.lean
  - Modularity: det(S) ≠ 0 → Z₂ trivial (general theorem in ModularityTheorem.lean)
  - Row-0 (quantum-dimension row) tied to the trig form S_{0b} = √(2/(k+2))·
    sin((b+1)π/(k+2)) at k=3,4,5 (S_k3_row0_sin / S_k4_row0_sin / S_k5_row0_sin)
  - Everything kernel-pure: decide/norm_num/ring/linear_combination only —
    no native_decide, no new axioms, no maxHeartbeats overrides
-/
end SKEFTHawking
