/-
Phase 5c Wave 4: SU(2)_k S-matrices and Verlinde Formula

Explicit S-matrices for SU(2) at levels k = 1, 2.
Unitarity (S * S^T = I) and Verlinde formula verification.

For k=1: S = (1/sqrt(2)) * Hadamard (2x2)
For k=2: 3x3 Ising S-matrix with entries in Q(sqrt(2))

All entries are algebraic — no transcendental trig needed.
The Verlinde formula N_{ij}^m = sum_l S_{il} S_{jl} S_{ml} / S_{0l}
reproduces the fusion rules from SU2kFusion.lean.

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

/-! ## 3. Module summary -/

/--
SU2kSMatrix module: S-matrices and Verlinde formula for SU(2) at k=1,2.
  - k=1: 2x2 Hadamard S-matrix, unitarity, det != 0 (modularity)
  - k=2: 3x3 Ising S-matrix (entries in Q(sqrt(2))), unitarity, det != 0
  - Verlinde formula verified: N_{11}^0=1, N_{11}^1=0 for k=1;
    N_{11}^0=1, N_{11}^1=0, N_{11}^2=1, N_{22}^0=1 for k=2
  - All entries algebraic (1/2, 1/sqrt(2), 0) — no transcendental trig
  - Modularity: det(S) != 0 makes these MTCs, not just fusion categories
-/
theorem su2k_smatrix_summary : True := trivial

end SKEFTHawking