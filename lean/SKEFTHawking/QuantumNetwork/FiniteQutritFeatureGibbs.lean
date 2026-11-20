import SKEFTHawking.QuantumNetwork.FiniteQutritEuclideanTransfer

/-!
# Gibbs and modular calculus on actual feature endomorphisms

The state here has six feature coordinates. It is not a physical qutrit
density; the normalized feature transfer is not a trace-preserving qutrit map.
The modular parameter comparison is algebraic and uses dimensionless energies.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteQutritFeatureGibbs
open Matrix FiniteQutritInvariantCarrier FiniteQutritInvariantReconstruction
open FiniteQutritAveragedTransfer FiniteQutritAveragedMixing
open FiniteQutritEuclideanTransfer
open scoped BigOperators ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

private theorem vec6_last {α : Type*} (a b c d e f : α) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def H6 : Matrix Index Index ℂ := Matrix.diagonal (fun i => (energy i : ℂ))

theorem H6_hermitian : H6.IsHermitian := by
  ext i j
  by_cases h : i=j
  · subst j; simp [H6, Matrix.conjTranspose_apply]
  · simp [H6, Matrix.conjTranspose_apply, h, Ne.symm h]

def Z (beta : ℝ) : ℝ := ∑ i : Index, (eigenvalue i)^beta
def sigma (beta : ℝ) : Matrix Index Index ℂ :=
  (Z beta)⁻¹ • Matrix.diagonal (fun i => (((eigenvalue i)^beta : ℝ) : ℂ))

theorem Z_pos (beta : ℝ) : 0 < Z beta := by
  unfold Z
  exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (eigenvalue_pos i) _)
    Finset.univ_nonempty

theorem boltzmann_concrete (beta : ℝ) :
    FiniteGibbsClock.boltzmann H6 beta =
      Matrix.diagonal (fun i => (((eigenvalue i)^beta : ℝ) : ℂ)) := by
  unfold FiniteGibbsClock.boltzmann H6
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  ext i
  rw [Real.rpow_def_of_pos (eigenvalue_pos i)]
  simp [← Complex.exp_eq_exp_ℂ, Complex.real_smul, energy,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_comm]

theorem partition_concrete (beta : ℝ) : FiniteGibbsClock.partition H6 beta = Z beta := by
  unfold FiniteGibbsClock.partition
  rw [boltzmann_concrete]
  simp [Matrix.trace, Complex.re_sum, Z]

theorem sigma_gibbs (beta : ℝ) : sigma beta = FiniteGibbsClock.gibbs H6 beta := by
  rw [FiniteGibbsClock.gibbs, partition_concrete, boltzmann_concrete]
  rfl

theorem sigma_density (beta : ℝ) : IsDensityOperator (sigma beta) := by
  rw [sigma_gibbs]
  exact FiniteGibbsClock.gibbs_density H6_hermitian beta

theorem sigma_faithful (beta : ℝ) : (sigma beta).PosDef := by
  rw [sigma_gibbs]
  exact FiniteGibbsClock.gibbs_posDef H6_hermitian beta

private theorem matrixLog_congr {A B : Matrix Index Index ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A=B) : matrixLog hA = matrixLog hB := by
  subst B
  rfl

theorem sigma_log (beta : ℝ) :
    matrixLog (sigma_faithful beta).posSemidef.isHermitian =
      (-beta) • H6 + (-(Real.log (Z beta)) : ℂ) • 1 := by
  calc
    _ = matrixLog (FiniteGibbsClock.gibbs_posDef H6_hermitian beta).posSemidef.isHermitian :=
      matrixLog_congr _ _ (sigma_gibbs beta)
    _ = _ := by simpa only [partition_concrete] using
      FiniteGibbsClock.matrixLog_gibbs H6_hermitian beta

theorem Z_zero : Z 0 = 6 := by simp [Z]
theorem Z_one : Z 1 = 4 := by
  norm_num [Z, eigenvalue, Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

theorem sigma_zero : sigma 0 = (1/6 : ℝ) • (1 : Matrix Index Index ℂ) := by
  simp [sigma, Z_zero]

theorem sigma_one : sigma 1 = Matrix.diagonal ![(1/4 : ℂ),9/40,7/40,3/20,1/8,3/40] := by
  rw [sigma, Z_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal_apply, eigenvalue, Matrix.smul_apply,
      Complex.real_smul, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, vec6_last, Fin.ext_iff]

theorem transfer_matrix :
    matrixOperator (Matrix.diagonal (fun i => (eigenvalue i : ℂ))) =
      LinearMap.toContinuousLinearMap quotientTransfer := by
  rw [matrixOperator_diagonal, ← E_one]
  congr 1
  unfold E
  congr 1
  ext i
  rw [one_mul, Real.exp_log (eigenvalue_pos i)]

def featureTrace (T : FeatureSpace →L[ℂ] FeatureSpace) : ℂ := (matrixOperator.symm T).trace

theorem transfer_feature_trace :
    featureTrace (LinearMap.toContinuousLinearMap quotientTransfer) = 4 := by
  rw [featureTrace, ← transfer_matrix, matrixOperator.symm_apply_apply]
  norm_num [Matrix.trace, Fin.sum_univ_succ, eigenvalue, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, vec6_last]

def sigmaEnd (beta : ℝ) : FeatureSpace →L[ℂ] FeatureSpace := matrixOperator (sigma beta)
def logEnd (beta : ℝ) : FeatureSpace →L[ℂ] FeatureSpace :=
  matrixOperator (matrixLog (sigma_faithful beta).posSemidef.isHermitian)

theorem sigmaEnd_evolution (beta : ℝ) : sigmaEnd beta = (Z beta)⁻¹ • EC beta := by
  unfold sigmaEnd sigma
  have h := (matrixOperator.toLinearMap.restrictScalars ℝ).map_smul (Z beta)⁻¹
    (Matrix.diagonal (fun i => (((eigenvalue i)^beta : ℝ) : ℂ)))
  change matrixOperator ((Z beta)⁻¹ • _) = (Z beta)⁻¹ • matrixOperator _ at h
  rw [h, matrixOperator_diagonal]
  congr 1
  congr 1
  unfold E
  congr 1
  ext i
  rw [Real.rpow_def_of_pos (eigenvalue_pos i), mul_comm]

theorem sigmaEnd_faithful (beta : ℝ) {q : FeatureSpace} (hq : q ≠ 0) :
    0 < (⟪q,sigmaEnd beta q⟫_ℂ).re := by
  rw [sigmaEnd_evolution]
  change 0 < (⟪q,(Z beta)⁻¹ • E beta q⟫_ℂ).re
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (inv_pos.mpr (Z_pos beta)) (E_strict_hilbert_positive beta hq)

theorem sigmaEnd_feature_trace (beta : ℝ) : featureTrace (sigmaEnd beta) = 1 := by
  rw [featureTrace, sigmaEnd, matrixOperator.symm_apply_apply]
  exact (sigma_density beta).2

theorem sigmaEnd_positive (beta : ℝ) : 0 ≤ sigmaEnd beta := by
  have hH : IsSelfAdjoint HC := H_selfadjoint.isSelfAdjoint
  have hE : 0 ≤ EC beta := by
    rw [E_operator_exp]
    exact ((IsSelfAdjoint.all (-beta : ℝ)).smul hH).exp_nonneg
  rw [sigmaEnd_evolution]
  exact smul_nonneg (inv_nonneg.mpr (Z_pos beta).le) hE

theorem sigmaEnd_selfadjoint (beta : ℝ) : IsSelfAdjoint (sigmaEnd beta) :=
  ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sigmaEnd_positive beta)).isSelfAdjoint

theorem logEnd_concrete (beta : ℝ) :
    logEnd beta = (-beta) • HC + (-(Real.log (Z beta)) : ℂ) • 1 := by
  rw [logEnd, sigma_log, map_add]
  have h := (matrixOperator.toLinearMap.restrictScalars ℝ).map_smul (-beta) H6
  change matrixOperator ((-beta) • H6) = (-beta) • matrixOperator H6 at h
  rw [h, map_smul, H6, matrixOperator_diagonal, map_one]
  rfl

theorem sigmaEnd_zero : sigmaEnd 0 = (1/6 : ℝ) • 1 := by
  rw [sigmaEnd_evolution, Z_zero, EC, E_zero]
  norm_num
  ext q
  rfl

theorem sigmaEnd_one :
    sigmaEnd 1 = (1/4 : ℝ) • LinearMap.toContinuousLinearMap quotientTransfer := by
  rw [sigmaEnd_evolution, Z_one, EC, E_one]
  norm_num

def modularEnd (beta s : ℝ) (X : FeatureSpace →L[ℂ] FeatureSpace) :=
  matrixOperator (FiniteGibbsClock.modular H6_hermitian beta s (matrixOperator.symm X))

theorem modular_phase (beta s : ℝ) (X : Matrix Index Index ℂ) (i j : Index) :
    FiniteGibbsClock.modular H6_hermitian beta s X i j =
      Complex.exp (Complex.I * beta * s *
        (Real.log (eigenvalue i)-Real.log (eigenvalue j))) * X i j := by
  rw [FiniteGibbsClock.modular_conjugate, H6, FiniteGibbsClock.diagonal_conjugate_entry]
  congr 2
  simp only [energy, Complex.ofReal_neg]
  ring

theorem modularEnd_parameter (beta s hbar : ℝ) (hhbar : 0 < hbar)
    (X : FeatureSpace →L[ℂ] FeatureSpace) :
    modularEnd beta s X = matrixOperator (FiniteGibbsClock.heisenberg H6 hbar
      (-beta*hbar*s) (matrixOperator.symm X)) :=
  congrArg matrixOperator (FiniteGibbsClock.modular_eq_heisenberg
    H6_hermitian beta s hbar hhbar (matrixOperator.symm X))

theorem H6_transport : matrixOperator H6 = HC := matrixOperator_diagonal _

theorem modularEnd_phase (beta s : ℝ) (X : FeatureSpace →L[ℂ] FeatureSpace) (i j : Index) :
    matrixOperator.symm (modularEnd beta s X) i j =
      Complex.exp (Complex.I * beta * s *
        (Real.log (eigenvalue i)-Real.log (eigenvalue j))) * matrixOperator.symm X i j := by
  rw [modularEnd, matrixOperator.symm_apply_apply, modular_phase]

theorem modularEnd_group (beta s t : ℝ) (X : FeatureSpace →L[ℂ] FeatureSpace) :
    modularEnd beta (s+t) X = modularEnd beta s (modularEnd beta t X) := by
  unfold modularEnd
  rw [matrixOperator.symm_apply_apply, FiniteGibbsClock.modular_group]

theorem modularEnd_zero (beta : ℝ) (X : FeatureSpace →L[ℂ] FeatureSpace) :
    modularEnd beta 0 X = X := by
  rw [modularEnd, FiniteGibbsClock.modular_zero, matrixOperator.apply_symm_apply]

theorem modularEnd_multiplicative (beta s : ℝ)
    (X Y : FeatureSpace →L[ℂ] FeatureSpace) :
    modularEnd beta s (X*Y) = modularEnd beta s X * modularEnd beta s Y := by
  unfold modularEnd
  rw [map_mul, FiniteGibbsClock.modular_mul, map_mul]

end SKEFTHawking.QuantumNetwork.FiniteQutritFeatureGibbs
