import SKEFTHawking.QuantumNetwork.QuantumRelativeEntropy
import SKEFTHawking.QuantumNetwork.NamedChannels
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-! Finite faithful Gibbs states and their modular/Heisenberg parameter comparison.
All exponentials are matrix exponentials; the logarithm is the existing spectral
matrixLog. The finite Gibbs construction works for every real beta; the usual
positive-temperature interpretation specializes to beta > 0. With beta in
inverse-energy units, hbar in energy*time and dimensionless s, the convention is
sigma_s(X)=rho^(is) X rho^(-is), alpha_t(X)=exp(itH/hbar) X exp(-itH/hbar),
so t=-beta*hbar*s. A periodic phase is not a globally unique clock readout.
Faithfulness is proved here; the log-zero convention does not extend the result
to singular states. No infinite-dimensional, KMS-analytic or horizon claim. -/
namespace SKEFTHawking.QuantumNetwork.FiniteGibbsClock
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exp_scalar (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix ι ι ℂ)) = Complex.exp c • 1 := by
  have h : c • (1 : Matrix ι ι ℂ) = diagonal (fun _ => c) := by
    ext i j; simp [diagonal, one_apply]
  rw [h, Matrix.exp_diagonal]
  ext i j
  simp [← Complex.exp_eq_exp_ℂ, diagonal, one_apply]

theorem exp_posDef {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp A).PosDef := by
  have hp := Matrix.nonneg_iff_posSemidef.mp hA.isSelfAdjoint.exp_nonneg
  exact hp.posDef_iff_isUnit.mpr (Matrix.isUnit_exp A)

noncomputable def boltzmann (H : Matrix ι ι ℂ) (β : ℝ) := NormedSpace.exp ((-β) • H)
noncomputable def partition (H : Matrix ι ι ℂ) (β : ℝ) : ℝ := (boltzmann H β).trace.re
noncomputable def gibbs (H : Matrix ι ι ℂ) (β : ℝ) := (partition H β)⁻¹ • boltzmann H β

theorem boltzmann_posDef {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    (boltzmann H β).PosDef := exp_posDef (hH.smul (IsSelfAdjoint.all _))

theorem partition_pos [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    0 < partition H β := (Complex.lt_def.mp (boltzmann_posDef hH β).trace_pos).1

theorem boltzmann_trace {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    (boltzmann H β).trace = (partition H β : ℂ) := by
  have hi := (Complex.le_def.mp (boltzmann_posDef hH β).posSemidef.trace_nonneg).2
  apply Complex.ext
  · rfl
  · simpa using hi.symm

theorem gibbs_posDef [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    (gibbs H β).PosDef := (boltzmann_posDef hH β).smul (inv_pos.mpr (partition_pos hH β))

theorem gibbs_trace_one [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    (gibbs H β).trace = 1 := by
  rw [gibbs, Matrix.trace_smul, boltzmann_trace hH β]
  simp [Complex.real_smul, partition_pos hH β |>.ne']

theorem gibbs_density [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    IsDensityOperator (gibbs H β) := ⟨(gibbs_posDef hH β).posSemidef, gibbs_trace_one hH β⟩

theorem exp_add_scalar (A : Matrix ι ι ℂ) (c : ℂ) :
    NormedSpace.exp (A + c • 1) = Complex.exp c • NormedSpace.exp A := by
  rw [Matrix.exp_add_of_commute _ _ ((Commute.one_right A).smul_right c), exp_scalar]
  simp

theorem gibbs_eq_exp [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    gibbs H β = NormedSpace.exp ((-β) • H + (-(Real.log (partition H β)) : ℂ) • 1) := by
  rw [exp_add_scalar]
  simp [gibbs, boltzmann, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    Real.exp_neg, Real.exp_log (partition_pos hH β)]
  ext i j
  simp [Complex.real_smul]

theorem matrixLog_gibbs [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β : ℝ) :
    matrixLog (gibbs_posDef hH β).posSemidef.isHermitian =
      (-β) • H + (-(Real.log (partition H β)) : ℂ) • 1 := by
  rw [matrixLog, ← Matrix.IsHermitian.cfc_eq, ← CFC.log]
  rw [gibbs_eq_exp hH β]
  apply CFC.log_exp
  exact ((hH.smul (IsSelfAdjoint.all _)).add
    (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))).isSelfAdjoint

noncomputable def expCoeff (A : Matrix ι ι ℂ) (c : ℂ) := NormedSpace.exp (c • A)

theorem expCoeff_add (A : Matrix ι ι ℂ) (c d : ℂ) :
    expCoeff A (c + d) = expCoeff A c * expCoeff A d := by
  unfold expCoeff
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left c).smul_right d)

theorem expCoeff_cancel (A : Matrix ι ι ℂ) (c : ℂ) :
    expCoeff A c * expCoeff A (-c) = 1 := by
  rw [← expCoeff_add]
  simp [expCoeff]

noncomputable def conjugate (A : Matrix ι ι ℂ) (c : ℂ) (X : Matrix ι ι ℂ) :=
  expCoeff A c * X * expCoeff A (-c)

theorem conjugate_one (A : Matrix ι ι ℂ) (c : ℂ) : conjugate A c 1 = 1 := by
  simpa [conjugate] using expCoeff_cancel A c

theorem conjugate_add (A : Matrix ι ι ℂ) (c : ℂ) (X Y : Matrix ι ι ℂ) :
    conjugate A c (X + Y) = conjugate A c X + conjugate A c Y := by
  simp [conjugate, Matrix.mul_add, Matrix.add_mul]

theorem conjugate_smul (A : Matrix ι ι ℂ) (c z : ℂ) (X : Matrix ι ι ℂ) :
    conjugate A c (z • X) = z • conjugate A c X := by simp [conjugate]

theorem conjugate_mul (A : Matrix ι ι ℂ) (c : ℂ) (X Y : Matrix ι ι ℂ) :
    conjugate A c (X * Y) = conjugate A c X * conjugate A c Y := by
  have hc : expCoeff A (-c) * expCoeff A c = 1 := by simpa using expCoeff_cancel A (-c)
  simp only [conjugate, mul_assoc]
  rw [← mul_assoc (expCoeff A (-c)), hc, one_mul]

theorem conjugate_zero (A X : Matrix ι ι ℂ) : conjugate A 0 X = X := by
  simp [conjugate, expCoeff]

theorem conjugate_group (A : Matrix ι ι ℂ) (c d : ℂ) (X : Matrix ι ι ℂ) :
    conjugate A (c + d) X = conjugate A c (conjugate A d X) := by
  have hn : -(c + d) = -d + -c := by ring
  simp only [conjugate, hn, expCoeff_add, mul_assoc]

theorem conjugate_inverse (A : Matrix ι ι ℂ) (c : ℂ) (X : Matrix ι ι ℂ) :
    conjugate A (-c) (conjugate A c X) = X := by
  rw [← conjugate_group]
  simp [conjugate_zero]

theorem expCoeff_adjoint {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℂ) :
    (expCoeff A c)ᴴ = expCoeff A (star c) := by
  simp [expCoeff, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hA.eq]

theorem conjugate_star {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ)
    (X : Matrix ι ι ℂ) :
    conjugate A (Complex.I * t) Xᴴ = (conjugate A (Complex.I * t) X)ᴴ := by
  simp [conjugate, Matrix.conjTranspose_mul, expCoeff_adjoint hA, mul_assoc]

theorem conjugate_affine (A : Matrix ι ι ℂ) (a b c : ℂ) (X : Matrix ι ι ℂ) :
    conjugate (a • A + b • 1) c X = conjugate A (c * a) X := by
  have hp (d : ℂ) : expCoeff (a • A + b • 1) d =
      Complex.exp (d * b) • expCoeff A (d * a) := by
    simp only [expCoeff, smul_add, smul_smul]
    exact exp_add_scalar _ _
  simp only [conjugate, hp, smul_mul_assoc, mul_smul_comm, smul_smul, neg_mul]
  rw [← Complex.exp_add]
  simp

/-- Dimensionless modular parameter, independently defined from log rho. -/
noncomputable def modular [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s : ℝ) (X : Matrix ι ι ℂ) :=
  conjugate (matrixLog (gibbs_posDef hH β).posSemidef.isHermitian) (Complex.I * s) X

/-- Physical Heisenberg time, hbar in energy-times-time units. -/
noncomputable def heisenberg (H : Matrix ι ι ℂ) (ℏ t : ℝ) (X : Matrix ι ι ℂ) :=
  conjugate H (Complex.I * (t / ℏ)) X

theorem modular_eq_heisenberg [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s ℏ : ℝ) (hℏ : 0 < ℏ) (X : Matrix ι ι ℂ) :
    modular hH β s X = heisenberg H ℏ (-β * ℏ * s) X := by
  unfold modular heisenberg
  rw [matrixLog_gibbs hH β]
  have hr : (-β) • H = ((-β : ℝ) : ℂ) • H := by ext i j; simp [Complex.real_smul]
  rw [hr, conjugate_affine]
  congr 1
  push_cast
  field_simp

theorem modular_conjugate [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s : ℝ) (X : Matrix ι ι ℂ) :
    modular hH β s X = conjugate H ((Complex.I * s) * (-β : ℂ)) X := by
  unfold modular
  rw [matrixLog_gibbs hH β]
  have hr : (-β) • H = ((-β : ℝ) : ℂ) • H := by ext i j; simp [Complex.real_smul]
  rw [hr, conjugate_affine]
  simp

theorem modular_add [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s : ℝ) (X Y : Matrix ι ι ℂ) :
    modular hH β s (X + Y) = modular hH β s X + modular hH β s Y := conjugate_add _ _ _ _
theorem modular_smul [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s : ℝ) (z : ℂ) (X : Matrix ι ι ℂ) :
    modular hH β s (z • X) = z • modular hH β s X := conjugate_smul _ _ _ _
theorem modular_one [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (β s : ℝ) :
    modular hH β s 1 = 1 := conjugate_one _ _
theorem modular_mul [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s : ℝ) (X Y : Matrix ι ι ℂ) :
    modular hH β s (X * Y) = modular hH β s X * modular hH β s Y := conjugate_mul _ _ _ _
theorem modular_star [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s : ℝ) (X : Matrix ι ι ℂ) : modular hH β s Xᴴ = (modular hH β s X)ᴴ :=
  conjugate_star (cfc_isHermitian _ _) _ _
theorem modular_zero [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β : ℝ) (X : Matrix ι ι ℂ) : modular hH β 0 X = X := by simp [modular, conjugate_zero]
theorem modular_group [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s t : ℝ) (X : Matrix ι ι ℂ) :
    modular hH β (s + t) X = modular hH β s (modular hH β t X) := by
  simp only [modular, Complex.ofReal_add, mul_add, conjugate_group]
theorem modular_inverse [Nonempty ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (β s : ℝ) (X : Matrix ι ι ℂ) : modular hH β (-s) (modular hH β s X) = X := by
  rw [← modular_group]
  simpa using modular_zero hH β X

theorem diagonal_conjugate_entry (e : ι → ℂ) (c : ℂ) (X : Matrix ι ι ℂ) (i j : ι) :
    conjugate (diagonal e) c X i j = Complex.exp (c * (e i - e j)) * X i j := by
  simp only [conjugate, expCoeff, ← Matrix.diagonal_smul, Matrix.exp_diagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [← Complex.exp_eq_exp_ℂ]
  rw [show c * (e i - e j) = c * e i + -(c * e j) by ring, Complex.exp_add]
  ring

/-- Equal-energy matrix entries are fixed, including degenerate blocks. -/
theorem degenerate_entry_fixed (e : ι → ℂ) (c : ℂ) (X : Matrix ι ι ℂ)
    (i j : ι) (h : e i = e j) : conjugate (diagonal e) c X i j = X i j := by
  simp [diagonal_conjugate_entry, h]

noncomputable def twoLevel (Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![0, (Δ : ℂ)]
theorem twoLevel_hermitian (Δ : ℝ) : (twoLevel Δ).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoLevel]
def E01 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 1 1

theorem twoLevel_phase (Δ β s : ℝ) :
    modular (twoLevel_hermitian Δ) β s E01 = Complex.exp (Complex.I * β * Δ * s) • E01 := by
  rw [modular_conjugate]
  ext i j
  simp only [twoLevel, diagonal_conjugate_entry]
  fin_cases i <;> fin_cases j <;> simp [E01, Matrix.single]; congr 1; ring

theorem twoLevel_sign_flip {Δ β : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β) :
    modular (twoLevel_hermitian Δ) β (Real.pi / (β * Δ)) E01 = -E01 := by
  rw [twoLevel_phase]
  have hphase : Complex.I * (β : ℂ) * Δ * (Real.pi / (β * Δ) : ℝ) = Real.pi * Complex.I := by
    push_cast
    field_simp
  rw [hphase, Complex.exp_pi_mul_I]
  simp

theorem E01_ne_zero : E01 ≠ 0 := by
  intro h
  have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 0 1) h
  norm_num [E01, Matrix.single] at hh

theorem conjugate_scalar (c d : ℂ) (X : Matrix ι ι ℂ) : conjugate (c • 1) d X = X := by
  have h := conjugate_affine (0 : Matrix ι ι ℂ) 0 c d X
  simpa [conjugate_zero] using h

theorem heisenberg_energy_shift (H : Matrix ι ι ℂ) (c ℏ t : ℝ) (X : Matrix ι ι ℂ) :
    heisenberg (H + (c : ℂ) • 1) ℏ t X = heisenberg H ℏ t X := by
  simpa [heisenberg] using conjugate_affine H 1 c (Complex.I * (t / ℏ)) X

theorem boltzmann_energy_shift (H : Matrix ι ι ℂ) (c β : ℝ) :
    boltzmann (H + (c : ℂ) • 1) β = Real.exp (-β * c) • boltzmann H β := by
  unfold boltzmann
  rw [smul_add]
  have he : (-β) • ((c : ℂ) • (1 : Matrix ι ι ℂ)) = ((-β * c : ℝ) : ℂ) • 1 := by
    ext i j; simp [Complex.real_smul]; ring
  rw [he, exp_add_scalar, ← Complex.ofReal_exp]
  ext i j; simp [Complex.real_smul]

theorem partition_energy_shift (H : Matrix ι ι ℂ) (c β : ℝ) :
    partition (H + (c : ℂ) • 1) β = Real.exp (-β * c) * partition H β := by
  unfold partition
  rw [boltzmann_energy_shift]
  rw [Matrix.trace_smul]
  exact Complex.smul_re _ _

theorem gibbs_energy_shift {H : Matrix ι ι ℂ} (c β : ℝ) :
    gibbs (H + (c : ℂ) • 1) β = gibbs H β := by
  unfold gibbs
  rw [partition_energy_shift, boltzmann_energy_shift]
  simp [smul_smul, _root_.mul_inv_rev, Real.exp_ne_zero]

theorem modular_energy_shift [Nonempty ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (c β s : ℝ)
    (hshift : (H + (c : ℂ) • 1).IsHermitian) (X : Matrix ι ι ℂ) :
    modular hshift β s X = modular hH β s X := by
  rw [modular_conjugate, modular_conjugate]
  simpa using conjugate_affine H 1 c ((Complex.I * s) * (-β : ℂ)) X

theorem gibbs_scalar (c β : ℝ) :
    gibbs ((c : ℂ) • (1 : Matrix ι ι ℂ)) β = ((Fintype.card ι : ℝ)⁻¹) • 1 := by
  have he := gibbs_energy_shift (H := (0 : Matrix ι ι ℂ)) c β
  simpa [gibbs, partition, boltzmann, Matrix.trace_one] using he

theorem heisenberg_scalar (c ℏ t : ℝ) (X : Matrix ι ι ℂ) :
    heisenberg ((c : ℂ) • 1) ℏ t X = X := conjugate_scalar _ _ _

theorem modular_scalar [Nonempty ι] (c β s : ℝ)
    (h : ((c : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian) (X : Matrix ι ι ℂ) :
    modular h β s X = X := by rw [modular_conjugate]; exact conjugate_scalar _ _ _

theorem twoLevel_pauliX_sign_flip {Δ β : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β) :
    modular (twoLevel_hermitian Δ) β (Real.pi / (β * Δ)) pauliX = -pauliX := by
  have hx : pauliX = E01 + E01ᴴ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, E01, Matrix.single]
  rw [hx, modular_add, modular_star, twoLevel_sign_flip hΔ hβ]
  simp [add_comm]

theorem twoLevel_nontrivial {Δ β : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β) :
    modular (twoLevel_hermitian Δ) β (Real.pi / (β * Δ)) E01 ≠ E01 := by
  rw [twoLevel_sign_flip hΔ hβ]
  intro h
  have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 0 1) h
  norm_num [E01, Matrix.single] at hh

theorem heisenberg_add (H : Matrix ι ι ℂ) (ℏ t : ℝ) (X Y : Matrix ι ι ℂ) :
    heisenberg H ℏ t (X + Y) = heisenberg H ℏ t X + heisenberg H ℏ t Y := conjugate_add _ _ _ _
theorem heisenberg_smul (H : Matrix ι ι ℂ) (ℏ t : ℝ) (z : ℂ) (X : Matrix ι ι ℂ) :
    heisenberg H ℏ t (z • X) = z • heisenberg H ℏ t X := conjugate_smul _ _ _ _
theorem heisenberg_one (H : Matrix ι ι ℂ) (ℏ t : ℝ) : heisenberg H ℏ t 1 = 1 := conjugate_one _ _
theorem heisenberg_mul (H : Matrix ι ι ℂ) (ℏ t : ℝ) (X Y : Matrix ι ι ℂ) :
    heisenberg H ℏ t (X * Y) = heisenberg H ℏ t X * heisenberg H ℏ t Y := conjugate_mul _ _ _ _
theorem heisenberg_star {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ℏ t : ℝ) (X : Matrix ι ι ℂ) :
    heisenberg H ℏ t Xᴴ = (heisenberg H ℏ t X)ᴴ := by
  simpa only [heisenberg, Complex.ofReal_div] using conjugate_star hH (t / ℏ) X
theorem heisenberg_zero (H X : Matrix ι ι ℂ) (ℏ : ℝ) : heisenberg H ℏ 0 X = X := by
  simp [heisenberg, conjugate_zero]
theorem heisenberg_group (H : Matrix ι ι ℂ) (ℏ s t : ℝ) (X : Matrix ι ι ℂ) :
    heisenberg H ℏ (s + t) X = heisenberg H ℏ s (heisenberg H ℏ t X) := by
  simp only [heisenberg, add_div, Complex.ofReal_add, mul_add, conjugate_group]
theorem heisenberg_inverse (H : Matrix ι ι ℂ) (ℏ t : ℝ) (X : Matrix ι ι ℂ) :
    heisenberg H ℏ (-t) (heisenberg H ℏ t X) = X := by
  rw [← heisenberg_group]
  simpa using heisenberg_zero H X ℏ

/-- Modular evolution fixes every entry within an equal-energy block. -/
theorem modular_degenerate_entry [Nonempty ι] (e : ι → ℝ)
    (hH : (diagonal (fun i => (e i : ℂ))).IsHermitian) (β s : ℝ)
    (X : Matrix ι ι ℂ) (i j : ι) (hij : e i = e j) :
    modular hH β s X i j = X i j := by
  rw [modular_conjugate]
  exact degenerate_entry_fixed _ _ X i j (congrArg (fun x : ℝ => (x : ℂ)) hij)

end SKEFTHawking.QuantumNetwork.FiniteGibbsClock
