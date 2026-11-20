import SKEFTHawking.QuantumNetwork.FiniteAdaptiveMixtureSurvival
import SKEFTHawking.QuantumNetwork.HelstromDiscrimination

/-! Attained binary discrimination of finite unnormalized branch families.
The first readout outcome chooses hypothesis A. The same history-indexed effects
are used under both hypotheses, without conditioning on positive branch mass. -/
namespace SKEFTHawking.QuantumNetwork
open Matrix
open scoped BigOperators ComplexOrder

namespace FiniteAdaptiveReadoutDiscrimination
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H]

/-- A positive branch family normalized only after summing all histories. -/
def IsBranchFamily (A : H → Matrix ι ι ℂ) : Prop :=
  (∀ h, (A h).PosSemidef) ∧ ∑ h, (A h).trace.re = 1

noncomputable def branchDistance (A B : H → Matrix ι ι ℂ) : ℝ :=
  ∑ h, traceDist (A h) (B h)

/-- Born probabilities for every allowed binary effect family. -/
noncomputable def effectTable (E Z : H → Matrix ι ι ℂ) (h : H) (a : Fin 2) : ℝ :=
  if a = 0 then (E h * Z h).trace.re else ((1 - E h) * Z h).trace.re

theorem effectTable_nonneg {E Z : H → Matrix ι ι ℂ}
    (hE : ∀ h, IsBinaryPOVM (E h)) (hZ : IsBranchFamily Z) (h : H) (a : Fin 2) :
    0 ≤ effectTable E Z h a := by
  unfold effectTable
  split
  · exact (Complex.le_def.mp (trace_mul_nonneg (hE h).1 (hZ.1 h))).1
  · exact (Complex.le_def.mp (trace_mul_nonneg (hE h).2 (hZ.1 h))).1

theorem effectTable_total (E : H → Matrix ι ι ℂ)
    {Z : H → Matrix ι ι ℂ} (hZ : IsBranchFamily Z) :
    ∑ h, ∑ a, effectTable E Z h a = 1 := by
  simp only [Fin.sum_univ_two, effectTable]
  norm_num only [ite_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
  calc
    _ = ∑ h, (Z h).trace.re := by apply Finset.sum_congr rfl; intro h _; ring
    _ = 1 := hZ.2

noncomputable def readoutError (A B E : H → Matrix ι ι ℂ) : ℝ :=
  ((∑ h, (E h * B h).trace.re) + (∑ h, ((1 - E h) * A h).trace.re)) / 2

/-- The cancellation uses total mass, never equality of individual branch masses. -/
theorem readoutError_eq (A B E : H → Matrix ι ι ℂ)
    (hA : ∑ h, (A h).trace.re = 1) :
    readoutError A B E = (1 - ∑ h, (E h * (A h - B h)).trace.re) / 2 := by
  simp only [readoutError, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    Complex.sub_re, Matrix.mul_sub, Finset.sum_sub_distrib, hA]
  ring

theorem branchDistance_eq_eigPosSum {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    branchDistance A B =
      ∑ h, eigPosSum ((hA.1 h).isHermitian.sub (hB.1 h).isHermitian) := by
  unfold branchDistance traceDist
  simp_rw [traceNorm_hermitian_eq ((hA.1 _).isHermitian.sub (hB.1 _).isHermitian),
    Matrix.trace_sub, Complex.sub_re]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  nlinarith [hA.2, hB.2]

theorem readoutError_lower {A B E : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) (hE : ∀ h, IsBinaryPOVM (E h)) :
    (1 - branchDistance A B) / 2 ≤ readoutError A B E := by
  have hb : (∑ h, (E h * (A h - B h)).trace.re) ≤
      ∑ h, eigPosSum ((hA.1 h).isHermitian.sub (hB.1 h).isHermitian) := by
    apply Finset.sum_le_sum
    intro h _
    rw [Matrix.trace_mul_comm, eigPosSum_eq_re_trace_posPart]
    exact re_trace_mul_le_trace_posPart
      ((hA.1 h).isHermitian.sub (hB.1 h).isHermitian) (hE h).1 (hE h).2
  rw [readoutError_eq A B E hA.2, branchDistance_eq_eigPosSum hA hB]
  linarith

noncomputable def optimalEffect {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) (h : H) : Matrix ι ι ℂ :=
  posProj ((hA.1 h).isHermitian.sub (hB.1 h).isHermitian)

theorem optimalEffect_admissible {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) (h : H) :
    IsBinaryPOVM (optimalEffect hA hB h) :=
  isBinaryPOVM_of_projection (posProj_isHermitian _) (posProj_idem _)

theorem optimalEffect_attains {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    readoutError A B (optimalEffect hA hB) = (1 - branchDistance A B) / 2 := by
  rw [readoutError_eq A B _ hA.2, branchDistance_eq_eigPosSum hA hB]
  simp_rw [eigPosSum_eq_re_trace_posProj]
  rfl

theorem readoutError_isLeast {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    IsLeast {x : ℝ | ∃ E : H → Matrix ι ι ℂ,
      (∀ h, IsBinaryPOVM (E h)) ∧ readoutError A B E = x}
      ((1 - branchDistance A B) / 2) := by
  refine ⟨⟨optimalEffect hA hB, optimalEffect_admissible hA hB,
    optimalEffect_attains hA hB⟩, ?_⟩
  rintro x ⟨E, hE, rfl⟩
  exact readoutError_lower hA hB hE

/-- A physical binary projective instrument, with one Kraus operator per outcome. -/
noncomputable def projectiveReadout (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) : FiniteInstrument ι 2 where
  count := 1
  operators a _ := if a = 0 then P else 1 - P
  normalized := by
    simp only [Fin.sum_univ_two, Fin.sum_univ_one]
    norm_num only [show (1 : Fin 2) ≠ 0 by decide, if_false, ite_true]
    rw [hP.eq, (Matrix.isHermitian_one.sub hP).eq]
    have hc : (1 - P) * (1 - P) = 1 - P := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hPP, sub_self, sub_zero]
    rw [hPP, hc]
    abel

theorem projectiveReadout_branch_zero (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (Z : Matrix ι ι ℂ) :
    (projectiveReadout P hP hPP).branch 0 Z = P * Z * P := by
  simp [projectiveReadout, FiniteInstrument.branch, krausMap, hP.eq]

theorem projectiveReadout_branch_one (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (Z : Matrix ι ι ℂ) :
    (projectiveReadout P hP hPP).branch 1 Z = (1 - P) * Z * (1 - P) := by
  simp [projectiveReadout, FiniteInstrument.branch, krausMap, hP.eq]

theorem projectiveReadout_weight_zero (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (Z : Matrix ι ι ℂ) :
    (projectiveReadout P hP hPP).weight 0 Z = (P * Z).trace.re := by
  rw [FiniteInstrument.weight, projectiveReadout_branch_zero, Matrix.trace_mul_cycle, hPP]

theorem projectiveReadout_weight_one (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (Z : Matrix ι ι ℂ) :
    (projectiveReadout P hP hPP).weight 1 Z = ((1 - P) * Z).trace.re := by
  rw [FiniteInstrument.weight, projectiveReadout_branch_one, Matrix.trace_mul_cycle]
  have hc : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hPP, sub_self, sub_zero]
  rw [hc]

noncomputable def optimalReadout {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) (h : H) : FiniteInstrument ι 2 :=
  projectiveReadout (optimalEffect hA hB h) (posProj_isHermitian _) (posProj_idem _)

/-- Joint history/readout probabilities are actual instrument trace weights. -/
noncomputable def readoutTable (I : H → FiniteInstrument ι 2)
    (Z : H → Matrix ι ι ℂ) (h : H) (a : Fin 2) : ℝ := (I h).weight a (Z h)

theorem readoutTable_nonneg (I : H → FiniteInstrument ι 2)
    {Z : H → Matrix ι ι ℂ} (hZ : IsBranchFamily Z) (h : H) (a : Fin 2) :
    0 ≤ readoutTable I Z h a := (I h).weight_nonneg a (hZ.1 h)

theorem readoutTable_total (I : H → FiniteInstrument ι 2)
    {Z : H → Matrix ι ι ℂ} (hZ : IsBranchFamily Z) :
    ∑ h, ∑ a, readoutTable I Z h a = 1 := by
  simp only [readoutTable, FiniteInstrument.sum_weight]
  exact hZ.2

/-- The attaining abstract effects are realized by the normalized Kraus instruments. -/
theorem optimalReadout_error {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hB : IsBranchFamily B) :
    ((∑ h, readoutTable (optimalReadout hA hB) B h 0) +
      (∑ h, readoutTable (optimalReadout hA hB) A h 1)) / 2 =
        (1 - branchDistance A B) / 2 := by
  simp only [readoutTable, optimalReadout, projectiveReadout_weight_zero,
    projectiveReadout_weight_one]
  exact optimalEffect_attains hA hB

/-! A genuinely complex, noncommuting qubit guard. -/
noncomputable def qubitX : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 + pauliX)
noncomputable def qubitY : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 + pauliY)
noncomputable def invSqrtTwo : ℝ := 1 / Real.sqrt 2

theorem invSqrtTwo_pos : 0 < invSqrtTwo := by unfold invSqrtTwo; positivity

theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = 1/2 := by
  unfold invSqrtTwo
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem invSqrtTwo_complex_sq : (invSqrtTwo : ℂ) ^ 2 = 1/2 := by
  rw [← Complex.ofReal_pow, invSqrtTwo_sq]
  norm_num

theorem qubitX_hermitian : qubitX.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, pauliX, Matrix.conjTranspose_apply, Matrix.one_apply]

theorem qubitY_hermitian : qubitY.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitY, pauliY, Matrix.conjTranspose_apply, Matrix.one_apply]

theorem qubitX_idem : qubitX * qubitX = qubitX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX, pauliX, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]

theorem qubitY_idem : qubitY * qubitY = qubitY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitY, pauliY, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two,
      Complex.I_sq] <;> ring_nf <;> norm_num

theorem qubitX_density : IsDensityOperator qubitX := by
  refine ⟨(isBinaryPOVM_of_projection qubitX_hermitian qubitX_idem).1, ?_⟩
  norm_num [qubitX, pauliX, Matrix.trace, Fin.sum_univ_two]

theorem qubitY_density : IsDensityOperator qubitY := by
  refine ⟨(isBinaryPOVM_of_projection qubitY_hermitian qubitY_idem).1, ?_⟩
  norm_num [qubitY, pauliY, Matrix.trace, Fin.sum_univ_two]

theorem qubit_noncommuting : qubitX * qubitY ≠ qubitY * qubitX := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).im) h
  norm_num [qubitX, qubitY, pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two] at he

noncomputable def qubitDirection : Matrix (Fin 2) (Fin 2) ℂ :=
  (invSqrtTwo : ℂ) • (pauliX - pauliY)

noncomputable def qubitProjector : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (1 + qubitDirection)

theorem qubitDirection_hermitian : qubitDirection.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitDirection, pauliX, pauliY, sub_eq_add_neg]

theorem qubitDirection_sq : qubitDirection * qubitDirection = 1 := by
  rw [qubitDirection, smul_mul_smul]
  have hh : (pauliX - pauliY) * (pauliX - pauliY) = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pauliX, pauliY, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;> ring_nf <;> norm_num
  rw [hh, smul_smul, ← sq, invSqrtTwo_complex_sq]
  norm_num

theorem qubitProjector_hermitian : qubitProjector.IsHermitian := by
  change qubitProjectorᴴ = qubitProjector
  rw [qubitProjector, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, qubitDirection_hermitian.eq]
  norm_num

theorem qubitProjector_idem : qubitProjector * qubitProjector = qubitProjector := by
  rw [qubitProjector, smul_mul_smul]
  have h : (1 + qubitDirection) * (1 + qubitDirection) =
      (2 : ℂ) • (1 + qubitDirection) := by
    rw [add_mul, one_mul, mul_add, mul_one, qubitDirection_sq]
    module
  rw [h, smul_smul]
  norm_num

/-- The actual normalized two-outcome instrument for the complex guard. -/
noncomputable def qubitReadout : FiniteInstrument (Fin 2) 2 :=
  projectiveReadout qubitProjector qubitProjector_hermitian qubitProjector_idem

theorem qubit_difference_square : (qubitX - qubitY)ᴴ * (qubitX - qubitY) =
    (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [(qubitX_hermitian.sub qubitY_hermitian).eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitX,qubitY,pauliX,pauliY,Matrix.mul_apply,Matrix.one_apply,
      Fin.sum_univ_two] <;> ring_nf <;> norm_num

theorem qubit_distance : traceDist qubitX qubitY = invSqrtTwo := by
  have ha : absOp (qubitX - qubitY) =
      (invSqrtTwo : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _)
      (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr invSqrtTwo_pos.le)) ?_
    rw [absOp_mul_self, qubit_difference_square, smul_mul_smul, one_mul,
      ← sq, invSqrtTwo_complex_sq]
  rw [traceDist, traceNorm_eq_trace_absOp, ha]
  norm_num [Matrix.trace_smul, Matrix.trace, Fin.sum_univ_two]
  ring

theorem qubit_readout_error :
    (qubitReadout.weight 0 qubitY + qubitReadout.weight 1 qubitX) / 2 =
      (1 - 1 / Real.sqrt 2) / 2 := by
  rw [qubitReadout, projectiveReadout_weight_zero, projectiveReadout_weight_one]
  norm_num [qubitProjector, qubitDirection, qubitX, qubitY, pauliX, pauliY,
    Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply,
    invSqrtTwo, Complex.mul_re, Complex.mul_im]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

theorem qubit_readout_probabilities :
    qubitReadout.weight 0 qubitX = (1 + invSqrtTwo)/2 ∧
    qubitReadout.weight 1 qubitX = (1 - invSqrtTwo)/2 ∧
    qubitReadout.weight 0 qubitY = (1 - invSqrtTwo)/2 ∧
    qubitReadout.weight 1 qubitY = (1 + invSqrtTwo)/2 := by
  simp only [qubitReadout, projectiveReadout_weight_zero, projectiveReadout_weight_one]
  norm_num [qubitProjector, qubitDirection, qubitX, qubitY, pauliX, pauliY,
    Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply,
    Complex.mul_re, Complex.mul_im]
  refine ⟨?_, ?_, ?_⟩ <;> ring

omit [DecidableEq ι] in
/-- Singleton history gives ordinary density discrimination without an index identification. -/
theorem singleton_family {Z : Matrix ι ι ℂ} (hZ : IsDensityOperator Z) :
    IsBranchFamily (fun _ : Unit => Z) := by
  refine ⟨fun _ => hZ.1, ?_⟩
  simp [hZ.2]

theorem singleton_distance (A B : Matrix ι ι ℂ) :
    branchDistance (fun _ : Unit => A) (fun _ : Unit => B) = traceDist A B := by
  simp [branchDistance]

theorem complex_guard_isLeast :
    IsLeast {x : ℝ | ∃ E : Unit → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ h, IsBinaryPOVM (E h)) ∧
        readoutError (fun _ => qubitX) (fun _ => qubitY) E = x}
      ((1 - 1 / Real.sqrt 2) / 2) := by
  have h := readoutError_isLeast (singleton_family qubitX_density) (singleton_family qubitY_density)
  simpa only [singleton_distance, qubit_distance, invSqrtTwo] using h

/-- Unequal positive mass, a one-sided impossible branch, and a common impossible branch. -/
noncomputable def unequalA : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := fun h => if h = 0 then qubitX else 0
noncomputable def unequalB : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun h => if h = 0 then (1/4 : ℂ) • qubitX else if h = 1 then (3/4 : ℂ) • qubitX else 0

theorem unequalA_family : IsBranchFamily unequalA := by
  refine ⟨?_, ?_⟩
  · intro h; fin_cases h
    · exact qubitX_density.1
    · exact Matrix.PosSemidef.zero
    · exact Matrix.PosSemidef.zero
  · simp [unequalA, Fin.sum_univ_three, qubitX_density.2]

theorem unequalB_family : IsBranchFamily unequalB := by
  refine ⟨?_, ?_⟩
  · intro h; fin_cases h
    · exact qubitX_density.1.smul (by norm_num [Complex.le_def])
    · exact qubitX_density.1.smul (by norm_num [Complex.le_def])
    · exact Matrix.PosSemidef.zero
  · norm_num [unequalB, Fin.sum_univ_three, Matrix.trace_smul, qubitX_density.2,
      show (2:Fin 3) ≠ 0 by decide, show (2:Fin 3) ≠ 1 by decide]

theorem unequal_masses : (unequalA 0).trace.re = 1 ∧ (unequalB 0).trace.re = 1/4 ∧
    unequalA 1 = 0 ∧ (unequalB 1).trace.re = 3/4 ∧ unequalA 2 = 0 ∧ unequalB 2 = 0 := by
  norm_num [unequalA, unequalB, Matrix.trace_smul, qubitX_density.2,
    show (2:Fin 3) ≠ 0 by decide, show (2:Fin 3) ≠ 1 by decide]

theorem unequal_distance : branchDistance unequalA unequalB = 3/4 := by
  have h0 : qubitX - (1/4 : ℂ) • qubitX = (3/4 : ℂ) • qubitX := by module
  simp only [branchDistance, Fin.sum_univ_three, unequalA, unequalB, traceDist]
  norm_num only [ite_true, show (1:Fin 3) ≠ 0 by decide, show (2:Fin 3) ≠ 0 by decide,
    show (2:Fin 3) ≠ 1 by decide, if_false]
  rw [h0, zero_sub, traceNorm_neg, traceNorm_zero]
  have hn := traceNorm_density_eq_one qubitX_density
  have hscale : traceNorm ((3/4 : ℂ) • qubitX) = 3/4 := by
    have h := traceNorm_smul_nonneg (show (0:ℝ) ≤ 3/4 by norm_num) qubitX
    norm_num [hn] at h ⊢
    exact h
  rw [hscale]
  norm_num

theorem unequal_actual_optimum :
    ((∑ h, readoutTable (optimalReadout unequalA_family unequalB_family) unequalB h 0) +
      (∑ h, readoutTable (optimalReadout unequalA_family unequalB_family) unequalA h 1))/2 = 1/8 := by
  rw [optimalReadout_error, unequal_distance]
  norm_num

theorem unequal_isLeast :
    IsLeast {x : ℝ | ∃ E : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ h, IsBinaryPOVM (E h)) ∧ readoutError unequalA unequalB E = x} (1/8) := by
  have h := readoutError_isLeast unequalA_family unequalB_family
  norm_num [unequal_distance] at h ⊢
  exact h

/-! Operational specialization to the actual retained joint output. -/
open FiniteInterventionProcess FiniteAdaptiveMapPerturbation
open scoped Kronecker
variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
variable {o n : ℕ}

theorem run_family (T : Tree S E o n) {X : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) : IsBranchFamily (fun h => run S E o T h X) := by
  refine ⟨fun h => run_posSemidef S E o T h hX.1, ?_⟩
  simpa only [weight, hX.2, Complex.one_re] using sum_weight S E o T X

theorem tree_error_isLeast (T U : Tree S E o n)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    IsLeast {x : ℝ | ∃ F : History o n → Matrix (S × E) (S × E) ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run S E o T h X) (fun h => run S E o U h Y) F = x}
      ((1 - outputDistance S E o T U X Y)/2) := by
  simpa only [branchDistance, outputDistance, traceDist, div_eq_mul_inv,
    mul_comm, one_mul, Finset.mul_sum] using
    readoutError_isLeast (run_family T hX) (run_family U hY)

theorem tree_readout_probabilities (T : Tree S E o n)
    {X : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X)
    (I : History o n → FiniteInstrument (S × E) 2) :
    (∀ h a, 0 ≤ readoutTable I (fun h => run S E o T h X) h a) ∧
      (∑ h, ∑ a, readoutTable I (fun h => run S E o T h X) h a) = 1 :=
  ⟨readoutTable_nonneg I (run_family T hX), readoutTable_total I (run_family T hX)⟩

theorem tree_optimalReadout_error (T U : Tree S E o n)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    ((∑ h, readoutTable (optimalReadout (run_family T hX) (run_family U hY))
      (fun h => run S E o U h Y) h 0) +
     (∑ h, readoutTable (optimalReadout (run_family T hX) (run_family U hY))
      (fun h => run S E o T h X) h 1))/2 =
      (1 - outputDistance S E o T U X Y)/2 := by
  simpa only [branchDistance, outputDistance, traceDist, div_eq_mul_inv,
    mul_comm, one_mul, Finset.mul_sum] using
    optimalReadout_error (run_family T hX) (run_family U hY)

/-- The carrier is explicitly Fin 2 × Unit, with normalized singleton environment. -/
noncomputable def qubitJoint (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ := X ⊗ₖ (1 : Matrix Unit Unit ℂ)

theorem unit_density : IsDensityOperator (1 : Matrix Unit Unit ℂ) := by
  refine ⟨Matrix.PosSemidef.one, ?_⟩
  simp [Matrix.trace]

theorem qubitJoint_density {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (qubitJoint X) := by
  exact ⟨hX.1.kronecker unit_density.1, by
    rw [qubitJoint, Matrix.trace_kronecker, hX.2, unit_density.2, mul_one]⟩

theorem qubitJoint_distance (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    traceDist (qubitJoint X) (qubitJoint Y) = traceDist X Y :=
  FiniteAdaptiveProcessRobustness.traceDist_tensor_right unit_density X Y

theorem depth_zero_isLeast {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    IsLeast {x : ℝ | ∃ F : History 2 0 → Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run (Fin 2) Unit 2 .done h (qubitJoint X))
        (fun h => run (Fin 2) Unit 2 .done h (qubitJoint Y)) F = x}
      ((1 - traceDist X Y)/2) := by
  have hh := tree_error_isLeast (o := 2) (Tree.done : Tree (Fin 2) Unit 2 0) .done
    (qubitJoint_density hX) (qubitJoint_density hY)
  simpa only [outputDistance_done, qubitJoint_distance] using hh

open FiniteMemoryProcess
/-- Joint unitary that flips only the retained environment. -/
noncomputable def environmentX : Matrix Joint Joint ℂ :=
  (1 : Matrix Qubit Qubit ℂ) ⊗ₖ pauliX

theorem environmentX_hermitian : environmentX.IsHermitian := by
  change environmentXᴴ = environmentX
  simp [environmentX, Matrix.conjTranspose_kronecker, pauliX_conjTranspose]

theorem environmentX_sq : environmentX * environmentX = 1 := by
  rw [environmentX, ← Matrix.mul_kronecker_mul, Matrix.one_mul, pauliX_mul_self]
  exact Matrix.one_kronecker_one

noncomputable def environmentXKraus (_ : Fin 1) : Matrix Joint Joint ℂ := environmentX

theorem environmentX_normalized : IsKrausChannel environmentXKraus := by
  simp [IsKrausChannel, environmentXKraus, environmentX_hermitian.eq, environmentX_sq]

theorem environmentX_action (Z : Matrix Joint Joint ℂ) :
    krausMap environmentXKraus Z = environmentX * Z * environmentX := by
  simp [krausMap, environmentXKraus, environmentX_hermitian.eq]

theorem environmentX_basis (s e : Qubit) :
    krausMap environmentXKraus (basisState s ⊗ₖ basisState e) =
      basisState s ⊗ₖ basisState (1-e) := by
  rw [environmentX_action, environmentX, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  congr 1
  fin_cases e <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, basisState, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

noncomputable def flipPrepare : Step Qubit Qubit 2 :=
  realizedStep Qubit Qubit 2 environmentXKraus environmentX_normalized (FiniteInstrument.prepare 0)

noncomputable def correlationKeep : Tree Qubit Qubit 2 2 :=
  .node readStep (fun _ => .node identityPrepare (fun _ => .done))

noncomputable def correlationFlip : Tree Qubit Qubit 2 2 :=
  .node readStep (fun _ => .node flipPrepare (fun _ => .done))

theorem identityPrepare_basis (a s e : Qubit) :
    identityPrepare.branch Qubit Qubit 2 a (basisState s ⊗ₖ basisState e) =
      if a=0 then basisState 0 ⊗ₖ basisState e else 0 := by
  have hh := idealStep_basis 0 a s e
  by_cases ha : a=0
  · subst a; simpa only [identityPrepare, idealStep] using hh
  · simpa only [identityPrepare, idealStep, if_neg ha] using hh

theorem flipPrepare_basis (a s e : Qubit) :
    flipPrepare.branch Qubit Qubit 2 a (basisState s ⊗ₖ basisState e) =
      if a=0 then basisState 0 ⊗ₖ basisState (1-e) else 0 := by
  change ((FiniteInstrument.prepare 0).lift Qubit).branch a
    (krausMap environmentXKraus (basisState s ⊗ₖ basisState e)) = _
  rw [environmentX_basis, lift_branch_tensor, prepare_basis]
  split_ifs <;> simp_all

theorem correlationKeep_run (h a : Qubit) :
    run Qubit Qubit 2 correlationKeep (h,a,()) correlatedInput =
      if a=0 then (1/2 : ℂ) • (basisState 0 ⊗ₖ basisState h) else 0 := by
  change identityPrepare.branch Qubit Qubit 2 a
    (readStep.branch Qubit Qubit 2 h correlatedInput) = _
  rw [readStep_correlated, Step.branch_smul, identityPrepare_basis]
  split_ifs <;> simp

theorem correlationFlip_run (h a : Qubit) :
    run Qubit Qubit 2 correlationFlip (h,a,()) correlatedInput =
      if a=0 then (1/2 : ℂ) • (basisState 0 ⊗ₖ basisState (1-h)) else 0 := by
  change flipPrepare.branch Qubit Qubit 2 a
    (readStep.branch Qubit Qubit 2 h correlatedInput) = _
  rw [readStep_correlated, Step.branch_smul, flipPrepare_basis]
  split_ifs <;> simp

theorem correlation_weights (h a : Qubit) :
    weight Qubit Qubit 2 correlationKeep (h,a,()) correlatedInput =
      (if a=0 then 1/2 else 0) ∧
    weight Qubit Qubit 2 correlationFlip (h,a,()) correlatedInput =
      (if a=0 then 1/2 else 0) := by
  simp only [weight, correlationKeep_run, correlationFlip_run]
  split_ifs <;> simp [Matrix.trace_smul, (basisJoint_density 0 h).2,
    (basisJoint_density 0 (1-h)).2]

theorem correlationKeep_run_history (h : History 2 2) :
    run Qubit Qubit 2 correlationKeep h correlatedInput =
      if h.2.1=0 then (1/2 : ℂ) • (basisState 0 ⊗ₖ basisState h.1) else 0 := by
  rcases h with ⟨h,a,⟨⟩⟩
  exact correlationKeep_run h a

theorem correlationFlip_run_history (h : History 2 2) :
    run Qubit Qubit 2 correlationFlip h correlatedInput =
      if h.2.1=0 then (1/2 : ℂ) • (basisState 0 ⊗ₖ basisState (1-h.1)) else 0 := by
  rcases h with ⟨h,a,⟨⟩⟩
  exact correlationFlip_run h a

theorem correlation_same_history (h : History 2 2) :
    weight Qubit Qubit 2 correlationKeep h correlatedInput =
      weight Qubit Qubit 2 correlationFlip h correlatedInput := by
  rcases h with ⟨h,a,⟨⟩⟩
  exact (correlation_weights h a).1.trans (correlation_weights h a).2.symm

/-- Both unconditional joint marginals agree, although their history correlations differ. -/
theorem correlation_terminal :
    terminalState Qubit Qubit 2 correlationKeep correlatedInput =
      basisState 0 ⊗ₖ ((1/2 : ℂ) • (1 : Matrix Qubit Qubit ℂ)) ∧
    terminalState Qubit Qubit 2 correlationFlip correlatedInput =
      basisState 0 ⊗ₖ ((1/2 : ℂ) • (1 : Matrix Qubit Qubit ℂ)) := by
  simp only [terminalState, correlationKeep_run_history, correlationFlip_run_history]
  change (∑ h : Qubit × (Qubit × Unit), _) = _ ∧ (∑ h : Qubit × (Qubit × Unit), _) = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  constructor <;> ext ⟨i,e⟩ ⟨j,f⟩ <;>
    fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
    norm_num [basisState, Matrix.kronecker_apply, Matrix.one_apply]

/-- All randomized classical classifiers, with score meaning choose A. -/
noncomputable def historyError (A B : H → Matrix ι ι ℂ) (a : H → ℝ) : ℝ :=
  ((∑ h, a h * (B h).trace.re) +
    (∑ h, (1-a h) * (A h).trace.re))/2

omit [DecidableEq ι] in
theorem historyError_same_law {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (he : ∀ h, (A h).trace.re = (B h).trace.re)
    (a : H → ℝ) : historyError A B a = 1/2 := by
  unfold historyError
  simp_rw [← he]
  rw [← Finset.sum_add_distrib]
  have hh : (∑ h, (a h * (A h).trace.re + (1-a h) * (A h).trace.re)) =
      ∑ h, (A h).trace.re := by
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hh, hA.2]

theorem correlation_history_only (a : History 2 2 → ℝ)
    (_ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    historyError (fun h => run Qubit Qubit 2 correlationKeep h correlatedInput)
      (fun h => run Qubit Qubit 2 correlationFlip h correlatedInput) a = 1/2 :=
  historyError_same_law (run_family correlationKeep correlatedInput_density)
    correlation_same_history a

theorem historyError_scalar_effect (A B : H → Matrix ι ι ℂ) (a : H → ℝ) :
    readoutError A B (fun h => (a h : ℂ) • 1) = historyError A B a := by
  simp only [readoutError, historyError, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  ring

omit [Fintype ι] [Fintype H] in
theorem scalar_effect_admissible (a : H → ℝ)
    (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) (h : H) :
    IsBinaryPOVM ((a h : ℂ) • (1 : Matrix ι ι ℂ)) := by
  refine ⟨Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (ha h).1), ?_⟩
  have he : (1 : Matrix ι ι ℂ) - (a h : ℂ) • 1 = ((1-a h : ℝ) : ℂ) • 1 := by
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  rw [he]
  exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr (ha h).2))

theorem constant_error_same_terminal {A B : H → Matrix ι ι ℂ}
    (hA : IsBranchFamily A) (hs : ∑ h, A h = ∑ h, B h) (F : Matrix ι ι ℂ) :
    readoutError A B (fun _ => F) = 1/2 := by
  rw [readoutError_eq _ _ _ hA.2]
  have he : ∑ h, (F * (A h-B h)).trace.re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum,
      Finset.sum_sub_distrib, hs, sub_self, Matrix.mul_zero, Matrix.trace_zero,
      Complex.zero_re]
  rw [he]
  norm_num

theorem correlation_terminal_only (F : Matrix Joint Joint ℂ)
    (_hF : IsBinaryPOVM F) :
    readoutError (fun h => run Qubit Qubit 2 correlationKeep h correlatedInput)
      (fun h => run Qubit Qubit 2 correlationFlip h correlatedInput)
      (fun _ => F) = 1/2 := by
  apply constant_error_same_terminal (run_family correlationKeep correlatedInput_density)
  exact correlation_terminal.1.trans correlation_terminal.2.symm

/-- A fixed computational-basis measurement on E followed by classical relabeling from h. -/
noncomputable def correlationEffect (h : History 2 2) : Matrix Joint Joint ℂ :=
  (1 : Matrix Qubit Qubit ℂ) ⊗ₖ basisState h.1

theorem basis_idempotent (a : Qubit) : basisState a * basisState a = basisState a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [basisState, Matrix.mul_apply]

theorem correlationEffect_hermitian (h : History 2 2) :
    (correlationEffect h).IsHermitian := by
  change (correlationEffect h)ᴴ = correlationEffect h
  simp only [correlationEffect, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, (basisState_density h.1).1.isHermitian.eq]

theorem correlationEffect_idem (h : History 2 2) :
    correlationEffect h * correlationEffect h = correlationEffect h := by
  rw [correlationEffect, ← Matrix.mul_kronecker_mul, Matrix.one_mul, basis_idempotent]

noncomputable def correlationReadout (h : History 2 2) : FiniteInstrument Joint 2 :=
  projectiveReadout (correlationEffect h) (correlationEffect_hermitian h)
    (correlationEffect_idem h)

theorem correlationReadout_weight_zero (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    (correlationReadout h).weight 0 Z = (correlationEffect h * Z).trace.re :=
  projectiveReadout_weight_zero _ _ _ _

theorem correlationReadout_weight_one (h : History 2 2) (Z : Matrix Joint Joint ℂ) :
    (correlationReadout h).weight 1 Z = ((1-correlationEffect h) * Z).trace.re :=
  projectiveReadout_weight_one _ _ _ _

theorem correlation_readout_table (k : History 2 2) (b : Qubit) :
    readoutTable correlationReadout
      (fun h => run Qubit Qubit 2 correlationKeep h correlatedInput) k b =
      (if k.2.1=0 ∧ b=0 then 1/2 else 0) ∧
    readoutTable correlationReadout
      (fun h => run Qubit Qubit 2 correlationFlip h correlatedInput) k b =
      (if k.2.1=0 ∧ b=1 then 1/2 else 0) := by
  fin_cases b
  · change (correlationReadout k).weight 0 (run Qubit Qubit 2 correlationKeep k correlatedInput) = _ ∧
      (correlationReadout k).weight 0 (run Qubit Qubit 2 correlationFlip k correlatedInput) = _
    rw [correlationReadout_weight_zero, correlationReadout_weight_zero,
      correlationKeep_run_history, correlationFlip_run_history]
    rcases k with ⟨h,a,u⟩
    fin_cases h <;> fin_cases a <;>
      norm_num [correlationEffect, Matrix.mul_apply, Matrix.trace, Matrix.kronecker_apply,
        basisState, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  · change (correlationReadout k).weight 1 (run Qubit Qubit 2 correlationKeep k correlatedInput) = _ ∧
      (correlationReadout k).weight 1 (run Qubit Qubit 2 correlationFlip k correlatedInput) = _
    rw [correlationReadout_weight_one, correlationReadout_weight_one,
      correlationKeep_run_history, correlationFlip_run_history]
    rcases k with ⟨h,a,u⟩
    fin_cases h <;> fin_cases a <;>
      norm_num [correlationEffect, Matrix.mul_apply, Matrix.trace, Matrix.kronecker_apply,
        basisState, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem correlation_readout_error_zero :
    ((∑ h, readoutTable correlationReadout
      (fun k => run Qubit Qubit 2 correlationFlip k correlatedInput) h 0) +
     (∑ h, readoutTable correlationReadout
      (fun k => run Qubit Qubit 2 correlationKeep k correlatedInput) h 1))/2 = 0 := by
  have hB : ∀ h, readoutTable correlationReadout
      (fun k => run Qubit Qubit 2 correlationFlip k correlatedInput) h 0 = 0 := by
    intro h
    simpa using (correlation_readout_table h 0).2
  have hA : ∀ h, readoutTable correlationReadout
      (fun k => run Qubit Qubit 2 correlationKeep k correlatedInput) h 1 = 0 := by
    intro h
    simpa using (correlation_readout_table h 1).1
  simp only [hB, hA, Finset.sum_const_zero, zero_add, zero_div]

theorem correlation_effect_error_zero :
    readoutError (fun h => run Qubit Qubit 2 correlationKeep h correlatedInput)
      (fun h => run Qubit Qubit 2 correlationFlip h correlatedInput) correlationEffect = 0 := by
  have hh := correlation_readout_error_zero
  simpa only [readoutTable, correlationReadout_weight_zero, correlationReadout_weight_one,
    readoutError] using hh

theorem correlation_outputDistance_one :
    outputDistance Qubit Qubit 2 correlationKeep correlationFlip correlatedInput correlatedInput = 1 := by
  have hl := readoutError_lower (run_family correlationKeep correlatedInput_density)
    (run_family correlationFlip correlatedInput_density)
    (fun h => isBinaryPOVM_of_projection (correlationEffect_hermitian h) (correlationEffect_idem h))
  have hu := outputDistance_mass Qubit Qubit 2 correlationKeep correlationFlip
    correlatedInput_density.1 correlatedInput_density.1
  rw [correlation_effect_error_zero] at hl
  have he : branchDistance (fun h => run Qubit Qubit 2 correlationKeep h correlatedInput)
      (fun h => run Qubit Qubit 2 correlationFlip h correlatedInput) =
      outputDistance Qubit Qubit 2 correlationKeep correlationFlip correlatedInput correlatedInput := by
    simp only [branchDistance, outputDistance, traceDist, div_eq_mul_inv,
      one_mul, mul_comm, Finset.mul_sum]
  rw [he] at hl
  rw [correlatedInput_density.2] at hu
  norm_num only [Complex.one_re] at hu
  linarith

theorem correlation_error_isLeast :
    IsLeast {x : ℝ | ∃ F : History 2 2 → Matrix Joint Joint ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run Qubit Qubit 2 correlationKeep h correlatedInput)
        (fun h => run Qubit Qubit 2 correlationFlip h correlatedInput) F = x} 0 := by
  have hh := tree_error_isLeast correlationKeep correlationFlip
    correlatedInput_density correlatedInput_density
  simpa only [correlation_outputDistance_one, sub_self, zero_div] using hh

theorem correlation_readout_normalized :
    (∀ h a, 0 ≤ readoutTable correlationReadout
      (fun k => run Qubit Qubit 2 correlationKeep k correlatedInput) h a) ∧
    (∑ h, ∑ a, readoutTable correlationReadout
      (fun k => run Qubit Qubit 2 correlationKeep k correlatedInput) h a) = 1 ∧
    (∀ h a, 0 ≤ readoutTable correlationReadout
      (fun k => run Qubit Qubit 2 correlationFlip k correlatedInput) h a) ∧
    (∑ h, ∑ a, readoutTable correlationReadout
      (fun k => run Qubit Qubit 2 correlationFlip k correlatedInput) h a) = 1 := by
  exact ⟨(tree_readout_probabilities correlationKeep correlatedInput_density correlationReadout).1,
    (tree_readout_probabilities correlationKeep correlatedInput_density correlationReadout).2,
    tree_readout_probabilities correlationFlip correlatedInput_density correlationReadout⟩

noncomputable def fixedEnvironmentProjector : Matrix Joint Joint ℂ :=
  (1 : Matrix Qubit Qubit ℂ) ⊗ₖ basisState 0

theorem fixedEnvironmentProjector_hermitian : fixedEnvironmentProjector.IsHermitian :=
  correlationEffect_hermitian (0,0,())

theorem fixedEnvironmentProjector_idem :
    fixedEnvironmentProjector * fixedEnvironmentProjector = fixedEnvironmentProjector :=
  correlationEffect_idem (0,0,())

noncomputable def fixedEnvironmentReadout : FiniteInstrument Joint 2 :=
  projectiveReadout fixedEnvironmentProjector
    fixedEnvironmentProjector_hermitian fixedEnvironmentProjector_idem

theorem correlationEffect_relabel (k : History 2 2) :
    correlationEffect k =
      if k.1=0 then fixedEnvironmentProjector else 1-fixedEnvironmentProjector := by
  rcases k with ⟨h,a,u⟩
  fin_cases h <;> ext ⟨i,e⟩ ⟨j,f⟩ <;>
    fin_cases i <;> fin_cases e <;> fin_cases j <;> fin_cases f <;>
    norm_num [correlationEffect, fixedEnvironmentProjector, Matrix.kronecker_apply,
      basisState, Matrix.one_apply]

/-- Only the classical outcome label changes with history; the physical measurement is fixed. -/
theorem correlationReadout_fixed_relabel (k : History 2 2) (b : Qubit)
    (Z : Matrix Joint Joint ℂ) :
    (correlationReadout k).weight b Z =
      fixedEnvironmentReadout.weight (if k.1=0 then b else 1-b) Z := by
  have hc : correlationEffect k = if k.1=0 then fixedEnvironmentProjector else 1-fixedEnvironmentProjector :=
    correlationEffect_relabel k
  by_cases hk : k.1=0
  · rw [if_pos hk]
    fin_cases b
    · change (correlationReadout k).weight 0 Z = fixedEnvironmentReadout.weight 0 Z
      rw [correlationReadout_weight_zero, fixedEnvironmentReadout, projectiveReadout_weight_zero,
        hc, if_pos hk]
    · change (correlationReadout k).weight 1 Z = fixedEnvironmentReadout.weight 1 Z
      rw [correlationReadout_weight_one, fixedEnvironmentReadout, projectiveReadout_weight_one,
        hc, if_pos hk]
  · rw [if_neg hk]
    fin_cases b
    · change (correlationReadout k).weight 0 Z = fixedEnvironmentReadout.weight (1-0) Z
      rw [sub_zero]
      rw [correlationReadout_weight_zero, fixedEnvironmentReadout, projectiveReadout_weight_one,
        hc, if_neg hk]
    · change (correlationReadout k).weight 1 Z = fixedEnvironmentReadout.weight (1-1) Z
      rw [sub_self]
      rw [correlationReadout_weight_one, fixedEnvironmentReadout, projectiveReadout_weight_zero,
        hc, if_neg hk]
      rw [sub_sub_cancel]

theorem equal_tree_error_isLeast (T : Tree S E o n)
    {X : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) :
    IsLeast {x : ℝ | ∃ F : History o n → Matrix (S × E) (S × E) ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run S E o T h X) (fun h => run S E o T h X) F = x} (1/2) := by
  have hh := tree_error_isLeast T T hX hX
  have hd : outputDistance S E o T T X X = 0 := by
    simp [outputDistance, traceNorm_zero]
  simpa only [hd, sub_zero] using hh

theorem orthogonal_depth_zero :
    IsLeast {x : ℝ | ∃ F : History 2 0 → Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run (Fin 2) Unit 2 .done h (qubitJoint (basisState 1)))
        (fun h => run (Fin 2) Unit 2 .done h (qubitJoint (basisState 0))) F = x} 0 := by
  have hh := depth_zero_isLeast (basisState_density 1) (basisState_density 0)
  simpa only [basis_one_zero_distance, sub_self, zero_div] using hh

theorem correlation_history_scalar_error (a : History 2 2 → ℝ)
    (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    readoutError (fun h => run Qubit Qubit 2 correlationKeep h correlatedInput)
      (fun h => run Qubit Qubit 2 correlationFlip h correlatedInput)
      (fun h => (a h : ℂ) • 1) = 1/2 := by
  rw [historyError_scalar_effect]
  exact correlation_history_only a ha

theorem correlation_history_error_isLeast :
    IsLeast {x : ℝ | ∃ a : History 2 2 → ℝ,
      (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) ∧
      historyError (fun h => run Qubit Qubit 2 correlationKeep h correlatedInput)
        (fun h => run Qubit Qubit 2 correlationFlip h correlatedInput) a = x} (1/2) := by
  refine ⟨⟨fun _ => 0, fun _ => by norm_num, correlation_history_only _ (fun _ => by norm_num)⟩, ?_⟩
  rintro x ⟨a,ha,rfl⟩
  exact (correlation_history_only a ha).symm.le

theorem correlation_marginal_distances_zero :
    historyVariation Qubit Qubit 2 correlationKeep correlationFlip correlatedInput correlatedInput = 0 ∧
    traceDist (terminalState Qubit Qubit 2 correlationKeep correlatedInput)
      (terminalState Qubit Qubit 2 correlationFlip correlatedInput) = 0 := by
  constructor
  · simp only [historyVariation, correlation_same_history, sub_self, abs_zero,
      Finset.sum_const_zero, zero_div]
  · rw [correlation_terminal.1, correlation_terminal.2]
    simp [traceDist, traceNorm_zero]

theorem complex_depth_zero_isLeast :
    IsLeast {x : ℝ | ∃ F : History 2 0 → Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run (Fin 2) Unit 2 .done h (qubitJoint qubitX))
        (fun h => run (Fin 2) Unit 2 .done h (qubitJoint qubitY)) F = x}
      ((1 - 1 / Real.sqrt 2)/2) := by
  have hh := depth_zero_isLeast qubitX_density qubitY_density
  simpa only [qubit_distance, invSqrtTwo] using hh

/-! Floors for every allowed terminal readout and the attained optimum. -/
open FiniteAdaptiveMixtureSurvival

theorem tree_readout_lower (T U : Tree S E o n)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    (1-outputDistance S E o T U X Y)/2 ≤
      readoutError (fun h => run S E o T h X) (fun h => run S E o U h Y) F := by
  simpa only [branchDistance, outputDistance, traceDist, div_eq_mul_inv,
    one_mul, mul_comm, Finset.mul_sum] using
    readoutError_lower (run_family T hX) (run_family U hY) hF

theorem pairedErrors_readout_floor {T U : Tree S E o n} {es : List ℝ}
    (hp : PairedErrors S E o T U es) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    (1-min 1 (traceDist X Y+es.sum))/2 ≤
      readoutError (fun h => run S E o T h X) (fun h => run S E o U h Y) F := by
  have hl := tree_readout_lower T U hX hY F hF
  have hu := pairedErrors_capped S E o hp hX hY
  linarith

theorem pairedErrors_optimum_floor {T U : Tree S E o n} {es : List ℝ}
    (hp : PairedErrors S E o T U es) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    (1-min 1 (traceDist X Y+es.sum))/2 ≤ (1-outputDistance S E o T U X Y)/2 := by
  linarith [pairedErrors_capped S E o hp hX hY]

theorem pairedMixture_readout_floor {T U : Tree S E o n} {rs : List NoiseRates}
    (hp : PairedMixture S E o T U rs) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    survival rs*(1-traceDist X Y)/2 ≤
      readoutError (fun h => run S E o T h X) (fun h => run S E o U h Y) F := by
  have hl := tree_readout_lower T U hX hY F hF
  have hu := pairedMixture_changed_input S E o hp hX hY
  nlinarith

theorem pairedMixture_optimum_floor {T U : Tree S E o n} {rs : List NoiseRates}
    (hp : PairedMixture S E o T U rs) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    survival rs*(1-traceDist X Y)/2 ≤ (1-outputDistance S E o T U X Y)/2 := by
  nlinarith [pairedMixture_changed_input S E o hp hX hY]

theorem pairedMixture_same_input_floor {T U : Tree S E o n} {rs : List NoiseRates}
    (hp : PairedMixture S E o T U rs) {X : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    survival rs/2 ≤
      readoutError (fun h => run S E o T h X) (fun h => run S E o U h X) F := by
  simpa only [traceDist_self, sub_zero, mul_one] using
    pairedMixture_readout_floor hp hX hX F hF

theorem pairedMixture_same_input_optimum {T U : Tree S E o n} {rs : List NoiseRates}
    (hp : PairedMixture S E o T U rs) {X : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) :
    survival rs/2 ≤ (1-outputDistance S E o T U X X)/2 := by
  simpa only [traceDist_self, sub_zero, mul_one] using
    pairedMixture_optimum_floor hp hX hX

/-! Actual independent-memory pair, with choose-A meaning the mixed hypothesis. -/
theorem memory_error_isLeast (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    IsLeast {x : ℝ | ∃ F : History 2 1 → Matrix Joint Joint ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput)
        (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) F = x}
      ((1-p)*(1-q)/2) := by
  have hh := tree_error_isLeast (memoryMixedTree p q hp hp1 hq hq1)
    memoryIdentityTree memoryInput_density memoryInput_density
  rw [memory_output_exact] at hh
  convert hh using 1
  ring

theorem memory_history_error (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (a : History 2 1 → ℝ) :
    historyError (fun h => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) a =
      (1+q*(a (0,())-a (1,())))/2 := by
  unfold historyError
  change ((∑ h : Qubit × Unit, a h*(identityPrepare.branch Qubit Qubit 2 h.1 memoryInput).trace.re) +
    (∑ h : Qubit × Unit, (1-a h)*((memoryMixed p q hp hp1 hq hq1).branch Qubit Qubit 2 h.1 memoryInput).trace.re))/2 = _
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_two,
    FiniteAdaptiveMixtureSurvival.memory_weights, memory_identity_branch]
  norm_num only [ite_true, show (1 : Qubit) ≠ 0 by decide, ite_false,
    Matrix.trace_zero, Complex.zero_re, zero_mul, mul_zero, zero_add, add_zero,
    (basisJoint_density 0 0).2, Complex.one_re, mul_one,
    show (default : Unit) = () by rfl]
  change (a (0,()) + ((1-a (0,()))*(1-q) + (1-a (1,()))*q))/2 = _
  ring

theorem memory_history_lower (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (a : History 2 1 → ℝ) (ha : ∀ h, a h ∈ Set.Icc (0 : ℝ) 1) :
    (1-q)/2 ≤
    historyError (fun h => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) a := by
  rw [memory_history_error]
  nlinarith [(ha (0,())).1, (ha (1,())).2]

def memoryClassifier (h : History 2 1) : ℝ := if h.1=0 then 0 else 1

theorem memoryClassifier_admissible (h : History 2 1) :
    memoryClassifier h ∈ Set.Icc (0 : ℝ) 1 := by
  unfold memoryClassifier
  split_ifs <;> norm_num

theorem memoryClassifier_attains (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    historyError (fun h => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryClassifier = (1-q)/2 := by
  rw [memory_history_error]
  norm_num [memoryClassifier]
  ring

theorem memory_history_isLeast (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    IsLeast {x : ℝ | ∃ a : History 2 1 → ℝ,
      (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) ∧
      historyError (fun h => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput)
        (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) a = x} ((1-q)/2) := by
  refine ⟨⟨memoryClassifier, memoryClassifier_admissible, memoryClassifier_attains p q hp hp1 hq hq1⟩, ?_⟩
  rintro x ⟨a,ha,rfl⟩
  exact memory_history_lower p q hp hp1 hq hq1 a ha

theorem memory_scalar_history_isLeast (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    IsLeast {x : ℝ | ∃ a : History 2 1 → ℝ,
      (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) ∧
      readoutError (fun h => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput)
        (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput)
        (fun h => (a h : ℂ) • 1) = x} ((1-q)/2) := by
  simpa only [historyError_scalar_effect] using memory_history_isLeast p q hp hp1 hq hq1

theorem memory_optimum_gap (p q : ℝ) :
    (1-q)/2 - (1-p)*(1-q)/2 = p*(1-q)/2 := by ring

theorem memory_optimum_strict_gap (p q : ℝ) (hp : 0<p) (hq : q<1) :
    (1-p)*(1-q)/2 < (1-q)/2 := by
  have hh := mul_pos hp (sub_pos.mpr hq)
  nlinarith

theorem memory_quarter_error :
    (1-(1/4 : ℝ))*(1-1/4)/2 = 9/32 ∧ (1-(1/4 : ℝ))/2 = 3/8 ∧ (9/32 : ℝ)<3/8 := by
  norm_num

noncomputable def memoryBaseProjector : Matrix Joint Joint ℂ := basisState 0 ⊗ₖ basisState 0

theorem memoryBaseProjector_hermitian : memoryBaseProjector.IsHermitian :=
  (basisJoint_density 0 0).1.isHermitian

theorem memoryBaseProjector_idem : memoryBaseProjector * memoryBaseProjector = memoryBaseProjector := by
  rw [memoryBaseProjector, ← Matrix.mul_kronecker_mul, basis_idempotent]

noncomputable def memoryEffect (h : History 2 1) : Matrix Joint Joint ℂ :=
  if h.1=0 then 1-memoryBaseProjector else 1

theorem memoryEffect_hermitian (h : History 2 1) : (memoryEffect h).IsHermitian := by
  unfold memoryEffect
  split_ifs
  · exact Matrix.isHermitian_one.sub memoryBaseProjector_hermitian
  · exact Matrix.isHermitian_one

theorem memoryEffect_idem (h : History 2 1) : memoryEffect h * memoryEffect h = memoryEffect h := by
  unfold memoryEffect
  split_ifs
  · rw [sub_mul, one_mul, mul_sub, mul_one, memoryBaseProjector_idem, sub_self, sub_zero]
  · exact Matrix.one_mul 1

noncomputable def memoryReadout (h : History 2 1) : FiniteInstrument Joint 2 :=
  projectiveReadout (memoryEffect h) (memoryEffect_hermitian h) (memoryEffect_idem h)

theorem memoryReadout_weight_zero (h : History 2 1) (Z : Matrix Joint Joint ℂ) :
    (memoryReadout h).weight 0 Z = (memoryEffect h * Z).trace.re :=
  projectiveReadout_weight_zero _ _ _ _

theorem memoryReadout_weight_one (h : History 2 1) (Z : Matrix Joint Joint ℂ) :
    (memoryReadout h).weight 1 Z = ((1-memoryEffect h) * Z).trace.re :=
  projectiveReadout_weight_one _ _ _ _

theorem memory_mixed_run (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (h : History 2 1) :
    run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput =
      if h.1=0 then ((1-p)*(1-q)) • (basisState 0 ⊗ₖ basisState 0) +
        (p*(1-q)) • (basisState 0 ⊗ₖ basisState 1)
      else ((1-p)*q) • (basisState 1 ⊗ₖ basisState 0) +
        (p*q) • (basisState 1 ⊗ₖ basisState 1) := by
  rcases h with ⟨a,u⟩
  cases u
  change (memoryMixed p q hp hp1 hq hq1).branch Qubit Qubit 2 a memoryInput = _
  have ha : a=0 ∨ a=1 := by fin_cases a <;> norm_num
  rcases ha with rfl | rfl
  · simpa only [ite_true] using memoryMixed_branch_zero p q hp hp1 hq hq1
  · simpa only [show (1 : Qubit) ≠ 0 by decide, ite_false] using memoryMixed_branch_one p q hp hp1 hq hq1

theorem memory_identity_run_history (h : History 2 1) :
    run Qubit Qubit 2 memoryIdentityTree h memoryInput =
      if h.1=0 then basisState 0 ⊗ₖ basisState 0 else 0 := by
  rcases h with ⟨a,u⟩
  cases u
  exact memory_identity_branch a

theorem memory_readout_table (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (h : History 2 1) :
    readoutTable memoryReadout (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h 0 =
      (if h.1=0 then p*(1-q) else q) ∧
    readoutTable memoryReadout (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h 1 =
      (if h.1=0 then (1-p)*(1-q) else 0) ∧
    readoutTable memoryReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0 = 0 ∧
    readoutTable memoryReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 1 =
      (if h.1=0 then 1 else 0) := by
  simp only [readoutTable, memory_mixed_run, memory_identity_run_history,
    memoryReadout_weight_zero, memoryReadout_weight_one]
  rcases h with ⟨a,u⟩
  fin_cases a <;>
    norm_num [memoryEffect, memoryBaseProjector, Matrix.mul_apply, Matrix.trace,
      Matrix.kronecker_apply, basisState, Matrix.one_apply, Complex.real_smul,
      Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals ring

theorem memoryReadout_attains (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    ((∑ h, readoutTable memoryReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable memoryReadout (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h 1))/2 =
      (1-p)*(1-q)/2 := by
  simp_rw [(memory_readout_table p q hp hp1 hq hq1 _).2.2.1,
    (memory_readout_table p q hp hp1 hq hq1 _).2.1]
  rw [Finset.sum_const_zero]
  change (0 + ∑ h : Qubit × Unit, (if h.1=0 then (1-p)*(1-q) else 0))/2 = _
  simp [Fintype.sum_prod_type]

theorem memoryReadout_optimal_effect (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    readoutError (fun h => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryEffect =
      (1-p)*(1-q)/2 := by
  have hh := memoryReadout_attains p q hp hp1 hq hq1
  simpa only [readoutTable, memoryReadout_weight_zero, memoryReadout_weight_one, readoutError] using hh

theorem memoryReadout_normalized (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    (∀ h a, 0 ≤ readoutTable memoryReadout
      (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h a) ∧
    (∑ h, ∑ a, readoutTable memoryReadout
      (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h a) = 1 ∧
    (∀ h a, 0 ≤ readoutTable memoryReadout
      (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h a) ∧
    (∑ h, ∑ a, readoutTable memoryReadout
      (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h a) = 1 := by
  exact ⟨(tree_readout_probabilities (memoryMixedTree p q hp hp1 hq hq1) memoryInput_density memoryReadout).1,
    (tree_readout_probabilities (memoryMixedTree p q hp hp1 hq hq1) memoryInput_density memoryReadout).2,
    tree_readout_probabilities memoryIdentityTree memoryInput_density memoryReadout⟩

theorem memory_quarter_probabilities (h : History 2 1) :
    readoutTable memoryReadout (fun k => run Qubit Qubit 2 quarterTree k memoryInput) h 0 =
      (if h.1=0 then 3/16 else 1/4) ∧
    readoutTable memoryReadout (fun k => run Qubit Qubit 2 quarterTree k memoryInput) h 1 =
      (if h.1=0 then 9/16 else 0) ∧
    readoutTable memoryReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0 = 0 ∧
    readoutTable memoryReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 1 =
      (if h.1=0 then 1 else 0) := by
  have hh := memory_readout_table (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
  norm_num [quarterTree, quarterStep, memoryMixedTree] at hh ⊢
  exact hh

theorem memory_quarter_actual_error :
    ((∑ h, readoutTable memoryReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable memoryReadout (fun k => run Qubit Qubit 2 quarterTree k memoryInput) h 1))/2 = 9/32 := by
  have hh := memoryReadout_attains (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [quarterTree, quarterStep, memoryMixedTree] at hh ⊢
  exact hh

/-- Total depth is m+1: root readout followed by m noisy feedback layers. -/
theorem feedback_error_isLeast (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    IsLeast {x : ℝ | ∃ F : History 2 (m+1) → Matrix Joint Joint ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run Qubit Qubit 2 (idealFeedback m) h correlatedInput)
        (fun h => run Qubit Qubit 2 (noisyFeedback p hp hp1 m) h correlatedInput) F = x}
      ((1-p)^m/2) := by
  have hh := tree_error_isLeast (idealFeedback m) (noisyFeedback p hp hp1 m)
    correlatedInput_density correlatedInput_density
  rw [(noisyFeedback_exact p hp hp1 m).1] at hh
  simpa only [sub_sub_cancel] using hh

noncomputable def feedbackReadout (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    History 2 (m+1) → FiniteInstrument Joint 2 :=
  optimalReadout (run_family (idealFeedback m) correlatedInput_density)
    (run_family (noisyFeedback p hp hp1 m) correlatedInput_density)

theorem feedbackReadout_attains (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    ((∑ h, readoutTable (feedbackReadout p hp hp1 m)
      (fun k => run Qubit Qubit 2 (noisyFeedback p hp hp1 m) k correlatedInput) h 0) +
     (∑ h, readoutTable (feedbackReadout p hp hp1 m)
      (fun k => run Qubit Qubit 2 (idealFeedback m) k correlatedInput) h 1))/2 = (1-p)^m/2 := by
  have hh := tree_optimalReadout_error (idealFeedback m) (noisyFeedback p hp hp1 m)
    correlatedInput_density correlatedInput_density
  rw [(noisyFeedback_exact p hp hp1 m).1] at hh
  simpa only [feedbackReadout, sub_sub_cancel] using hh

theorem feedback_readout_floor (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (F : History 2 (m+1) → Matrix Joint Joint ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    (1-p)^m/2 ≤
      readoutError (fun h => run Qubit Qubit 2 (idealFeedback m) h correlatedInput)
        (fun h => run Qubit Qubit 2 (noisyFeedback p hp hp1 m) h correlatedInput) F := by
  exact (feedback_error_isLeast p hp hp1 m).2 ⟨F,hF,rfl⟩

theorem feedbackReadout_probabilities (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    (∀ h a, 0 ≤ readoutTable (feedbackReadout p hp hp1 m)
      (fun k => run Qubit Qubit 2 (idealFeedback m) k correlatedInput) h a) ∧
    (∑ h, ∑ a, readoutTable (feedbackReadout p hp hp1 m)
      (fun k => run Qubit Qubit 2 (idealFeedback m) k correlatedInput) h a) = 1 ∧
    (∀ h a, 0 ≤ readoutTable (feedbackReadout p hp hp1 m)
      (fun k => run Qubit Qubit 2 (noisyFeedback p hp hp1 m) k correlatedInput) h a) ∧
    (∑ h, ∑ a, readoutTable (feedbackReadout p hp hp1 m)
      (fun k => run Qubit Qubit 2 (noisyFeedback p hp hp1 m) k correlatedInput) h a) = 1 := by
  exact ⟨(tree_readout_probabilities (idealFeedback m) correlatedInput_density (feedbackReadout p hp hp1 m)).1,
    (tree_readout_probabilities (idealFeedback m) correlatedInput_density (feedbackReadout p hp hp1 m)).2,
    tree_readout_probabilities (noisyFeedback p hp hp1 m) correlatedInput_density (feedbackReadout p hp hp1 m)⟩

theorem feedback_zero_layers (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    ((∑ h, readoutTable (feedbackReadout p hp hp1 0)
      (fun k => run Qubit Qubit 2 (noisyFeedback p hp hp1 0) k correlatedInput) h 0) +
     (∑ h, readoutTable (feedbackReadout p hp hp1 0)
      (fun k => run Qubit Qubit 2 (idealFeedback 0) k correlatedInput) h 1))/2 = 1/2 := by
  rw [feedbackReadout_attains, pow_zero]

theorem feedback_zero_noise_error (m : ℕ) :
    ((∑ h, readoutTable (feedbackReadout 0 le_rfl (by norm_num) m)
      (fun k => run Qubit Qubit 2 (noisyFeedback 0 le_rfl (by norm_num) m) k correlatedInput) h 0) +
     (∑ h, readoutTable (feedbackReadout 0 le_rfl (by norm_num) m)
      (fun k => run Qubit Qubit 2 (idealFeedback m) k correlatedInput) h 1))/2 = 1/2 := by
  rw [feedbackReadout_attains]
  simp

theorem feedback_full_noise_error (m : ℕ) (hm : 0<m) :
    ((∑ h, readoutTable (feedbackReadout 1 (by norm_num) le_rfl m)
      (fun k => run Qubit Qubit 2 (noisyFeedback 1 (by norm_num) le_rfl m) k correlatedInput) h 0) +
     (∑ h, readoutTable (feedbackReadout 1 (by norm_num) le_rfl m)
      (fun k => run Qubit Qubit 2 (idealFeedback m) k correlatedInput) h 1))/2 = 0 := by
  rw [feedbackReadout_attains]
  simp [Nat.ne_of_gt hm]

/-- At rate one, absence of any feedback layer still leaves the same experiment. -/
theorem feedback_full_noise_zero_layers :
    ((∑ h, readoutTable (feedbackReadout 1 (by norm_num) le_rfl 0)
      (fun k => run Qubit Qubit 2 (noisyFeedback 1 (by norm_num) le_rfl 0) k correlatedInput) h 0) +
     (∑ h, readoutTable (feedbackReadout 1 (by norm_num) le_rfl 0)
      (fun k => run Qubit Qubit 2 (idealFeedback 0) k correlatedInput) h 1))/2 = 1/2 :=
  feedback_zero_layers 1 (by norm_num) le_rfl

theorem pairedMixture_survival_zero_guard {T U : Tree S E o n} {rs : List NoiseRates}
    (hp : PairedMixture S E o T U rs) (hs : survival rs=0)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    0 ≤ readoutError (fun h => run S E o T h X) (fun h => run S E o U h Y) F := by
  simpa only [hs, zero_mul, zero_div] using pairedMixture_readout_floor hp hX hY F hF

theorem pairedMixture_survival_one_guard {T U : Tree S E o n} {rs : List NoiseRates}
    (hp : PairedMixture S E o T U rs) (hs : survival rs=1)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (F : History o n → Matrix (S × E) (S × E) ℂ) (hF : ∀ h, IsBinaryPOVM (F h)) :
    (1-traceDist X Y)/2 ≤ readoutError (fun h => run S E o T h X) (fun h => run S E o U h Y) F := by
  simpa only [hs, one_mul] using pairedMixture_readout_floor hp hX hY F hF

theorem pairedErrors_empty_depth_guard {X : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (F : History o 0 → Matrix (S × E) (S × E) ℂ)
    (hF : ∀ h, IsBinaryPOVM (F h)) :
    1/2 ≤ readoutError (fun h => run S E o .done h X) (fun h => run S E o .done h X) F := by
  have hh := pairedErrors_readout_floor
    (PairedErrors.done : PairedErrors S E o (.done) (.done) []) hX hX F hF
  simpa only [traceDist_self, List.sum_nil, zero_add, min_eq_right (by norm_num : (0 : ℝ) ≤ 1), sub_zero] using hh

theorem memory_endpoint_actual_errors (p q : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    readoutError (fun h => run Qubit Qubit 2 (memoryMixedTree 0 q le_rfl (by norm_num) hq hq1) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryEffect = (1-q)/2 ∧
    readoutError (fun h => run Qubit Qubit 2 (memoryMixedTree p 0 hp hp1 le_rfl (by norm_num)) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryEffect = (1-p)/2 ∧
    readoutError (fun h => run Qubit Qubit 2 (memoryMixedTree 1 q (by norm_num) le_rfl hq hq1) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryEffect = 0 ∧
    readoutError (fun h => run Qubit Qubit 2 (memoryMixedTree p 1 hp hp1 (by norm_num) le_rfl) h memoryInput)
      (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) memoryEffect = 0 := by
  simp only [memoryReadout_optimal_effect, sub_zero, one_mul, mul_one, sub_self, zero_mul, mul_zero, zero_div]
  trivial

theorem memoryClassifier_effect_idem (h : History 2 1) :
    ((memoryClassifier h : ℂ) • (1 : Matrix Joint Joint ℂ)) *
      ((memoryClassifier h : ℂ) • 1) = (memoryClassifier h : ℂ) • 1 := by
  unfold memoryClassifier
  split_ifs <;> simp

theorem memoryClassifier_effect_hermitian (h : History 2 1) :
    ((memoryClassifier h : ℂ) • (1 : Matrix Joint Joint ℂ)).IsHermitian := by
  unfold memoryClassifier
  split_ifs <;> simp [Matrix.IsHermitian]

noncomputable def historyOnlyReadout (h : History 2 1) : FiniteInstrument Joint 2 :=
  projectiveReadout ((memoryClassifier h : ℂ) • 1)
    (memoryClassifier_effect_hermitian h) (memoryClassifier_effect_idem h)

theorem historyOnlyReadout_attains (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    ((∑ h, readoutTable historyOnlyReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable historyOnlyReadout
        (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h 1))/2 = (1-q)/2 := by
  have he : ((∑ h, readoutTable historyOnlyReadout
      (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable historyOnlyReadout
      (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h 1))/2 =
      readoutError (fun h => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) h memoryInput)
        (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput)
        (fun h => (memoryClassifier h : ℂ) • 1) := by
    simp only [readoutTable, historyOnlyReadout, projectiveReadout_weight_zero,
      projectiveReadout_weight_one, readoutError]
  rw [he, historyError_scalar_effect]
  exact memoryClassifier_attains p q hp hp1 hq hq1

theorem historyOnlyReadout_probabilities (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    (∀ h a, 0 ≤ readoutTable historyOnlyReadout
      (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h a) ∧
    (∑ h, ∑ a, readoutTable historyOnlyReadout
      (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h a) = 1 ∧
    (∀ h a, 0 ≤ readoutTable historyOnlyReadout
      (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h a) ∧
    (∑ h, ∑ a, readoutTable historyOnlyReadout
      (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h a) = 1 := by
  exact ⟨(tree_readout_probabilities (memoryMixedTree p q hp hp1 hq hq1) memoryInput_density historyOnlyReadout).1,
    (tree_readout_probabilities (memoryMixedTree p q hp hp1 hq hq1) memoryInput_density historyOnlyReadout).2,
    tree_readout_probabilities memoryIdentityTree memoryInput_density historyOnlyReadout⟩

theorem quarter_history_actual_error :
    ((∑ h, readoutTable historyOnlyReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable historyOnlyReadout (fun k => run Qubit Qubit 2 quarterTree k memoryInput) h 1))/2 = 3/8 := by
  have hh := historyOnlyReadout_attains (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [quarterTree, quarterStep, memoryMixedTree] at hh ⊢
  exact hh

theorem quarter_joint_isLeast :
    IsLeast {x : ℝ | ∃ F : History 2 1 → Matrix Joint Joint ℂ,
      (∀ h, IsBinaryPOVM (F h)) ∧
      readoutError (fun h => run Qubit Qubit 2 quarterTree h memoryInput)
        (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) F = x} (9/32) := by
  have hh := memory_error_isLeast (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [quarterTree, quarterStep, memoryMixedTree] at hh ⊢
  exact hh

theorem quarter_history_isLeast :
    IsLeast {x : ℝ | ∃ a : History 2 1 → ℝ,
      (∀ h, a h ∈ Set.Icc (0 : ℝ) 1) ∧
      historyError (fun h => run Qubit Qubit 2 quarterTree h memoryInput)
        (fun h => run Qubit Qubit 2 memoryIdentityTree h memoryInput) a = x} (3/8) := by
  have hh := memory_history_isLeast (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [quarterTree, quarterStep, memoryMixedTree] at hh ⊢
  exact hh

theorem actual_memory_readout_gap (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1) :
    ((∑ h, readoutTable historyOnlyReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable historyOnlyReadout (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h 1))/2 -
    ((∑ h, readoutTable memoryReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable memoryReadout (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp hp1 hq hq1) k memoryInput) h 1))/2 =
      p*(1-q)/2 := by
  rw [historyOnlyReadout_attains, memoryReadout_attains, memory_optimum_gap]

theorem actual_memory_readout_strict_gap (p q : ℝ) (hp : 0<p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q<1) :
    ((∑ h, readoutTable memoryReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable memoryReadout (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp.le hp1 hq hq1.le) k memoryInput) h 1))/2 <
    ((∑ h, readoutTable historyOnlyReadout (fun k => run Qubit Qubit 2 memoryIdentityTree k memoryInput) h 0) +
      (∑ h, readoutTable historyOnlyReadout (fun k => run Qubit Qubit 2 (memoryMixedTree p q hp.le hp1 hq hq1.le) k memoryInput) h 1))/2 := by
  rw [memoryReadout_attains, historyOnlyReadout_attains]
  exact memory_optimum_strict_gap p q hp hq1

end FiniteAdaptiveReadoutDiscrimination
end SKEFTHawking.QuantumNetwork
