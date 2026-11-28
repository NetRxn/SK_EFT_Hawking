import SKEFTHawking.FiniteGibbsResetSchedule
import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper
import SKEFTHawking.QuantumNetwork.LogNegativity
import SKEFTHawking.QuantumNetwork.DiamondBudget
import SKEFTHawking.QuantumNetwork.NamedChannels

/-! Exact stabilized differences for channels with a common retained action. -/

noncomputable section

set_option autoImplicit false

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped BigOperators Kronecker

variable {m n : ℕ}
variable {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}

/-- If the difference of two system maps is a trace followed by a fixed
matrix, their stabilized difference retains precisely the spectator marginal. -/
theorem tensorKraus_sub_of_trace_replacement (T : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ X, krausMap K₁ X - krausMap K₂ X = X.trace • T)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    krausMap (tensorKraus K₁) ρ - krausMap (tensorKraus K₂) ρ
      = T ⊗ₖ ptrace1 ρ := by
  have hChoi (a b y z : Fin n) : choiMatrix (krausMap K₁) (a,y) (b,z)
      - choiMatrix (krausMap K₂) (a,y) (b,z) = if a = b then T y z else 0 := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M y z)
      (h (Matrix.single a b 1))
    by_cases hab : a = b
    · subst b
      simpa [choiMatrix, Matrix.trace_single_eq_same] using he
    · simpa [choiMatrix, Matrix.trace_single_eq_of_ne a b (1 : ℂ) hab, hab] using he
  ext ⟨y,α⟩ ⟨z,β⟩
  rw [Matrix.sub_apply, krausMap_tensorKraus_apply, krausMap_tensorKraus_apply]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul, hChoi, ite_mul, zero_mul]
  simp [ptrace1, Matrix.kroneckerMap_apply, Finset.mul_sum]

/-- Every density input gives the same stabilized distance for a trace
replacement difference, including correlated inputs. -/
theorem tensorKraus_traceDist_of_trace_replacement (T : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ X, krausMap K₁ X - krausMap K₂ X = X.trace • T)
    {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ}
    (hρ : IsDensityOperator ρ) :
    traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ)
      = traceNorm T / 2 := by
  have hMarginal : IsDensityOperator (ptrace1 ρ) :=
    ⟨ptrace1_posSemidef hρ.1, (trace_ptrace1 ρ).trans hρ.2⟩
  rw [traceDist, tensorKraus_sub_of_trace_replacement T h,
    traceNorm_kronecker, traceNorm_density_eq_one hMarginal, mul_one]
  ring

/-- The operational diamond distance for a trace replacement difference
is half the trace norm of the fixed system matrix. -/
theorem diamondDist_of_trace_replacement [NeZero n]
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    (T : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ X, krausMap K₁ X - krausMap K₂ X = X.trace • T) :
    diamondDist K₁ K₂ = traceNorm T / 2 := by
  apply le_antisymm
  · unfold diamondDist
    apply Real.sSup_le _ (div_nonneg (traceNorm_nonneg T) (by norm_num))
    rintro d ⟨ρ, hρ, rfl⟩
    rw [tensorKraus_traceDist_of_trace_replacement T h hρ]
  · have hh := le_diamondDist hK₁ hK₂ (ρ := maxEntangled n) isDensityOperator_maxEntangled
    rwa [tensorKraus_traceDist_of_trace_replacement T h isDensityOperator_maxEntangled] at hh

open FinitePositiveKernel.GibbsReset in
/-- For channels realizing the two actual fixed-total-dose schedules, the
distance is exactly the norm of the accumulated thermal target difference. -/
theorem diamondDist_of_equalDose_resetSchedules [NeZero n]
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    (steps other : List (ResetSlice (Fin n)))
    (hDose : resetScheduleDose steps = resetScheduleDose other)
    (h₁ : ∀ X, krausMap K₁ X = evolveResetSchedule steps X)
    (h₂ : ∀ X, krausMap K₂ X = evolveResetSchedule other X) :
    diamondDist K₁ K₂ = traceNorm (resetScheduleTarget steps - resetScheduleTarget other) / 2 := by
  apply diamondDist_of_trace_replacement hK₁ hK₂
  intro X
  rw [h₁, h₂, evolveResetSchedule_affine, evolveResetSchedule_affine]
  have hAttenuation : resetScheduleAttenuation steps = resetScheduleAttenuation other :=
    congrArg (fun d : ℝ => (Real.exp (-d) : ℂ)) hDose
  rw [hAttenuation]
  module

open FinitePositiveKernel.GibbsReset in
/-- Every finite reset schedule has a normalized Kraus representation. -/
theorem exists_resetSchedule_kraus (steps : List (ResetSlice (Fin n))) :
    ∃ k : ℕ, ∃ K : Fin k → Matrix (Fin n) (Fin n) ℂ,
      IsKrausChannel K ∧ ∀ X, krausMap K X = evolveResetSchedule steps X := by
  induction steps with
  | nil =>
      exact ⟨1, idKrausPad 0 n, isKrausChannel_idKrausPad 0 n,
        fun X => krausMap_idKrausPad 0 n X⟩
  | cons s rest ih =>
      obtain ⟨k, K, hK, hAction⟩ := ih
      refine ⟨_, composeKraus K (timeKraus s.weights (Real.exp (-s.rate*s.duration))),
        isKrausChannel_composeKraus hK s.normalized_kraus, ?_⟩
      intro X
      rw [krausMap_composeKraus, ← s.evolve_eq_kraus, hAction]
      rfl

open FinitePositiveKernel.GibbsReset in
/-- Equal-dose schedules admit normalized representations on one common
Kraus index type and attain the stated exact diamond distance. -/
theorem equalDose_resetSchedules_exact_diamond [NeZero n]
    (steps other : List (ResetSlice (Fin n)))
    (hDose : resetScheduleDose steps = resetScheduleDose other) :
    ∃ k : ℕ, ∃ L R : Fin k → Matrix (Fin n) (Fin n) ℂ,
      IsKrausChannel L ∧ IsKrausChannel R ∧
      (∀ X, krausMap L X = evolveResetSchedule steps X) ∧
      (∀ X, krausMap R X = evolveResetSchedule other X) ∧
      diamondDist L R = traceNorm (resetScheduleTarget steps - resetScheduleTarget other) / 2 := by
  obtain ⟨a, L, hL, hLeft⟩ := exists_resetSchedule_kraus steps
  obtain ⟨b, R, hR, hRight⟩ := exists_resetSchedule_kraus other
  let L' : Fin (a + b) → Matrix (Fin n) (Fin n) ℂ := Fin.addCases L (fun _ => 0)
  let R' : Fin (a + b) → Matrix (Fin n) (Fin n) ℂ := Fin.addCases (fun _ => 0) R
  have hL' : IsKrausChannel L' := by
    simpa [IsKrausChannel, Fin.sum_univ_add, L'] using hL
  have hR' : IsKrausChannel R' := by
    simpa [IsKrausChannel, Fin.sum_univ_add, R'] using hR
  have hLeft' (X : Matrix (Fin n) (Fin n) ℂ) :
      krausMap L' X = evolveResetSchedule steps X := by
    simpa [krausMap, Fin.sum_univ_add, L'] using hLeft X
  have hRight' (X : Matrix (Fin n) (Fin n) ℂ) :
      krausMap R' X = evolveResetSchedule other X := by
    simpa [krausMap, Fin.sum_univ_add, R'] using hRight X
  exact ⟨a + b, L', R', hL', hR', hLeft', hRight',
    diamondDist_of_equalDose_resetSchedules hL' hR' steps other hDose hLeft' hRight'⟩

end SKEFTHawking.QuantumNetwork
