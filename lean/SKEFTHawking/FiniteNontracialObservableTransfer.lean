import SKEFTHawking.FiniteNontracialHistoryConsistency

noncomputable section

namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix NontracialPauliReflection NontracialReflectionDynamics FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

/-- Two-rate dynamics on the actual all-depth history quotient. -/
def historyTransfer (p : Gap) (rs : List Gap) (γ η t : ℝ) :
    HistorySpace p rs →L[ℂ] HistorySpace p rs :=
  historyScalarProjection p rs + (Real.exp (-γ*t) : ℂ) •
    (historyDiagonalProjection p rs-historyScalarProjection p rs) +
    (Real.exp (-(γ+η)*t) : ℂ) • (1-historyDiagonalProjection p rs)

/-- Positive dissipation generator; the observable evolution differentiates to its negative. -/
def historyGenerator (p : Gap) (rs : List Gap) (γ η : ℝ) :
    HistorySpace p rs →L[ℂ] HistorySpace p rs :=
  (γ : ℂ) • (1-historyScalarProjection p rs) +
    (η : ℂ) • (1-historyDiagonalProjection p rs)

section
variable (p : Gap) (rs : List Gap)
local notation "C" => historyScalarProjection p rs
local notation "B" => historyDiagonalProjection p rs
local notation "E" => historyReferenceEquiv p rs
local notation "TR" => transfer p.value 0 p.nonnegative p.bounded le_rfl zero_le_one
local notation "HR" => generator p.value 0 p.nonnegative p.bounded le_rfl zero_le_one

theorem historyTransfer_apply (γ η t : ℝ) (z : HistorySpace p rs) :
    historyTransfer p rs γ η t z = C z + (Real.exp (-γ*t) : ℂ) • (B z-C z) +
      (Real.exp (-(γ+η)*t) : ℂ) • (z-B z) := by
  simp [historyTransfer]

theorem historyGenerator_apply (γ η : ℝ) (z : HistorySpace p rs) :
    historyGenerator p rs γ η z = (γ : ℂ) • (z-C z)+(η : ℂ) • (z-B z) := by
  simp [historyGenerator]

theorem historyTransfer_coordinates (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (z : HistorySpace p rs) :
    historyCoordinates p rs (historyTransfer p rs γ η t z) =
      observable γ η t (historyCoordinates p rs z) := by
  rw [historyTransfer_apply, map_add, map_add, map_smul, map_smul, map_sub, map_sub,
    historyScalarProjection_coordinates, historyDiagonalProjection_coordinates,
    observable_formula γ η t hγ hη ht]
  rfl

theorem historyGenerator_coordinates (γ η : ℝ) (z : HistorySpace p rs) :
    historyCoordinates p rs (-historyGenerator p rs γ η z) =
      observableGenerator γ η (historyCoordinates p rs z) := by
  simp only [historyGenerator_apply, map_neg, map_add, map_smul, map_sub,
    historyScalarProjection_coordinates, historyDiagonalProjection_coordinates, observableGenerator]
  module

/-- The proved weighted reference isometry intertwines the genuinely defined transfer. -/
theorem historyReferenceEquiv_transfer (γ η t : ℝ) (z : HistorySpace p rs) :
    E (historyTransfer p rs γ η t z) = TR γ η t (E z) := by
  simp only [historyTransfer_apply, map_add, map_smul, map_sub,
    historyReferenceEquiv_scalar, historyReferenceEquiv_diagonal, transfer_apply]

theorem historyReferenceEquiv_generator (γ η : ℝ) (z : HistorySpace p rs) :
    E (historyGenerator p rs γ η z) = HR γ η (E z) := by
  simp only [historyGenerator_apply, map_add, map_smul, map_sub,
    historyReferenceEquiv_scalar, historyReferenceEquiv_diagonal,
    generator, _root_.add_apply, _root_.smul_apply, _root_.sub_apply, one_apply_eq_self]

/-- Full complex pairing of actual chronological histories with the transfer operator. -/
theorem history_actual_pairing_transfer (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (F G : Labels rs → ℂ) :
    pairing (historyInsertedKernel p rs γ η t hγ hη ht) F G =
      ⟪mk _ (history_posSemidef p rs) F,
        historyTransfer p rs γ η t (mk _ (history_posSemidef p rs) G)⟫_ℂ := by
  rw [history_coordinates_inner, historyTransfer_coordinates p rs γ η t hγ hη ht,
    historyCoordinates_mk, historyCoordinates_mk, history_inserted_pairing]

/-- A chronological singleton coefficient, rather than a formal matrix coordinate. -/
def historySingletonVector (u : Labels rs) : HistorySpace p rs :=
  by
    classical
    exact mk _ (history_posSemidef p rs) (Pi.single u 1)

theorem historySingletonVector_coordinates (u : Labels rs) :
    historyCoordinates p rs (historySingletonVector p rs u) = historyMidpoint p rs u := by
  classical
  rw [historySingletonVector, historyCoordinates_mk]
  simp [historySynthesis, Pi.single_apply]

theorem history_actual_entry_transfer (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Labels rs) :
    historyInsertedKernel p rs γ η t hγ hη ht u v =
      ⟪historySingletonVector p rs u,
        historyTransfer p rs γ η t (historySingletonVector p rs v)⟫_ℂ := by
  rw [history_coordinates_inner, historyTransfer_coordinates p rs γ η t hγ hη ht,
    historySingletonVector_coordinates, historySingletonVector_coordinates,
    history_inserted_kernel_form]

theorem historyTransfer_convex (γ η t : ℝ) :
    historyTransfer p rs γ η t =
      ((1-Real.exp (-γ*t) : ℝ) : ℂ) • C +
      ((Real.exp (-γ*t)-Real.exp (-(γ+η)*t) : ℝ) : ℂ) • B +
      (Real.exp (-(γ+η)*t) : ℂ) • (1 : HistorySpace p rs →L[ℂ] HistorySpace p rs) := by
  simp only [historyTransfer, Complex.ofReal_sub, Complex.ofReal_one]
  module

theorem historyTransfer_positive (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (historyTransfer p rs γ η t).IsPositive := by
  rw [historyTransfer_convex]
  obtain ⟨ha,hb,hc⟩ := GibbsBlockRelaxation.time_coefficients_nonneg γ η t hγ hη ht
  exact (((historyScalarProjection_positive p rs).smul_of_nonneg (by exact_mod_cast ha)).add
    ((historyDiagonalProjection_positive p rs).smul_of_nonneg (by exact_mod_cast hb))).add
    (ContinuousLinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast hc))

theorem historyTransfer_selfAdjoint (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    IsSelfAdjoint (historyTransfer p rs γ η t) :=
  (historyTransfer_positive p rs γ η t hγ hη ht).isSelfAdjoint

theorem historyTransfer_norm_le (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : HistorySpace p rs) :
    ‖historyTransfer p rs γ η t z‖ ≤ ‖z‖ := by
  rw [← (historyReferenceEquiv p rs).norm_map (historyTransfer p rs γ η t z), historyReferenceEquiv_transfer,
    ← (historyReferenceEquiv p rs).norm_map z]
  exact transfer_norm_le p.value 0 p.nonnegative p.bounded le_rfl zero_le_one
    γ η t hγ hη ht (E z)

theorem historyTransfer_zero (γ η : ℝ) : historyTransfer p rs γ η 0 = 1 := by
  ext z
  simp only [historyTransfer_apply, mul_zero, Real.exp_zero, Complex.ofReal_one,
    one_smul, one_apply_eq_self]
  abel

theorem historyTransfer_comp (γ η s t : ℝ) (z : HistorySpace p rs) :
    historyTransfer p rs γ η (s+t) z =
      historyTransfer p rs γ η s (historyTransfer p rs γ η t z) := by
  apply (historyReferenceEquiv p rs).injective
  simp only [historyReferenceEquiv_transfer]
  exact transfer_comp p.value 0 p.nonnegative p.bounded le_rfl zero_le_one γ η s t (E z)

theorem historyGenerator_positive (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    (historyGenerator p rs γ η).IsPositive := by
  change ((γ : ℂ) • historyScalarComplement p rs +
    (η : ℂ) • (1-B)).IsPositive
  exact ((historyScalarComplement_positive p rs).smul_of_nonneg (by exact_mod_cast hγ)).add
    ((historyProjection_positive_of_idempotent p rs (1-B)
      ((ContinuousLinearMap.isPositive_one.isSymmetric).sub (historyDiagonalProjection_symmetric p rs))
      (historyOffDiagonalProjection_twice p rs)).smul_of_nonneg (by exact_mod_cast hη))

theorem historyGenerator_selfAdjoint (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    IsSelfAdjoint (historyGenerator p rs γ η) :=
  (historyGenerator_positive p rs γ η hγ hη).isSelfAdjoint

/-- Actual finite Kraus jump duality on every complex matrix input. -/
theorem history_quotient_generator_GKSL (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (z : HistorySpace p rs) (X : Mat2) :
    (historyCoordinates p rs z * OpenSystems.lindbladGenerator 0
      (GibbsBlockRelaxation.jumps signature weights γ η) X).trace =
      (historyCoordinates p rs (-historyGenerator p rs γ η z)*X).trace := by
  rw [historyGenerator_coordinates, actual_generator_duality γ η hγ hη]

/-- Naturality of the genuine transfer under one literal outer intervention. -/
theorem historyTransfer_outer (q : Gap) (γ η t : ℝ) (z : HistorySpace p rs) :
    outerMap p q rs (historyTransfer p rs γ η t z) =
      historyTransfer p (rs++[q]) γ η t (outerMap p q rs z) := by
  apply (historyReferenceEquiv p (rs++[q])).injective
  rw [historyReferenceEquiv_outer, historyReferenceEquiv_transfer, historyReferenceEquiv_transfer,
    historyReferenceEquiv_outer]

theorem historyGenerator_outer (q : Gap) (γ η : ℝ) (z : HistorySpace p rs) :
    outerMap p q rs (historyGenerator p rs γ η z) =
      historyGenerator p (rs++[q]) γ η (outerMap p q rs z) := by
  apply (historyReferenceEquiv p (rs++[q])).injective
  rw [historyReferenceEquiv_outer, historyReferenceEquiv_generator, historyReferenceEquiv_generator,
    historyReferenceEquiv_outer]

/-- All ordered outer extensions preserve the actual transfer, at both central ranks. -/
theorem historyTransfer_extension (qs : List Gap) (γ η t : ℝ) (z : HistorySpace p rs) :
    extensionMap p rs qs (historyTransfer p rs γ η t z) =
      historyTransfer p (extendSchedule rs qs) γ η t (extensionMap p rs qs z) := by
  apply (historyReferenceEquiv p (extendSchedule rs qs)).injective
  rw [historyReferenceEquiv_extension, historyReferenceEquiv_transfer, historyReferenceEquiv_transfer,
    historyReferenceEquiv_extension]

theorem historyGenerator_extension (qs : List Gap) (γ η : ℝ) (z : HistorySpace p rs) :
    extensionMap p rs qs (historyGenerator p rs γ η z) =
      historyGenerator p (extendSchedule rs qs) γ η (extensionMap p rs qs z) := by
  apply (historyReferenceEquiv p (extendSchedule rs qs)).injective
  rw [historyReferenceEquiv_extension, historyReferenceEquiv_generator, historyReferenceEquiv_generator,
    historyReferenceEquiv_extension]

/-- The explicit schedule transport retains the order of every extension. -/
theorem historyTransfer_ordered_composition (as bs : List Gap) (γ η t : ℝ)
    (z : HistorySpace p rs) :
    scheduleTransport p (extendSchedule_composition rs as bs)
      (extensionMap p rs (as++bs) (historyTransfer p rs γ η t z)) =
    historyTransfer p (extendSchedule (extendSchedule rs as) bs) γ η t
      (extensionMap p (extendSchedule rs as) bs (extensionMap p rs as z)) := by
  rw [extensionMap_composition, historyTransfer_extension, historyTransfer_extension]

theorem historyGenerator_ordered_composition (as bs : List Gap) (γ η : ℝ)
    (z : HistorySpace p rs) :
    scheduleTransport p (extendSchedule_composition rs as bs)
      (extensionMap p rs (as++bs) (historyGenerator p rs γ η z)) =
    historyGenerator p (extendSchedule (extendSchedule rs as) bs) γ η
      (extensionMap p (extendSchedule rs as) bs (extensionMap p rs as z)) := by
  rw [extensionMap_composition, historyGenerator_extension, historyGenerator_extension]

theorem historyGenerator_transfer (γ η t : ℝ) (z : HistorySpace p rs) :
    historyGenerator p rs γ η (historyTransfer p rs γ η t z) =
      ((γ:ℂ)*(Real.exp (-γ*t):ℂ)) • (B z-C z) +
      (((γ+η:ℝ):ℂ)*(Real.exp (-(γ+η)*t):ℂ)) • (z-B z) := by
  simp only [historyGenerator_apply, historyTransfer_apply, map_add, map_smul, map_sub,
    historyScalarProjection_twice, historyDiagonalProjection_twice,
    historyScalarProjection_after_diagonal, historyDiagonalProjection_after_scalar,
    Complex.ofReal_add]
  module

/-- The derivative is the negative actual dissipation generator, for every real time. -/
theorem history_orbit_hasDerivAt (γ η t : ℝ) (z : HistorySpace p rs) :
    HasDerivAt (fun s : ℝ => historyTransfer p rs γ η s z)
      (-historyGenerator p rs γ η (historyTransfer p rs γ η t z)) t := by
  have hs : HasDerivAt (fun s : ℝ => Real.exp (-γ*s)) (Real.exp (-γ*t)*(-γ)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-γ)).exp
  have hf : HasDerivAt (fun s : ℝ => Real.exp (-(γ+η)*s))
      (Real.exp (-(γ+η)*t)*(-(γ+η))) t := by
    simpa using ((hasDerivAt_id t).const_mul (-(γ+η))).exp
  have hd := ((hasDerivAt_const t (C z)).add
    (hs.ofReal_comp.smul_const (B z-C z))).add (hf.ofReal_comp.smul_const (z-B z))
  simp only [historyTransfer_apply]
  convert hd using 1
  · rfl
  · rw [← historyTransfer_apply, historyGenerator_transfer]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, zero_add]
    module

theorem history_orbit_continuous (γ η : ℝ) (z : HistorySpace p rs) :
    Continuous (fun t : ℝ => historyTransfer p rs γ η t z) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (history_orbit_hasDerivAt p rs γ η t z).continuousAt)

/-- At central reset the actual transfer is identity at every finite time. -/
theorem historyTransfer_reset (hp : p.value=0) (γ η t : ℝ) :
    historyTransfer p rs γ η t = 1 := by
  simp [historyTransfer, historyScalarProjection_reset p rs hp,
    historyDiagonalProjection_reset p rs hp]

theorem historyGenerator_reset (hp : p.value=0) (γ η : ℝ) :
    historyGenerator p rs γ η = 0 := by
  simp [historyGenerator, historyScalarProjection_reset p rs hp,
    historyDiagonalProjection_reset p rs hp]

theorem historyTransfer_rates_zero (t : ℝ) : historyTransfer p rs 0 0 t = 1 := by
  ext z
  apply (historyReferenceEquiv p rs).injective
  rw [historyReferenceEquiv_transfer, rates_zero_identity]
  rfl

/-- The all-depth orbit converges to its scalar component for positive reset rate. -/
theorem historyTransfer_tendsto_scalar (γ η : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η)
    (z : HistorySpace p rs) :
    Filter.Tendsto (fun t : ℝ => historyTransfer p rs γ η t z) Filter.atTop (nhds (C z)) := by
  have hs := decay_tendsto γ hγ
  have hf := decay_tendsto (γ+η) (by linarith)
  have hC : Filter.Tendsto (fun _ : ℝ => C z) Filter.atTop (nhds (C z)) := tendsto_const_nhds
  have hBC : Filter.Tendsto (fun _ : ℝ => B z-C z) Filter.atTop (nhds (B z-C z)) := tendsto_const_nhds
  have hIB : Filter.Tendsto (fun _ : ℝ => z-B z) Filter.atTop (nhds (z-B z)) := tendsto_const_nhds
  simpa only [historyTransfer_apply, zero_smul, add_zero] using (hC.add (hs.smul hBC)).add (hf.smul hIB)

/-- Zero reset rate leaves precisely the diagonal limit under positive dephasing. -/
theorem historyTransfer_tendsto_diagonal (η : ℝ) (hη : 0 < η) (z : HistorySpace p rs) :
    Filter.Tendsto (fun t : ℝ => historyTransfer p rs 0 η t z) Filter.atTop (nhds (B z)) := by
  have hf := transfer_tendsto_diagonal p.value 0 p.nonnegative p.bounded
    le_rfl zero_le_one η hη (E z)
  have he := (historyReferenceEquiv p rs).symm.continuous.continuousAt.tendsto.comp hf
  simpa only [Function.comp_def, ← historyReferenceEquiv_transfer,
    ← historyReferenceEquiv_diagonal, LinearIsometryEquiv.symm_apply_apply] using he

/-- Exact sector error, transported with the proved weighted inner-product isometry. -/
theorem historyTransfer_error_sq (γ η t : ℝ) (z : HistorySpace p rs) :
    ‖historyTransfer p rs γ η t z-C z‖^2 =
      Real.exp (-γ*t)^2*‖B z-C z‖^2 + Real.exp (-(γ+η)*t)^2*‖z-B z‖^2 := by
  rw [← (historyReferenceEquiv p rs).norm_map (historyTransfer p rs γ η t z-C z),
    ← (historyReferenceEquiv p rs).norm_map (B z-C z),
    ← (historyReferenceEquiv p rs).norm_map (z-B z)]
  simp only [map_sub, historyReferenceEquiv_transfer, historyReferenceEquiv_scalar,
    historyReferenceEquiv_diagonal]
  exact transfer_error_sq p.value 0 p.nonnegative p.bounded le_rfl zero_le_one γ η t (E z)

theorem historyTransfer_error_bound (γ η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (z : HistorySpace p rs) :
    ‖historyTransfer p rs γ η t z-C z‖ ≤ Real.exp (-γ*t)*‖z-C z‖ := by
  rw [← (historyReferenceEquiv p rs).norm_map (historyTransfer p rs γ η t z-C z),
    ← (historyReferenceEquiv p rs).norm_map (z-C z)]
  simp only [map_sub, historyReferenceEquiv_transfer, historyReferenceEquiv_scalar]
  exact transfer_error_bound p.value 0 p.nonnegative p.bounded le_rfl zero_le_one
    γ η t hη ht (E z)

/-- Operator norm conjugation uses the genuine surjective weighted isometry. -/
theorem historyReferenceEquiv_opNorm (P : HistorySpace p rs →L[ℂ] HistorySpace p rs)
    (Q : HistoryReference p →L[ℂ] HistoryReference p)
    (hPQ : ∀ z, E (P z)=Q (E z)) : ‖P‖=‖Q‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Q)
    intro z
    rw [← (historyReferenceEquiv p rs).norm_map (P z), hPQ,
      ← (historyReferenceEquiv p rs).norm_map z]
    exact Q.le_opNorm (E z)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P)
    intro w
    obtain ⟨z,rfl⟩ := (historyReferenceEquiv p rs).surjective w
    rw [← hPQ, (historyReferenceEquiv p rs).norm_map, (historyReferenceEquiv p rs).norm_map]
    exact P.le_opNorm z

/-- Sharp norm requires positive central retention; no side retention is restricted. -/
theorem historyTransfer_centered_opNorm (hpos : 0 < p.value) (γ η t : ℝ)
    (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖historyTransfer p rs γ η t-C‖ = Real.exp (-γ*t) := by
  rw [historyReferenceEquiv_opNorm p rs (historyTransfer p rs γ η t-C)
    (TR γ η t-scalarProjection p.value 0 p.nonnegative p.bounded le_rfl zero_le_one)
    (by intro z; simp only [_root_.sub_apply, map_sub, historyReferenceEquiv_transfer,
      historyReferenceEquiv_scalar])]
  exact centered_operator_norm p.value 0 p.nonnegative p.bounded le_rfl zero_le_one
    hpos γ η t hη ht

theorem historyTransfer_centered_opNorm_reset (hp : p.value=0) (γ η t : ℝ) :
    ‖historyTransfer p rs γ η t-C‖ = 0 := by
  rw [historyTransfer_reset p rs hp, historyScalarProjection_reset p rs hp, sub_self, norm_zero]

theorem historyTransfer_constant (γ η t : ℝ) :
    historyTransfer p rs γ η t (historyConstantVector p rs) = historyConstantVector p rs := by
  rw [historyTransfer_apply, historyScalarProjection_constant, historyDiagonalProjection_constant]
  simp

theorem historyTransfer_centered (γ η t : ℝ) (a : Fin 3) :
    historyTransfer p rs γ η t (historyCenteredVector p rs a) =
      (Real.exp (-(if a=2 then γ else γ+η)*t) : ℂ) • historyCenteredVector p rs a := by
  rw [historyTransfer_apply, historyScalarProjection_centered, historyDiagonalProjection_centered]
  split_ifs <;> simp

theorem historyTransfer_complex (γ η t : ℝ) :
    historyTransfer p rs γ η t (historyComplexVector p rs) =
      (Real.exp (-(γ+η)*t) : ℂ) • historyComplexVector p rs := by
  rw [historyTransfer_apply, historyScalarProjection_complex, historyDiagonalProjection_complex]
  simp

theorem historyTransfer_centered_norm_sq (γ η t : ℝ) (a : Fin 3) :
    ‖historyTransfer p rs γ η t (historyCenteredVector p rs a)‖^2 =
      modeNorm a*p.value^2*Real.exp (-(if a=2 then γ else γ+η)*t)^2 := by
  rw [historyTransfer_centered, norm_smul, mul_pow, historyCenteredVector_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

theorem historyTransfer_complex_norm_sq (γ η t : ℝ) :
    ‖historyTransfer p rs γ η t (historyComplexVector p rs)‖^2 =
      (48*p.value^2/25)*Real.exp (-(γ+η)*t)^2 := by
  rw [historyTransfer_complex, norm_smul, mul_pow, historyComplexVector_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

/-- A scalar fixed point is exactly a multiple of the nonzero actual constant class. -/
theorem historyScalarProjection_fixed_line (z : HistorySpace p rs) :
    C z=z ↔ ∃ c : ℂ, z=c • historyConstantVector p rs := by
  constructor
  · intro hz
    refine ⟨(rhoN*historyCoordinates p rs z).trace,?_⟩
    apply historyCoordinates_injective p rs
    rw [map_smul, historyConstantVector_coordinates]
    have h := historyScalarProjection_coordinates p rs z
    rw [hz] at h
    exact h
  · rintro ⟨c,rfl⟩
    rw [map_smul, historyScalarProjection_constant]

theorem historyTransfer_fixed_scalar (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t)
    (z : HistorySpace p rs) : historyTransfer p rs γ η t z=z ↔ C z=z := by
  rw [← (historyReferenceEquiv p rs).injective.eq_iff,
    ← (historyReferenceEquiv p rs).injective.eq_iff (a := C z) (b := z)]
  rw [historyReferenceEquiv_transfer, historyReferenceEquiv_scalar]
  exact transfer_fixed_scalar p.value 0 p.nonnegative p.bounded le_rfl zero_le_one
    γ η t hγ hη ht (E z)

theorem historyTransfer_fixed_line (γ η t : ℝ) (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t)
    (z : HistorySpace p rs) :
    historyTransfer p rs γ η t z=z ↔ ∃ c : ℂ, z=c • historyConstantVector p rs := by
  rw [historyTransfer_fixed_scalar p rs γ η t hγ hη ht, historyScalarProjection_fixed_line]

theorem historyTransfer_fixed_diagonal (η t : ℝ) (hη : 0 < η) (ht : 0 < t)
    (z : HistorySpace p rs) : historyTransfer p rs 0 η t z=z ↔ B z=z := by
  rw [← (historyReferenceEquiv p rs).injective.eq_iff,
    ← (historyReferenceEquiv p rs).injective.eq_iff (a := B z) (b := z)]
  rw [historyReferenceEquiv_transfer, historyReferenceEquiv_diagonal]
  exact transfer_fixed_diagonal p.value 0 p.nonnegative p.bounded le_rfl zero_le_one
    η t hη ht (E z)

theorem historyDiagonalProjection_fixed_range (z : HistorySpace p rs) : B z=z ↔ z ∈ (B).range := by
  constructor
  · intro hz; exact ⟨z,hz⟩
  · rintro ⟨w,rfl⟩; exact historyDiagonalProjection_twice p rs w

theorem historyTransfer_fixed_diagonal_range (η t : ℝ) (hη : 0 < η) (ht : 0 < t)
    (z : HistorySpace p rs) : historyTransfer p rs 0 η t z=z ↔ z ∈ (B).range := by
  rw [historyTransfer_fixed_diagonal p rs η t hη ht, historyDiagonalProjection_fixed_range]

/-- Four actual inner modes, with the literal constant first. -/
def historyFourModeVector : Fin 4 → HistorySpace p rs :=
  ![historyConstantVector p rs, historyCenteredVector p rs 0,
    historyCenteredVector p rs 1, historyCenteredVector p rs 2]

theorem historyFourModeVector_reference (i : Fin 4) :
    E (historyFourModeVector p rs i) =
      mk _ (kernel_posSemidef p.value 0 p.nonnegative p.bounded le_rfl zero_le_one) (fourMode i) := by
  fin_cases i
  · exact historyReferenceEquiv_constant p rs
  · exact historyReferenceEquiv_centered p rs 0
  · exact historyReferenceEquiv_centered p rs 1
  · exact historyReferenceEquiv_centered p rs 2

/-- Positive central retention makes these four actual modes span every history class. -/
theorem history_four_modes_span (hpos : 0 < p.value) (z : HistorySpace p rs) :
    ∃ c : Fin 4 → ℂ, z=∑ i,c i • historyFourModeVector p rs i := by
  obtain ⟨c,hc⟩ := quotient_four_modes_span p.value 0 p.nonnegative p.bounded le_rfl zero_le_one hpos (E z)
  refine ⟨c,?_⟩
  apply (historyReferenceEquiv p rs).injective
  simpa only [map_sum, map_smul, historyFourModeVector_reference] using hc

/-- Finite positive-time dynamics cannot be a scalar operator when decay is present. -/
theorem historyTransfer_not_scalar (hpos : 0 < p.value) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (hrate : 0 < γ ∨ 0 < η) (ht : 0 < t) (c : ℂ) :
    historyTransfer p rs γ η t ≠ c • (1 : HistorySpace p rs →L[ℂ] HistorySpace p rs) := by
  intro he
  apply transfer_not_scalar p.value 0 p.nonnegative p.bounded le_rfl zero_le_one hpos
    γ η t hγ hη hrate ht c
  ext w
  obtain ⟨z,rfl⟩ := (historyReferenceEquiv p rs).surjective w
  rw [← historyReferenceEquiv_transfer, he]
  simp

/-- The diagonal range is represented by its two actual matrix diagonal entries. -/
def historyDiagonalRangeCoordinates : (B).range →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun z i := historyCoordinates p rs z.val i i
  map_add' z w := by ext i; simp
  map_smul' c z := by ext i; simp

theorem history_range_diagonal_coordinates (z : (B).range) :
    diagonalPart (historyCoordinates p rs z.val)=historyCoordinates p rs z.val := by
  obtain ⟨w,hw⟩ := z.property
  rw [← hw]
  change diagonalPart (historyCoordinates p rs (B w))=historyCoordinates p rs (B w)
  rw [historyDiagonalProjection_coordinates, diagonal_idempotent]

theorem historyDiagonalRangeCoordinates_injective :
    Function.Injective (historyDiagonalRangeCoordinates p rs) := by
  intro z w h
  apply Subtype.ext
  apply historyCoordinates_injective p rs
  rw [← history_range_diagonal_coordinates p rs z, ← history_range_diagonal_coordinates p rs w]
  unfold diagonalPart
  congr 1

theorem historyDiagonalRangeCoordinates_surjective (hpos : 0 < p.value) :
    Function.Surjective (historyDiagonalRangeCoordinates p rs) := by
  intro v
  let z := (historyCoordinateEquiv p hpos rs).symm (Matrix.diagonal v)
  have hz : historyCoordinates p rs z=Matrix.diagonal v :=
    (historyCoordinateEquiv p hpos rs).apply_symm_apply _
  refine ⟨⟨B z,⟨z,rfl⟩⟩,?_⟩
  ext i
  change historyCoordinates p rs (B z) i i=v i
  rw [historyDiagonalProjection_coordinates, hz]
  simp [diagonalPart]

theorem history_diagonal_range_finrank (hpos : 0 < p.value) :
    Module.finrank ℂ (B).range=2 := by
  let e := LinearEquiv.ofBijective (historyDiagonalRangeCoordinates p rs)
    ⟨historyDiagonalRangeCoordinates_injective p rs,
      historyDiagonalRangeCoordinates_surjective p rs hpos⟩
  rw [e.finrank_eq]
  simp

/-- The scalar range is measured by its actual faithful-state mean. -/
def historyScalarRangeCoordinates : (C).range →ₗ[ℂ] ℂ where
  toFun z := (rhoN*historyCoordinates p rs z.val).trace
  map_add' z w := by simp [mul_add, Matrix.trace_add]
  map_smul' c z := by simp [Matrix.trace_smul]

theorem historyScalarRangeCoordinates_injective :
    Function.Injective (historyScalarRangeCoordinates p rs) := by
  intro z w h
  apply Subtype.ext
  apply historyCoordinates_injective p rs
  obtain ⟨v,hv⟩ := z.property
  obtain ⟨u,hu⟩ := w.property
  have hz : scalarPart (historyCoordinates p rs z.val)=historyCoordinates p rs z.val := by
    rw [← hv]
    change scalarPart (historyCoordinates p rs (C v))=historyCoordinates p rs (C v)
    rw [historyScalarProjection_coordinates, scalar_idempotent]
  have hw : scalarPart (historyCoordinates p rs w.val)=historyCoordinates p rs w.val := by
    rw [← hu]
    change scalarPart (historyCoordinates p rs (C u))=historyCoordinates p rs (C u)
    rw [historyScalarProjection_coordinates, scalar_idempotent]
  rw [← hz, ← hw]
  exact congrArg (fun c : ℂ => c • (1 : Mat2)) h

theorem historyScalarRangeCoordinates_surjective :
    Function.Surjective (historyScalarRangeCoordinates p rs) := by
  intro c
  refine ⟨⟨c • historyConstantVector p rs,⟨c • historyConstantVector p rs,?_⟩⟩,?_⟩
  · change C (c • historyConstantVector p rs)=c • historyConstantVector p rs
    rw [map_smul, historyScalarProjection_constant]
  · change (rhoN*historyCoordinates p rs (c • historyConstantVector p rs)).trace=c
    rw [map_smul, historyConstantVector_coordinates]
    simp [Matrix.trace_smul, rhoN_trace]

/-- The scalar fixed space has complex dimension one at every central retention. -/
theorem history_scalar_range_finrank : Module.finrank ℂ (C).range=1 := by
  let e := LinearEquiv.ofBijective (historyScalarRangeCoordinates p rs)
    ⟨historyScalarRangeCoordinates_injective p rs, historyScalarRangeCoordinates_surjective p rs⟩
  rw [e.finrank_eq]
  simp

/-- Reset makes the diagonal range the whole one-dimensional history quotient. -/
theorem history_diagonal_range_finrank_reset (hp : p.value=0) :
    Module.finrank ℂ (B).range=1 := by
  rw [historyDiagonalProjection_reset p rs hp]
  change Module.finrank ℂ (LinearMap.id : HistorySpace p rs →ₗ[ℂ] HistorySpace p rs).range=1
  rw [LinearMap.range_id]
  simpa using history_reset_finrank p hp rs

end
end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
