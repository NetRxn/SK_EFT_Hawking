import SKEFTHawking.FiniteGibbsReflectedHistory
import SKEFTHawking.FiniteGibbsReset

/-! A constant probe and centered probes of one actual finite Gibbs history.
The unital reflected quotient embeds isometrically onto diagonal Gibbs observables
and intertwines the actual reset channel. This finite computational-probe sector
does not assert a full field reconstruction or a translated-history semigroup. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsUnitalHistory
open Matrix FiniteInterventionProcess GibbsRelaxationProcess GibbsTwoTimeProcess GibbsHistoryKernel
open FinitePositiveKernel FinitePositiveKernel.GibbsObservable FinitePositiveKernel.DiagonalLindblad
open scoped ComplexOrder InnerProductSpace

/-- Only model parameters and the nonempty ordered sector schedule are supplied. -/
structure Data (n : ℕ) where
  β : ℝ
  Δ : ℝ
  γ : ℝ
  η : ℝ
  rate_nonnegative : 0 ≤ γ
  dephasing_nonnegative : 0 ≤ η
  times : Fin (n+1) → ℝ
  ordered : Monotone times
  nonnegative : ∀ i,0 ≤ times i

variable {n : ℕ}

def base (d : Data n) := GibbsReflectedHistory.reflection d.β d.Δ d.γ d.η
  d.rate_nonnegative d.dephasing_nonnegative d.times d.ordered d.nonnegative

def schedule (d : Data n) := extendSchedule (GibbsReflectedHistory.symmetricSchedule d.times)

theorem schedule_monotone (d : Data n) : Monotone (schedule d) :=
  extendSchedule_monotone (GibbsReflectedHistory.symmetric_monotone d.ordered d.nonnegative)

def history (d : Data n) := historyTree d.β d.Δ d.γ d.η d.rate_nonnegative d.dephasing_nonnegative
  (2*n+1) (schedule d) (schedule_monotone d)

def mass (d : Data n) (h : History 2 (2*n+1+1)) : ℝ :=
  weight Qubit Unit 2 (history d) h (joint (equilibrium d.β d.Δ))

/-- None is a probe, not an additional measurement event. -/
def probe (d : Data n) (h : History 2 (2*n+1+1)) : Option (Fin (2*n+1+1)) → ℝ
  | none => 1
  | some i => centered d.β d.Δ (outcome h i.val)

def moment (d : Data n) : Matrix (Option (Fin (2*n+1+1))) (Option (Fin (2*n+1+1))) ℂ :=
  fun i j => ((∑ h,mass d h*(probe d h i*probe d h j):ℝ):ℂ)

theorem mass_sum (d : Data n) : ∑ h,mass d h=1 :=
  (normalized_weights Qubit Unit 2 (history d) (joint_density _ (equilibrium_density d.β d.Δ))).2

theorem mass_nonnegative (d : Data n) (h : History 2 (2*n+1+1)) : 0 ≤ mass d h :=
  (normalized_weights Qubit Unit 2 (history d) (joint_density _ (equilibrium_density d.β d.Δ))).1 h

theorem centered_mean (d : Data n) (i : Fin (2*n+1+1)) :
    (∑ h,mass d h*centered d.β d.Δ (outcome h i.val))=0 := by
  have h := pair_expectation d.β d.Δ d.γ (2*n+1) (schedule d) i.val i.val le_rfl
    (by omega) (fun a _ => centered d.β d.Δ a)
  simp only [mass,history,history_weight]
  rw [h]
  simp only [sub_self,transition_zero]
  have hn : weights d.β d.Δ 0+weights d.β d.Δ 1=1 := by
    simpa only [Fin.sum_univ_two] using weights_sum d.β d.Δ
  simp [Fin.sum_univ_two,centered,sign,meanZ]
  rw [show weights d.β d.Δ 1=1-weights d.β d.Δ 0 by linarith]
  ring

theorem moment_none_none (d : Data n) : moment d none none=1 := by
  simp only [moment,probe,mul_one,mass_sum,Complex.ofReal_one]

theorem moment_none_some (d : Data n) (i : Fin (2*n+1+1)) : moment d none (some i)=0 := by
  simp only [moment,probe,one_mul,centered_mean,Complex.ofReal_zero]

theorem moment_some_none (d : Data n) (i : Fin (2*n+1+1)) : moment d (some i) none=0 := by
  simp only [moment,probe,mul_one,centered_mean,Complex.ofReal_zero]

theorem moment_some_some (d : Data n) (i j : Fin (2*n+1+1)) :
    moment d (some i) (some j)=(base d).covariance i j := rfl

def reflection (d : Data n) : ReflectionData (Option (Fin (2*n+1+1))) (Option (Fin (n+1))) where
  theta := Option.map GibbsReflectedHistory.reverse
  involutive := by intro i; cases i with
    | none => rfl
    | some i => simp [GibbsReflectedHistory.reverse_involutive n i]
  positiveSector := ⟨Option.map (GibbsReflectedHistory.positive n),by
    intro i j h
    cases i <;> cases j <;> simp_all
    ⟩
  covariance := moment d

theorem kernel_none_none (d : Data n) : (reflection d).kernel none none=1 := moment_none_none d

theorem kernel_none_some (d : Data n) (i : Fin (n+1)) : (reflection d).kernel none (some i)=0 :=
  moment_none_some d _

theorem kernel_some_none (d : Data n) (i : Fin (n+1)) : (reflection d).kernel (some i) none=0 :=
  moment_some_none d _

theorem kernel_some_some (d : Data n) (i j : Fin (n+1)) :
    (reflection d).kernel (some i) (some j)=(base d).kernel i j := rfl

def amplitude (d : Data n) (c : Option (Fin (n+1)) → ℂ) : ℂ :=
  GibbsReflectedHistory.amplitude d.γ d.times (fun i => c (some i))

theorem pairing_modes (d : Data n) (c e : Option (Fin (n+1)) → ℂ) :
    pairing (reflection d).kernel c e=star (c none)*e none+
      ((1-meanZ d.β d.Δ^2:ℝ):ℂ)*star (amplitude d c)*amplitude d e := by
  have h := GibbsReflectedHistory.reflected_pairing d.β d.Δ d.γ d.η d.rate_nonnegative
    d.dephasing_nonnegative d.times d.ordered d.nonnegative (fun i => c (some i)) (fun i => e (some i))
  calc
    _ = star (c none)*e none+pairing (base d).kernel (fun i => c (some i)) (fun i => e (some i)) := by
      simp [pairing,dotProduct,mulVec,Fintype.sum_option,kernel_none_none,kernel_none_some,kernel_some_none,kernel_some_some]
    _ = _ := by unfold base; rw [h]; rfl

theorem positive (d : Data n) : (reflection d).kernel.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · have hb := (GibbsReflectedHistory.reflected_positive d.β d.Δ d.γ d.η d.rate_nonnegative
      d.dephasing_nonnegative d.times d.ordered d.nonnegative).isHermitian
    ext i j
    cases i <;> cases j
    · simp [Matrix.conjTranspose_apply,kernel_none_none]
    · simp [Matrix.conjTranspose_apply,kernel_none_some,kernel_some_none]
    · simp [Matrix.conjTranspose_apply,kernel_none_some,kernel_some_none]
    · exact congrFun (congrFun hb _) _
  · intro c
    change 0 ≤ pairing (reflection d).kernel c c
    rw [pairing_modes]
    have hv : (0:ℂ) ≤ ((1-meanZ d.β d.Δ^2:ℝ):ℂ) := by exact_mod_cast (stationary_variance_pos d.β d.Δ).le
    simpa only [mul_assoc] using add_nonneg (star_mul_self_nonneg (c none))
      (mul_nonneg hv (star_mul_self_nonneg (amplitude d c)))

abbrev Reconstructed (d : Data n) := FinitePositiveKernel.Space (reflection d).kernel (positive d)

theorem pairing_self_real (d : Data n) (c : Option (Fin (n+1)) → ℂ) :
    pairing (reflection d).kernel c c=
      ((Complex.normSq (c none)+(1-meanZ d.β d.Δ^2)*Complex.normSq (amplitude d c):ℝ):ℂ) := by
  rw [pairing_modes]
  simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.normSq_eq_conj_mul_self,Complex.star_def,mul_assoc]

theorem null_iff (d : Data n) (c : Option (Fin (n+1)) → ℂ) :
    mk _ (positive d) c=0 ↔ c none=0 ∧ amplitude d c=0 := by
  rw [mk_eq_zero_iff,pairing_self_real,Complex.ofReal_eq_zero]
  have hv := stationary_variance_pos d.β d.Δ
  have hn := Complex.normSq_nonneg (c none)
  have ha := Complex.normSq_nonneg (amplitude d c)
  constructor
  · intro h
    have hca : Complex.normSq (c none)=0 ∧ Complex.normSq (amplitude d c)=0 := by
      constructor
      · nlinarith [mul_nonneg hv.le ha]
      · nlinarith [mul_nonneg hv.le ha]
    simpa only [Complex.normSq_eq_zero] using hca
  · rintro ⟨hc,ha⟩
    simp [hc,ha]

abbrev Target (d : Data n) := WeightedSpace (weights d.β d.Δ) (weights_pos d.β d.Δ)

/-- All diagonal qubit observables, expressed in constant and centered coordinates. -/
def modeMatrix (d : Data n) (a b : ℂ) : Matrix Qubit Qubit ℂ :=
  diagonal (fun i => a+b*((sign i-meanZ d.β d.Δ:ℝ):ℂ))

def mode (d : Data n) (a b : ℂ) : Target d :=
  observable (density_posDef _ (weights_pos d.β d.Δ)).posSemidef (modeMatrix d a b)

theorem mode_inner (d : Data n) (a b c e : ℂ) :
    ⟪mode d a b,mode d c e⟫_ℂ=star a*c+((1-meanZ d.β d.Δ^2:ℝ):ℂ)*star b*e := by
  rw [mode,mode,inner_observable]
  have hn : (weights d.β d.Δ 1:ℂ)=1-(weights d.β d.Δ 0:ℂ) := by
    have h := weights_sum d.β d.Δ
    simp only [Fin.sum_univ_two] at h
    exact_mod_cast (show weights d.β d.Δ 1=1-weights d.β d.Δ 0 by linarith)
  simp [modeMatrix,density,Matrix.trace,Fin.sum_univ_two,sign,meanZ]
  rw [hn]
  ring

def matrixLinear (d : Data n) : Coefficients (positive d) →ₗ[ℂ] Matrix Qubit Qubit ℂ where
  toFun c := modeMatrix d (c none) (amplitude d c)
  map_add' c e := by
    ext i j
    by_cases h : i=j
    · subst j
      simp only [modeMatrix, Matrix.diagonal_apply_eq, Matrix.add_apply]
      change c none + e none + (∑ k, (c (some k)+e (some k))*GibbsReflectedHistory.decay d.γ (d.times k)) * _ = _
      simp [amplitude,GibbsReflectedHistory.amplitude,Finset.sum_add_distrib,add_mul]
      ring
    · simp [modeMatrix,h]
  map_smul' r c := by
    ext i j
    by_cases h : i=j
    · subst j
      simp only [modeMatrix, Matrix.diagonal_apply_eq, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
      change r*c none + (∑ k, (r*c (some k))*GibbsReflectedHistory.decay d.γ (d.times k)) * _ = _
      simp [amplitude,GibbsReflectedHistory.amplitude,← Finset.mul_sum,mul_assoc]
      ring
    · simp [modeMatrix,h]

def coefficientMap (d : Data n) : Coefficients (positive d) →ₗ[ℂ] Target d :=
  (observableLinear (density_posDef _ (weights_pos d.β d.Δ)).posSemidef).comp (matrixLinear d)

theorem coefficientMap_apply (d : Data n) (c : Coefficients (positive d)) :
    coefficientMap d c=mode d (c none) (amplitude d c) := rfl

theorem coefficientMap_inner (d : Data n) (c e : Coefficients (positive d)) :
    ⟪coefficientMap d c,coefficientMap d e⟫_ℂ=pairing (reflection d).kernel c e := by
  rw [coefficientMap_apply,coefficientMap_apply,mode_inner,pairing_modes]

theorem coefficientMap_null (d : Data n) : nullSpace (reflection d).kernel (positive d) ≤ (coefficientMap d).ker := by
  intro c hc
  apply LinearMap.mem_ker.mpr
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [coefficientMap_inner]
  exact (mem_nullSpace_iff _ _ c).mp hc

/-- Genuine cross-kernel descent into the existing faithful observable quotient. -/
def embeddingLinear (d : Data n) : Reconstructed d →ₗ[ℂ] Target d :=
  ((nullSpace (reflection d).kernel (positive d)).liftQ (coefficientMap d) (coefficientMap_null d)).comp
    (quotientEquiv (reflection d).kernel (positive d)).symm.toLinearMap

theorem embeddingLinear_mk (d : Data n) (c : Coefficients (positive d)) :
    embeddingLinear d (mk _ (positive d) c)=coefficientMap d c := by
  rw [← quotientEquiv_mk (positive d) c]
  simp only [embeddingLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]

def embedding (d : Data n) : Reconstructed d →ₗᵢ[ℂ] Target d :=
  (embeddingLinear d).isometryOfInner (by
    intro z w
    obtain ⟨c,rfl⟩ := mk_surjective _ (positive d) z
    obtain ⟨e,rfl⟩ := mk_surjective _ (positive d) w
    rw [embeddingLinear_mk,embeddingLinear_mk,inner_mk,coefficientMap_inner])

theorem embedding_mk (d : Data n) (c : Coefficients (positive d)) :
    embedding d (mk _ (positive d) c)=mode d (c none) (amplitude d c) := embeddingLinear_mk d c

/-- A representative for every pair of constant and centered amplitudes. -/
def representative (d : Data n) (a b : ℂ) : Option (Fin (n+1)) → ℂ :=
  fun i => match i with
  | none => a
  | some j => (Pi.single 0 (b/GibbsReflectedHistory.decay d.γ (d.times 0)) : Fin (n+1) → ℂ) j

theorem representative_amplitude (d : Data n) (a b : ℂ) : amplitude d (representative d a b)=b := by
  unfold amplitude representative
  rw [GibbsReflectedHistory.amplitude_single]
  exact div_mul_cancel₀ b (GibbsReflectedHistory.decay_ne_zero _ _)

def state (d : Data n) (a b : ℂ) : Reconstructed d := mk _ (positive d) (representative d a b)

theorem embedding_state (d : Data n) (a b : ℂ) : embedding d (state d a b)=mode d a b := by
  rw [state,embedding_mk,representative_amplitude]
  rfl

theorem state_surjective (d : Data n) (z : Reconstructed d) : ∃ a b,z=state d a b := by
  obtain ⟨c,rfl⟩ := mk_surjective _ (positive d) z
  refine ⟨c none,amplitude d c,?_⟩
  apply (embedding d).injective
  rw [embedding_mk,embedding_state]

theorem mode_injective (d : Data n) {a b c e : ℂ} (h : mode d a b=mode d c e) : a=c ∧ b=e := by
  have hm := observable_injective (density_posDef _ (weights_pos d.β d.Δ)) h
  have h0 := congrFun (congrFun hm 0) 0
  have h1 := congrFun (congrFun hm 1) 1
  simp only [modeMatrix,Matrix.diagonal_apply_eq,sign] at h0 h1
  push_cast at h0 h1
  have hb : b=e := by linear_combination (h0-h1)/2
  refine ⟨?_,hb⟩
  rw [hb] at h0
  linear_combination h0

theorem state_injective (d : Data n) {a b c e : ℂ} (h : state d a b=state d c e) : a=c ∧ b=e := by
  apply mode_injective d
  simpa only [embedding_state] using congrArg (embedding d) h

def representativeLinear (d : Data n) : (ℂ × ℂ) →ₗ[ℂ] Coefficients (positive d) where
  toFun x := representative d x.1 x.2
  map_add' x y := by
    change representative d (x+y).1 (x+y).2 = fun i => representative d x.1 x.2 i + representative d y.1 y.2 i
    funext i
    cases i with
    | none => rfl
    | some i =>
      change (Pi.single 0 ((x.2+y.2)/_) : Fin (n+1) → ℂ) i = _
      by_cases h : i=0
      · subst i; simp [representative,add_div]
      · simp [representative,h]
  map_smul' r x := by
    change representative d (r • x).1 (r • x).2 = fun i => r * representative d x.1 x.2 i
    funext i
    cases i with
    | none => rfl
    | some i =>
      change (Pi.single 0 ((r*x.2)/_) : Fin (n+1) → ℂ) i = _
      by_cases h : i=0
      · subst i; simp [representative,mul_div_assoc]
      · simp [representative,h]

def stateLinear (d : Data n) : (ℂ × ℂ) →ₗ[ℂ] Reconstructed d :=
  (mkLinear _ (positive d)).comp (representativeLinear d)

theorem stateLinear_apply (d : Data n) (x : ℂ × ℂ) : stateLinear d x=state d x.1 x.2 := rfl

def coordinateEquiv (d : Data n) : (ℂ × ℂ) ≃ₗ[ℂ] Reconstructed d :=
  LinearEquiv.ofBijective (stateLinear d) ⟨by
    intro x y h
    exact Prod.ext (state_injective d h).1 (state_injective d h).2, by
    intro z
    obtain ⟨a,b,h⟩ := state_surjective d z
    exact ⟨(a,b),h.symm⟩⟩

/-- Both modes survive for every allowed rate and schedule, including zero rate. -/
theorem reconstructed_finrank (d : Data n) : Module.finrank ℂ (Reconstructed d)=2 := by
  rw [← (coordinateEquiv d).finrank_eq]
  simp

theorem embedding_range (d : Data n) (z : Target d) :
    z ∈ LinearMap.range (embedding d).toLinearMap ↔
      ∃ f : Qubit → ℂ,z=observable (density_posDef _ (weights_pos d.β d.Δ)).posSemidef (Matrix.diagonal f) := by
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨a,b,rfl⟩ := state_surjective d x
    exact ⟨_,embedding_state d a b⟩
  · rintro ⟨f,rfl⟩
    let b := (f 0-f 1)/2
    let a := f 0-b*(1-(meanZ d.β d.Δ : ℂ))
    refine ⟨state d a b,?_⟩
    change embedding d (state d a b)=_
    rw [embedding_state]
    change observable _ (modeMatrix d a b)=_
    congr 1
    ext i j
    by_cases h : i=j
    · subst j
      fin_cases i
      · simp [modeMatrix,a,b,sign]
      · simp [modeMatrix,a,b,sign]
        ring
    · simp [modeMatrix,h]

theorem state_add (d : Data n) (a b c e : ℂ) :
    state d (a+c) (b+e)=state d a b+state d c e := (stateLinear d).map_add (a,b) (c,e)

theorem state_smul (d : Data n) (r a b : ℂ) : state d (r*a) (r*b)=r • state d a b :=
  (stateLinear d).map_smul r (a,b)

theorem state_zero (d : Data n) : state d 0 0=0 := (stateLinear d).map_zero

theorem state_inner (d : Data n) (a b c e : ℂ) :
    ⟪state d a b,state d c e⟫_ℂ=star a*c+((1-meanZ d.β d.Δ^2:ℝ):ℂ)*star b*e := by
  rw [← (embedding d).inner_map_map,embedding_state,embedding_state,mode_inner]

theorem mode_add (d : Data n) (a b c e : ℂ) : mode d (a+c) (b+e)=mode d a b+mode d c e := by
  simpa only [map_add,embedding_state] using congrArg (embedding d) (state_add d a b c e)

theorem mode_smul (d : Data n) (r a b : ℂ) : mode d (r*a) (r*b)=r • mode d a b := by
  simpa only [map_smul,embedding_state] using congrArg (embedding d) (state_smul d r a b)

theorem mode_constant (d : Data n) : mode d 1 0=observable (density_posDef _ (weights_pos d.β d.Δ)).posSemidef 1 := by
  change observable _ (modeMatrix d 1 0)=_
  congr 1
  ext i j
  by_cases h : i=j
  · subst j; simp [modeMatrix]
  · simp [modeMatrix,h]

theorem mode_trace (d : Data n) (a b : ℂ) : (density (weights d.β d.Δ)*modeMatrix d a b).trace=a := by
  have h := mode_inner d 1 0 a b
  rw [mode_constant,mode,inner_observable] at h
  simp only [star_one,one_mul,star_zero,mul_zero,zero_mul,add_zero,Matrix.conjTranspose_one,Matrix.mul_one] at h
  rw [Matrix.trace_mul_comm]
  exact h

theorem mode_projection (d : Data n) (a b : ℂ) :
    GibbsReset.scalarProjection _ (weights_pos d.β d.Δ) (weights_sum d.β d.Δ) (mode d a b)=mode d a 0 := by
  rw [mode,GibbsReset.scalarProjection_observable,mode_trace,← mode_constant,← mode_smul]
  simp

theorem mode_evolution (d : Data n) (t : ℝ) (ht : 0≤t) (a b : ℂ) :
    GibbsReset.evolution _ (weights_pos d.β d.Δ) (weights_sum d.β d.Δ) d.γ t d.rate_nonnegative ht (mode d a b)=
      mode d a (GibbsReflectedHistory.decay d.γ t*b) := by
  rw [GibbsReset.evolution_apply,mode_projection,← mode_smul,← mode_smul,← mode_add]
  congr 1 <;> simp [GibbsReflectedHistory.decay]
  ring

/-- Reset acts on the two proven quotient coordinates. Its coefficient action is proved below. -/
def reset (d : Data n) (t : ℝ) : Reconstructed d →L[ℂ] Reconstructed d :=
  ((stateLinear d).comp
    (((LinearMap.fst ℂ ℂ ℂ).prod (GibbsReflectedHistory.decay d.γ t • LinearMap.snd ℂ ℂ ℂ)).comp
      (coordinateEquiv d).symm.toLinearMap)).toContinuousLinearMap

theorem reset_state (d : Data n) (t : ℝ) (a b : ℂ) :
    reset d t (state d a b)=state d a (GibbsReflectedHistory.decay d.γ t*b) := by
  change stateLinear d ((LinearMap.fst ℂ ℂ ℂ).prod (_ • LinearMap.snd ℂ ℂ ℂ)
    ((coordinateEquiv d).symm ((coordinateEquiv d) (a,b)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Actual time-Kraus quotient dynamics on every reconstructed vector. -/
theorem reset_intertwining (d : Data n) (t : ℝ) (ht : 0≤t) (z : Reconstructed d) :
    embedding d (reset d t z)=
      GibbsReset.evolution _ (weights_pos d.β d.Δ) (weights_sum d.β d.Δ) d.γ t d.rate_nonnegative ht (embedding d z) := by
  obtain ⟨a,b,rfl⟩ := state_surjective d z
  rw [reset_state,embedding_state,embedding_state,mode_evolution]

theorem mk_coordinates (d : Data n) (c : Coefficients (positive d)) :
    mk _ (positive d) c=state d (c none) (amplitude d c) := by
  apply (embedding d).injective
  rw [embedding_mk,embedding_state]

def resetCoefficients (d : Data n) (t : ℝ) (c : Option (Fin (n+1)) → ℂ) : Option (Fin (n+1)) → ℂ
  | none => c none
  | some i => GibbsReflectedHistory.decay d.γ t*c (some i)

theorem reset_coefficients_amplitude (d : Data n) (t : ℝ) (c : Option (Fin (n+1)) → ℂ) :
    amplitude d (resetCoefficients d t c)=GibbsReflectedHistory.decay d.γ t*amplitude d c := by
  simp [amplitude,GibbsReflectedHistory.amplitude,resetCoefficients,Finset.mul_sum,mul_assoc]

/-- Thus the action really descends the stated action on all history coefficients. -/
theorem reset_mk (d : Data n) (t : ℝ) (c : Coefficients (positive d)) :
    reset d t (mk _ (positive d) c)=mk _ (positive d) (resetCoefficients d t c) := by
  rw [mk_coordinates,reset_state,mk_coordinates,reset_coefficients_amplitude]
  rfl

theorem reset_zero (d : Data n) : reset d 0=1 := by
  ext z
  obtain ⟨a,b,rfl⟩ := state_surjective d z
  simp [reset_state,GibbsReflectedHistory.decay]

theorem reset_add (d : Data n) (s t : ℝ) : reset d (s+t)=(reset d s).comp (reset d t) := by
  ext z
  obtain ⟨a,b,rfl⟩ := state_surjective d z
  simp only [ContinuousLinearMap.comp_apply,reset_state]
  congr 1
  simp [GibbsReflectedHistory.decay,mul_add,Real.exp_add,Complex.ofReal_mul,mul_assoc]

theorem reset_zero_rate (d : Data n) (hγ : d.γ=0) (t : ℝ) : reset d t=1 := by
  ext z
  obtain ⟨a,b,rfl⟩ := state_surjective d z
  simp [reset_state,GibbsReflectedHistory.decay,hγ]

theorem reset_constant (d : Data n) (t : ℝ) (a : ℂ) : reset d t (state d a 0)=state d a 0 := by
  simp [reset_state]

theorem reset_centered (d : Data n) (t : ℝ) (b : ℂ) :
    reset d t (state d 0 b)=GibbsReflectedHistory.decay d.γ t • state d 0 b := by
  rw [reset_state,← state_smul]
  simp

theorem reset_centered_norm (d : Data n) (t : ℝ) (b : ℂ) :
    ‖reset d t (state d 0 b)‖=Real.exp (-d.γ*t)*‖state d 0 b‖ := by
  rw [reset_centered,norm_smul]
  rw [GibbsReflectedHistory.decay,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem state_nonzero (d : Data n) {a b : ℂ} (h : a≠0 ∨ b≠0) : state d a b≠0 := by
  intro hz
  rw [← state_zero d] at hz
  have he := state_injective d hz
  rcases h with ha|hb
  · exact ha he.1
  · exact hb he.2

theorem reset_centered_strict (d : Data n) (hγ : 0<d.γ) {t : ℝ} (ht : 0<t) {b : ℂ} (hb : b≠0) :
    ‖reset d t (state d 0 b)‖<‖state d 0 b‖ := by
  rw [reset_centered_norm]
  have he : Real.exp (-d.γ*t)<1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  exact mul_lt_of_lt_one_left (norm_pos_iff.mpr (state_nonzero d (Or.inr hb))) he

theorem state_norm_sq (d : Data n) (a b : ℂ) :
    ‖state d a b‖^2=Complex.normSq a+(1-meanZ d.β d.Δ^2)*Complex.normSq b := by
  rw [state,norm_mk_sq,pairing_self_real]
  simp only [Complex.ofReal_re,representative_amplitude,representative]

theorem reset_norm_le (d : Data n) (t : ℝ) (ht : 0≤t) (z : Reconstructed d) : ‖reset d t z‖≤‖z‖ := by
  obtain ⟨a,b,rfl⟩ := state_surjective d z
  have hn := state_norm_sq d a b
  have hr := state_norm_sq d a (GibbsReflectedHistory.decay d.γ t*b)
  rw [reset_state]
  simp only [Complex.normSq_mul,GibbsReflectedHistory.decay,Complex.normSq_ofReal] at hr
  have he := GibbsReset.exp_rate_le_one d.γ t d.rate_nonnegative ht
  have hep := Real.exp_pos (-d.γ*t)
  have hv := stationary_variance_pos d.β d.Δ
  have hb := Complex.normSq_nonneg b
  have hprod : 0≤(1-meanZ d.β d.Δ^2)*Complex.normSq b := mul_nonneg hv.le hb
  have hs : Real.exp (-d.γ*t)^2≤1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs hprod
  change ‖state d a ((Real.exp (-d.γ*t):ℂ)*b)‖≤_
  nlinarith [norm_nonneg (state d a b),norm_nonneg (state d a ((Real.exp (-d.γ*t):ℂ)*b))]

/-- Hilbert-space positivity transferred from the actual reset channel through the isometry. -/
theorem reset_positive (d : Data n) (t : ℝ) (ht : 0≤t) : (reset d t).IsPositive := by
  have h := GibbsReset.evolution_positive _ (weights_pos d.β d.Δ) (weights_sum d.β d.Δ) d.γ t d.rate_nonnegative ht
  constructor
  · intro x y
    change ⟪reset d t x,y⟫_ℂ=⟪x,reset d t y⟫_ℂ
    rw [← (embedding d).inner_map_map,← (embedding d).inner_map_map x (reset d t y)]
    rw [reset_intertwining d t ht,reset_intertwining d t ht]
    exact h.1 (embedding d x) (embedding d y)
  · intro x
    change 0≤(⟪reset d t x,x⟫_ℂ).re
    rw [← (embedding d).inner_map_map,reset_intertwining d t ht]
    exact h.2 (embedding d x)

theorem reset_selfAdjoint (d : Data n) (t : ℝ) (ht : 0≤t) : IsSelfAdjoint (reset d t) :=
  (reset_positive d t ht).isSelfAdjoint

theorem feature_none (d : Data n) : feature _ (positive d) none=state d 1 0 := by
  rw [feature,mk_coordinates]
  congr 1
  simp [amplitude,GibbsReflectedHistory.amplitude]

theorem feature_some (d : Data n) (i : Fin (n+1)) :
    feature _ (positive d) (some i)=state d 0 (GibbsReflectedHistory.decay d.γ (d.times i)) := by
  rw [feature,mk_coordinates]
  congr 1
  simp [amplitude,GibbsReflectedHistory.amplitude,Pi.single_apply]

theorem centered_matrix (d : Data n) : modeMatrix d 0 1=
    Matrix.diagonal (fun i => (sign i : ℂ))-(meanZ d.β d.Δ:ℂ) • (1 : Matrix Qubit Qubit ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j; simp [modeMatrix]
  · simp [modeMatrix,h]

theorem embedding_feature_none (d : Data n) : embedding d (feature _ (positive d) none)=
    observable (density_posDef _ (weights_pos d.β d.Δ)).posSemidef 1 := by
  rw [feature_none,embedding_state,mode_constant]

theorem embedding_feature_some (d : Data n) (i : Fin (n+1)) :
    embedding d (feature _ (positive d) (some i))=
      GibbsReflectedHistory.decay d.γ (d.times i) • mode d 0 1 := by
  rw [feature_some,embedding_state,← mode_smul]
  simp

theorem two_modes_orthogonal (d : Data n) : ⟪state d 1 0,state d 0 1⟫_ℂ=0 := by
  simp [state_inner]

theorem two_modes_nonzero (d : Data n) : state d 1 0≠0 ∧ state d 0 1≠0 :=
  ⟨state_nonzero d (Or.inl one_ne_zero),state_nonzero d (Or.inr one_ne_zero)⟩

theorem two_modes_span (d : Data n) (z : Reconstructed d) :
    ∃ a b : ℂ,z=a • state d 1 0+b • state d 0 1 := by
  obtain ⟨a,b,rfl⟩ := state_surjective d z
  refine ⟨a,b,?_⟩
  rw [← state_smul,← state_smul,← state_add]
  simp

theorem repeated_time_feature (d : Data n) (i j : Fin (n+1)) (h : d.times i=d.times j) :
    feature _ (positive d) (some i)=feature _ (positive d) (some j) := by
  rw [feature_some,feature_some,h]

theorem zero_rate_features (d : Data n) (hγ : d.γ=0) (i : Fin (n+1)) :
    feature _ (positive d) (some i)=state d 0 1 := by
  simp [feature_some,GibbsReflectedHistory.decay,hγ]

/-- Nonuniform Gibbs weights and the same four-event history used in the centered reconstruction. -/
def exampleData : Data 1 where
  β := 1
  Δ := 1
  γ := 1
  η := 0
  rate_nonnegative := by norm_num
  dephasing_nonnegative := by norm_num
  times := GibbsReflectedHistory.exampleTimes
  ordered := GibbsReflectedHistory.exampleTimes_monotone
  nonnegative := GibbsReflectedHistory.exampleTimes_nonnegative

theorem example_nonuniform : weights exampleData.β exampleData.Δ 1 < weights exampleData.β exampleData.Δ 0 :=
  nonuniform_equilibrium

theorem example_schedule : GibbsReflectedHistory.symmetricSchedule exampleData.times= ![-2,-1,1,2] :=
  GibbsReflectedHistory.example_schedule

theorem example_matrix : (reflection exampleData).kernel=
    fun i j => match i,j with
    | none,none => 1
    | none,some _ => 0
    | some _,none => 0
    | some i,some j =>
      let v : ℂ := ((1-meanZ 1 1^2:ℝ):ℂ)
      !![v*(Real.exp (-2):ℂ),v*(Real.exp (-3):ℂ);
         v*(Real.exp (-3):ℂ),v*(Real.exp (-4):ℂ)] i j := by
  ext i j
  cases i with
  | none => cases j <;> simp [kernel_none_none,kernel_none_some]
  | some i =>
    cases j with
    | none => exact kernel_some_none _ _
    | some j =>
      rw [kernel_some_some]
      exact congrFun (congrFun GibbsReflectedHistory.example_reflected_matrix i) j

def exampleNull : Option (Fin 2) → ℂ
  | none => 0
  | some i => GibbsReflectedHistory.exampleNull i

theorem example_null_nonzero : exampleNull≠0 := by
  intro h
  apply GibbsReflectedHistory.example_null_nonzero
  funext i
  exact congrFun h (some i)

theorem example_null : mk _ (positive exampleData) exampleNull=0 := by
  apply (null_iff _ _).mpr
  refine ⟨rfl,?_⟩
  exact (GibbsReflectedHistory.reflected_null_iff 1 1 1 0 (by norm_num) (by norm_num)
    GibbsReflectedHistory.exampleTimes GibbsReflectedHistory.exampleTimes_monotone
    GibbsReflectedHistory.exampleTimes_nonnegative GibbsReflectedHistory.exampleNull).mp
      GibbsReflectedHistory.example_null

theorem example_surviving_orthogonal_modes :
    feature _ (positive exampleData) none≠0 ∧ feature _ (positive exampleData) (some 0)≠0 ∧
    ⟪feature _ (positive exampleData) none,feature _ (positive exampleData) (some 0)⟫_ℂ=0 := by
  rw [feature_none,feature_some]
  refine ⟨(two_modes_nonzero _).1,state_nonzero _ (Or.inr (GibbsReflectedHistory.decay_ne_zero _ _)),?_⟩
  simp [state_inner]

theorem example_fixed_and_strict (t : ℝ) (ht : 0<t) :
    reset exampleData t (feature _ (positive exampleData) none)=feature _ (positive exampleData) none ∧
    ‖reset exampleData t (feature _ (positive exampleData) (some 0))‖<‖feature _ (positive exampleData) (some 0)‖ := by
  rw [feature_none,feature_some]
  exact ⟨reset_constant _ _ _,reset_centered_strict _ (by norm_num [exampleData]) ht
    (GibbsReflectedHistory.decay_ne_zero _ _)⟩

end SKEFTHawking.QuantumNetwork.GibbsUnitalHistory
