import SKEFTHawking.FiniteGibbsHistoryKernel

/-! Reflection of one actual finite computational Gibbs history. The reflected
centered covariance has a one-dimensional null quotient. No dynamics or full
field reconstruction is asserted. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsReflectedHistory
open Matrix GibbsHistoryKernel GibbsTwoTimeProcess FinitePositiveKernel
open scoped ComplexOrder InnerProductSpace

/-- Reversal of the chronological labels, including distinct duplicate-time labels. -/
def reverse {n : ℕ} (i : Fin (2*n+1+1)) : Fin (2*n+1+1) := ⟨2*n+1-i.val,by omega⟩

theorem reverse_involutive (n : ℕ) : Function.Involutive (@reverse n) := by
  intro i
  apply Fin.ext
  simp only [reverse]
  omega

/-- The positive half keeps its original increasing order. -/
def positive (n : ℕ) : Fin (n+1) ↪ Fin (2*n+1+1) where
  toFun i := ⟨n+1+i.val,by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

/-- One chronological schedule, negative reversed half followed by positive half. -/
def symmetricSchedule {n : ℕ} (τ : Fin (n+1) → ℝ) (i : Fin (2*n+1+1)) : ℝ :=
  if h : i.val ≤ n then -τ ⟨n-i.val,by omega⟩ else τ ⟨i.val-(n+1),by omega⟩

theorem positive_time {n : ℕ} (τ : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    symmetricSchedule τ (positive n i)=τ i := by
  simp only [symmetricSchedule,positive,Function.Embedding.coeFn_mk]
  split_ifs with h
  · omega
  · congr 1
    apply Fin.ext
    simp

theorem reflected_time {n : ℕ} (τ : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    symmetricSchedule τ (reverse (positive n i)) = -τ i := by
  simp only [symmetricSchedule,reverse,positive,Function.Embedding.coeFn_mk]
  split_ifs with h
  · congr 2
    apply Fin.ext
    dsimp
    omega
  · omega

theorem symmetric_monotone {n : ℕ} {τ : Fin (n+1) → ℝ}
    (hτ : Monotone τ) (h0 : ∀ i, 0 ≤ τ i) : Monotone (symmetricSchedule τ) := by
  intro i j hij
  have hv : i.val ≤ j.val := hij
  unfold symmetricSchedule
  split_ifs with hi hj hj
  · apply neg_le_neg
    apply hτ
    change n-j.val ≤ n-i.val
    omega
  · exact (neg_nonpos.mpr (h0 _)).trans (h0 _)
  · omega
  · apply hτ
    change i.val-(n+1) ≤ j.val-(n+1)
    omega

theorem reverse_time {n : ℕ} (τ : Fin (n+1) → ℝ) (i : Fin (2*n+1+1)) :
    symmetricSchedule τ (reverse i) = -symmetricSchedule τ i := by
  unfold symmetricSchedule reverse
  dsimp only
  split_ifs with h₁ h₂ h₂
  · omega
  · congr 2
    apply Fin.ext
    dsimp
    omega
  · rw [neg_neg]
    congr 1
    apply Fin.ext
    dsimp
    omega
  · omega

theorem sectors_disjoint {n : ℕ} (i j : Fin (n+1)) :
    reverse (positive n i) ≠ positive n j := by
  intro h
  have := congrArg Fin.val h
  simp only [reverse,positive,Function.Embedding.coeFn_mk] at this
  omega

/-- The ambient matrix is definitionally the covariance of the single doubled history. -/
def reflection (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) :
    ReflectionData (Fin (2*n+1+1)) (Fin (n+1)) where
  theta := reverse
  involutive := reverse_involutive n
  positiveSector := positive n
  covariance := finiteCovariance β Δ γ η hγ hη (2*n+1) (symmetricSchedule τ) (symmetric_monotone hτ h0)

theorem ambient_positive (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) :
    (reflection β Δ γ η hγ hη τ hτ h0).covariance.PosSemidef :=
  finiteCovariance_positive β Δ γ η hγ hη (2*n+1) (symmetricSchedule τ) (symmetric_monotone hτ h0)

theorem reflected_entry (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) (i j : Fin (n+1)) :
    (reflection β Δ γ η hγ hη τ hτ h0).kernel i j =
      (((1-meanZ β Δ^2)*Real.exp (-γ*(τ i+τ j)):ℝ):ℂ) := by
  simp only [ReflectionData.kernel,reflection,finiteCovariance_eq,reflected_time,positive_time]
  rw [abs_of_nonpos (by linarith [h0 i,h0 j])]
  congr 3
  ring

/-- The centered mode attached to a positive observation time. -/
def decay (γ t : ℝ) : ℂ := (Real.exp (-γ*t):ℝ)

theorem decay_ne_zero (γ t : ℝ) : decay γ t ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

theorem reflected_factor (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) (i j : Fin (n+1)) :
    (reflection β Δ γ η hγ hη τ hτ h0).kernel i j =
      ((1-meanZ β Δ^2:ℝ):ℂ)*decay γ (τ i)*decay γ (τ j) := by
  rw [reflected_entry,show -γ*(τ i+τ j)=(-γ*τ i)+(-γ*τ j) by ring,Real.exp_add]
  simp only [decay,Complex.ofReal_mul,mul_assoc]

/-- Direct Gram factorization proves reflection positivity independently of ambient PSD. -/
theorem reflected_positive (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) :
    (reflection β Δ γ η hγ hη τ hτ h0).kernel.PosSemidef := by
  let f : Fin (n+1) → ℂ := fun i => (Real.sqrt (1-meanZ β Δ^2):ℂ)*decay γ (τ i)
  have he : (reflection β Δ γ η hγ hη τ hτ h0).kernel=Matrix.vecMulVec (star f) f := by
    ext i j
    rw [reflected_factor]
    simp only [Matrix.vecMulVec,Pi.star_apply,f,decay,map_mul,Complex.star_def,Complex.conj_ofReal]
    have hs := Real.sq_sqrt (stationary_variance_pos β Δ).le
    have hc := congrArg Complex.ofReal hs
    push_cast at hc
    simp only [Matrix.of_apply]
    simp only [Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_one]
    linear_combination -((Real.exp (-γ*τ i):ℂ)*(Real.exp (-γ*τ j):ℂ))*hc
  rw [he]
  exact Matrix.posSemidef_vecMulVec_star_self f

/-- The amplitude functional exactly describes the reflected quotient. -/
def amplitude {n : ℕ} (γ : ℝ) (τ : Fin (n+1) → ℝ) (c : Fin (n+1) → ℂ) : ℂ :=
  ∑ i,c i*decay γ (τ i)

theorem reflected_pairing (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i)
    (c d : Fin (n+1) → ℂ) :
    pairing (reflection β Δ γ η hγ hη τ hτ h0).kernel c d =
      ((1-meanZ β Δ^2:ℝ):ℂ)*star (amplitude γ τ c)*amplitude γ τ d := by
  simp only [pairing,dotProduct,mulVec,Pi.star_apply,reflected_factor,amplitude,map_sum,map_mul,
    decay,Complex.star_def,Complex.conj_ofReal,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem reflected_null_iff (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i)
    (c : Fin (n+1) → ℂ) :
    mk _ (reflected_positive β Δ γ η hγ hη τ hτ h0) c=0 ↔ amplitude γ τ c=0 := by
  rw [mk_eq_zero_iff,reflected_pairing]
  have hv : ((1-meanZ β Δ^2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (stationary_variance_pos β Δ).ne'
  simp only [mul_eq_zero,hv,false_or,star_eq_zero,or_self]

theorem amplitude_single {n : ℕ} (γ : ℝ) (τ : Fin (n+1) → ℝ) (i : Fin (n+1)) (a : ℂ) :
    amplitude γ τ (Pi.single i a)=a*decay γ (τ i) := by
  simp [amplitude,Pi.single_apply]

theorem amplitude_sub {n : ℕ} (γ : ℝ) (τ : Fin (n+1) → ℝ) (c d : Fin (n+1) → ℂ) :
    amplitude γ τ (c-d)=amplitude γ τ c-amplitude γ τ d := by
  simp [amplitude,sub_mul,Finset.sum_sub_distrib]

/-- A point-mass feature survives for every time, including zero reset. -/
theorem feature_nonzero (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) (i : Fin (n+1)) :
    feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) i ≠ 0 := by
  intro he
  have hz := (reflected_null_iff β Δ γ η hγ hη τ hτ h0 (Pi.single i 1)).mp he
  rw [amplitude_single,one_mul] at hz
  exact decay_ne_zero γ (τ i) hz

/-- Every coefficient class is determined by its one complex amplitude. -/
theorem mk_amplitude (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i)
    (c : Fin (n+1) → ℂ) (j : Fin (n+1)) :
    mk _ (reflected_positive β Δ γ η hγ hη τ hτ h0) c =
      (amplitude γ τ c/decay γ (τ j)) • feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) j := by
  let a := amplitude γ τ c/decay γ (τ j)
  have he : (a • (Pi.single j 1 : Fin (n+1) → ℂ))=Pi.single j a := by
    ext i
    simp [Pi.single_apply]
  change mk _ _ c=a • mk _ _ (Pi.single j 1)
  erw [← (mkLinear _ (reflected_positive β Δ γ η hγ hη τ hτ h0)).map_smul a (Pi.single j 1)]
  change mk _ _ c=mk _ _ (a • Pi.single j 1)
  erw [he,mk_eq_mk_iff,reflected_pairing,amplitude_sub,amplitude_single]
  have hz : amplitude γ τ c-a*decay γ (τ j)=0 := by
    dsimp [a]
    field_simp [decay_ne_zero γ (τ j)]
    ring
  rw [hz]
  simp

theorem feature_proportional (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) (i j : Fin (n+1)) :
    feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) i =
      (decay γ (τ i)/decay γ (τ j)) • feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) j := by
  simpa only [feature,amplitude_single,one_mul] using mk_amplitude β Δ γ η hγ hη τ hτ h0 (Pi.single i 1) j

/-- One nonzero feature spans the entire reconstructed space, not just the displayed family. -/
theorem one_feature_spans (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i)
    (z : (reflection β Δ γ η hγ hη τ hτ h0).Reconstructed
      (reflected_positive β Δ γ η hγ hη τ hτ h0)) (j : Fin (n+1)) :
    ∃ a : ℂ,z=a • feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) j := by
  obtain ⟨c,rfl⟩ := mk_surjective _ (reflected_positive β Δ γ η hγ hη τ hτ h0) z
  exact ⟨_,mk_amplitude β Δ γ η hγ hη τ hτ h0 c j⟩

/-- A concrete linear equivalence establishes the exact dimension of reconstruction. -/
def scalarEquiv (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) :
    ℂ ≃ₗ[ℂ] (reflection β Δ γ η hγ hη τ hτ h0).Reconstructed
      (reflected_positive β Δ γ η hγ hη τ hτ h0) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ _
    (feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) 0))
    ⟨smul_left_injective ℂ (feature_nonzero β Δ γ η hγ hη τ hτ h0 0),by
      intro z
      obtain ⟨a,ha⟩ := one_feature_spans β Δ γ η hγ hη τ hτ h0 z 0
      exact ⟨a,ha.symm⟩⟩

theorem reconstructed_finrank (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) :
    Module.finrank ℂ ((reflection β Δ γ η hγ hη τ hτ h0).Reconstructed
      (reflected_positive β Δ γ η hγ hη τ hτ h0))=1 := by
  rw [← (scalarEquiv β Δ γ η hγ hη τ hτ h0).finrank_eq,Module.finrank_self]

/-- Reconstructed pairings are the reflected entries of the actual ambient history. -/
theorem inner_reflected (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) (i j : Fin (n+1)) :
    ⟪feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) i,
      feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) j⟫_ℂ =
      (reflection β Δ γ η hγ hη τ hτ h0).covariance (reverse (positive n i)) (positive n j) :=
  ReflectionData.inner_reconstructed _ _ i j

theorem zero_reset_entry (β Δ η : ℝ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) (i j : Fin (n+1)) :
    (reflection β Δ 0 η (by norm_num) hη τ hτ h0).kernel i j=((1-meanZ β Δ^2:ℝ):ℂ) := by
  rw [reflected_entry]
  simp

theorem zero_reset_null (β Δ η : ℝ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i) (c : Fin (n+1) → ℂ) :
    mk _ (reflected_positive β Δ 0 η (by norm_num) hη τ hτ h0) c=0 ↔ ∑ i,c i=0 := by
  rw [reflected_null_iff]
  simp [amplitude,decay]

theorem repeated_time_feature (β Δ γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    {n : ℕ} (τ : Fin (n+1) → ℝ) (hτ : Monotone τ) (h0 : ∀ i,0 ≤ τ i)
    (i j : Fin (n+1)) (hij : τ i=τ j) :
    feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) i=
      feature _ (reflected_positive β Δ γ η hγ hη τ hτ h0) j := by
  rw [feature_proportional β Δ γ η hγ hη τ hτ h0 i j,hij,div_self (decay_ne_zero _ _),one_smul]

/-- Two strictly positive sector times produce the four chronological labels -2,-1,1,2. -/
def exampleTimes (i : Fin 2) : ℝ := i.val+1

theorem exampleTimes_monotone : Monotone exampleTimes := by
  intro i j hij
  unfold exampleTimes
  have hv : (i.val:ℝ) ≤ j.val := by exact_mod_cast hij
  linarith

theorem exampleTimes_nonnegative (i : Fin 2) : 0 ≤ exampleTimes i := by
  unfold exampleTimes
  positivity

def exampleReflection : ReflectionData (Fin 4) (Fin 2) :=
  reflection 1 1 1 0 (by norm_num) (by norm_num) exampleTimes exampleTimes_monotone exampleTimes_nonnegative

theorem example_positive : exampleReflection.kernel.PosSemidef :=
  reflected_positive _ _ _ _ _ _ _ _ _

theorem example_schedule : symmetricSchedule exampleTimes= ![-2,-1,1,2] := by
  ext i
  fin_cases i <;> norm_num [symmetricSchedule,exampleTimes]

theorem example_reflected_matrix : exampleReflection.kernel=
    let v : ℂ := ((1-meanZ 1 1^2:ℝ):ℂ)
    !![v*(Real.exp (-2):ℂ),v*(Real.exp (-3):ℂ);
       v*(Real.exp (-3):ℂ),v*(Real.exp (-4):ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [exampleReflection,reflected_entry,exampleTimes]

def exampleNull : Fin 2 → ℂ := ![(Real.exp (-2):ℂ),-(Real.exp (-1):ℂ)]

theorem example_null_nonzero : exampleNull ≠ 0 := by
  intro h
  have hh := congrFun h 0
  have hn : (Real.exp (-2):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  apply hn
  simpa only [exampleNull,Matrix.cons_val_zero,Pi.zero_apply] using hh

theorem example_null : mk _ example_positive exampleNull=0 := by
  apply (reflected_null_iff 1 1 1 0 (by norm_num) (by norm_num)
    exampleTimes exampleTimes_monotone exampleTimes_nonnegative exampleNull).mpr
  change (∑ i : Fin 2,exampleNull i*decay 1 (exampleTimes i))=0
  rw [Fin.sum_univ_two]
  norm_num [exampleNull,exampleTimes,decay]
  ring

theorem example_survivor : feature _ example_positive 0 ≠ 0 :=
  feature_nonzero _ _ _ _ _ _ _ _ _ _

/-- Ordinary covariance of the very same four-observation history retains a positive minor. -/
theorem example_ordinary_minor :
    (exampleReflection.covariance 2 2).re*(exampleReflection.covariance 3 3).re-
      (exampleReflection.covariance 2 3).re*(exampleReflection.covariance 3 2).re=
        (1-meanZ 1 1^2)^2*(1-Real.exp (-2)) := by
  have he : Real.exp (-2)=Real.exp (-1)*Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  simp only [exampleReflection,reflection,finiteCovariance_eq,Complex.ofReal_re]
  norm_num [symmetricSchedule,exampleTimes]
  rw [he]
  ring

theorem example_ordinary_minor_positive :
    0 < (exampleReflection.covariance 2 2).re*(exampleReflection.covariance 3 3).re-
      (exampleReflection.covariance 2 3).re*(exampleReflection.covariance 3 2).re := by
  rw [example_ordinary_minor]
  exact mul_pos (sq_pos_of_pos (stationary_variance_pos 1 1))
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))

end SKEFTHawking.QuantumNetwork.GibbsReflectedHistory
