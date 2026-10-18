import SKEFTHawking.FiniteGibbsCylinderShift

/-! Reflected two-event computational histories of a faithful finite reset channel.
The reconstruction concerns diagonal observables at finite times. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsMultilevelReflection
open Matrix FiniteInterventionProcess FinitePositiveKernel
open FinitePositiveKernel.DiagonalLindblad OpenSystems
open scoped ComplexOrder Kronecker InnerProductSpace
variable {d : ℕ}

/-- One computational outcome projector. -/
def projector (a : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal (fun i => if i=a then 1 else 0)

theorem projector_adjoint (a : Fin d) : (projector a)ᴴ=projector a := by
  simp [projector]

theorem projector_square (a : Fin d) : projector a * projector a=projector a := by
  simp only [projector,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem projector_sum : ∑ a : Fin d,projector a=1 := by
  ext i j
  by_cases h : i=j
  · subst j; simp [projector,Matrix.sum_apply]
  · simp [projector,Matrix.sum_apply,h]

/-- A genuine normalized d-outcome instrument with one Kraus operator per outcome. -/
def instrument (d : ℕ) : FiniteInstrument (Fin d) d where
  count := 1
  operators a _ := projector a
  normalized := by simp only [Fin.sum_univ_one,projector_adjoint,projector_square]; exact projector_sum

theorem instrument_branch (a : Fin d) (X : Matrix (Fin d) (Fin d) ℂ) :
    (instrument d).branch a X=X a a • projector a := by
  simp only [FiniteInstrument.branch,instrument,krausMap,projector_adjoint]
  ext i j
  by_cases hi : i=a
  · subst i
    by_cases hj : j=a
    · subst j; simp [projector,Matrix.mul_diagonal,Matrix.diagonal_mul]
    · simp [projector,Matrix.mul_diagonal,Matrix.diagonal_mul,hj,Ne.symm hj]
  · simp [projector,Matrix.mul_diagonal,Matrix.diagonal_mul,hi,Matrix.diagonal_apply]

theorem projector_trace (a : Fin d) : (projector a).trace=1 := by simp [projector,Matrix.trace]

def joint (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Unit) (Fin d × Unit) ℂ := X ⊗ₖ 1

theorem joint_trace (X : Matrix (Fin d) (Fin d) ℂ) : (joint X).trace=X.trace := by
  rw [joint,Matrix.trace_kronecker]; simp [Matrix.trace]

theorem joint_kraus {m : ℕ} (V : Fin m → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    krausMap (fun k => joint (V k)) (joint X)=joint (krausMap V X) := by
  simp only [krausMap,joint,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul]
  exact sum_kronOne_general _

theorem joint_normalized {m : ℕ} (V : Fin m → Matrix (Fin d) (Fin d) ℂ) (hV : IsKrausChannel V) :
    IsKrausChannel (fun k => joint (V k)) := by
  unfold IsKrausChannel
  simp only [joint,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul]
  rw [sum_kronOne_general,show ∑ k,(V k)ᴴ*V k=1 from hV,Matrix.one_kronecker_one]

/-- Actual reset evolution followed by the computational instrument. -/
def step (w : Fin d → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
    (γ s : ℝ) (hγ : 0 ≤ γ) (hs : 0 ≤ s) : Step (Fin d) Unit d where
  count := _
  evolution k := joint (GibbsReset.timeKraus w (Real.exp (-γ*s)) k)
  normalized := joint_normalized _ (GibbsReset.time_normalized w (fun i => (hw i).le) hn _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ s hγ hs))
  instrument := instrument d

theorem step_branch (w : Fin d → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
    (γ s : ℝ) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (a : Fin d) (X : Matrix (Fin d) (Fin d) ℂ) :
    (step w hw hn γ s hγ hs).branch (Fin d) Unit d a (joint X)=
      joint ((instrument d).branch a (krausMap (GibbsReset.timeKraus w (Real.exp (-γ*s))) X)) := by
  change ((instrument d).lift Unit).branch a (krausMap (fun k => joint (GibbsReset.timeKraus w (Real.exp (-γ*s)) k)) (joint X))=_
  rw [joint_kraus]
  exact joint_kraus _ _

/-- First observation has zero evolution lag; the reflected partner has lag 2t. -/
def tree (w : Fin d → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) : Tree (Fin d) Unit d 2 :=
  .node (step w hw hn γ 0 hγ le_rfl) (fun _ =>
    .node (step w hw hn γ (2*t) hγ (by positivity)) (fun _ => .done))

def transition (w : Fin d → ℝ) (γ s : ℝ) (i j : Fin d) : ℝ :=
  Real.exp (-γ*s)*(if i=j then 1 else 0)+(1-Real.exp (-γ*s))*w j

theorem first_collapse (w : Fin d → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
    (γ : ℝ) (hγ : 0 ≤ γ) (a : Fin d) :
    (step w hw hn γ 0 hγ le_rfl).branch (Fin d) Unit d a (joint (density w))=
      joint ((w a:ℂ) • projector a) := by
  rw [step_branch,GibbsReset.time_stationary w (fun i => (hw i).le) hn _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ 0 hγ le_rfl),instrument_branch]
  simp [density]

theorem joint_weight (w : Fin d → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
    (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (i j : Fin d) :
    weight (Fin d) Unit d (tree w hw hn γ t hγ ht) (i,j,()) (joint (density w))=
      w i*transition w γ (2*t) i j := by
  change ((step w hw hn γ (2*t) hγ _).branch (Fin d) Unit d j
    ((step w hw hn γ 0 hγ le_rfl).branch (Fin d) Unit d i (joint (density w)))).trace.re=_
  rw [first_collapse,step_branch,GibbsReset.time_state w (fun i => (hw i).le) _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one γ (2*t) hγ (by positivity)),
    instrument_branch,joint_trace,Matrix.trace_smul,projector_trace]
  by_cases h : i=j
  · subst j
    simp [transition,projector,density,Matrix.trace_smul,Matrix.add_apply,Matrix.smul_apply,
      smul_eq_mul,Complex.mul_re,Complex.sub_re,Complex.exp_re]
    ring
  · simp [transition,projector,density,Matrix.trace_smul,h,Ne.symm h,
      Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.mul_re,Complex.sub_re,Complex.exp_re]
    ring


theorem initial_density (w : Fin d → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1) :
    IsDensityOperator (joint (density w)) := by
  refine ⟨(density_posDef w hw).posSemidef.kronecker Matrix.PosSemidef.one,?_⟩
  rw [joint_trace,GibbsReset.density_trace,hn]; simp

theorem step_actual (w : Fin d → ℝ) (hw : ∀ i,0 < w i) (hn : ∑ i,w i=1)
    (γ s : ℝ) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (X : Matrix (Fin d) (Fin d) ℂ) :
    krausMap (step w hw hn γ s hγ hs).evolution (joint X)=
      joint (lindbladPropagatorAction 0 (GibbsReset.jumps w γ) s X) := by
  change krausMap (fun k => joint (GibbsReset.timeKraus w (Real.exp (-γ*s)) k)) (joint X)=_
  rw [joint_kraus,GibbsReset.time_state_eq_propagator w (fun i => (hw i).le) hn γ s hγ hs]

theorem transition_sum (w : Fin d → ℝ) (hn : ∑ i,w i=1) (γ s : ℝ) (i : Fin d) :
    ∑ j,transition w γ s i j=1 := by
  simp [transition,Finset.sum_add_distrib,← Finset.mul_sum,hn]

theorem transition_balance (w : Fin d → ℝ) (γ s : ℝ) (i j : Fin d) :
    w i*transition w γ s i j=w j*transition w γ s j i := by
  by_cases h : i=j
  · subst j; rfl
  · simp [transition,h,Ne.symm h]; ring

theorem transition_add (w : Fin d → ℝ) (hn : ∑ i,w i=1) (γ s t : ℝ) (i j : Fin d) :
    ∑ x,transition w γ s i x*transition w γ t x j=transition w γ (s+t) i j := by
  simp only [transition,mul_add,add_mul,Finset.sum_add_distrib]
  simp [← Finset.mul_sum,← Finset.sum_mul,hn,Real.exp_add]
  split_ifs <;> ring

theorem central_factor (w : Fin d → ℝ) (hn : ∑ i,w i=1) (γ t : ℝ) (i j : Fin d) :
    ∑ x,w x*transition w γ t x i*transition w γ t x j=w i*transition w γ (2*t) i j := by
  simp_rw [transition_balance w γ t _ i, mul_assoc]
  rw [← Finset.mul_sum,transition_add w hn]
  congr 2; ring

/-- Faithfulness, normalization, and finite nonnegative rate/time are supplied explicitly. -/
structure Data (d : ℕ) where
  w : Fin d → ℝ
  positive : ∀ i,0 < w i
  normalized : ∑ i,w i=1
  γ : ℝ
  rate_nonneg : 0 ≤ γ
  t : ℝ
  time_nonneg : 0 ≤ t

/-- Entries are actual weights of the same two-event process. -/
def kernel (R : Data d) : Matrix (Fin d) (Fin d) ℂ := fun i j =>
  (weight (Fin d) Unit d (tree R.w R.positive R.normalized R.γ R.t R.rate_nonneg R.time_nonneg)
    (i,j,()) (joint (density R.w)) : ℂ)

theorem kernel_apply (R : Data d) (i j : Fin d) :
    kernel R i j=(R.w i*transition R.w R.γ (2*R.t) i j : ℝ) := by
  unfold kernel; rw [joint_weight]

def gramFactor (R : Data d) : Matrix (Fin d) (Fin d) ℂ :=
  fun x i => (Real.sqrt (R.w x)*transition R.w R.γ R.t x i : ℝ)

theorem kernel_gram (R : Data d) : kernel R=(gramFactor R)ᴴ*gramFactor R := by
  ext i j
  rw [kernel_apply,← central_factor R.w R.normalized R.γ R.t i j]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,gramFactor,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,
    ← Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have h := Real.mul_self_sqrt (R.positive x).le
  calc
    _ = (Real.sqrt (R.w x)*Real.sqrt (R.w x))*
        (transition R.w R.γ R.t x i*transition R.w R.γ R.t x j) := by rw [h]; ring
    _ = _ := by ring

theorem positive (R : Data d) : (kernel R).PosSemidef := by
  rw [kernel_gram]; exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The conditional expectation of a coefficient function at the latent midpoint. -/
def action (R : Data d) (F : Fin d → ℂ) (x : Fin d) : ℂ :=
  ∑ i,(transition R.w R.γ R.t x i : ℂ)*F i

def mean (R : Data d) (F : Fin d → ℂ) : ℂ := ∑ i,(R.w i:ℂ)*F i

theorem action_modes (R : Data d) (F : Fin d → ℂ) (x : Fin d) :
    action R F x=mean R F+(Real.exp (-R.γ*R.t):ℂ)*(F x-mean R F) := by
  simp only [action,transition,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_one,apply_ite Complex.ofReal,Complex.ofReal_zero]
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,mul_ite,mul_one,zero_mul,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [mul_assoc,← Finset.mul_sum,mean]
  ring


theorem factor_action (R : Data d) (F : Fin d → ℂ) (x : Fin d) :
    (gramFactor R *ᵥ F) x=(Real.sqrt (R.w x):ℂ)*action R F x := by
  simp only [Matrix.mulVec,dotProduct,gramFactor,Complex.ofReal_mul,action,mul_assoc,Finset.mul_sum]

theorem pairing_action (R : Data d) (F G : Fin d → ℂ) :
    pairing (kernel R) F G=∑ x,(R.w x:ℂ)*star (action R F x)*action R G x := by
  rw [pairing,kernel_gram,← Matrix.mulVec_mulVec,dotProduct_mulVec,← star_mulVec]
  simp only [dotProduct,Pi.star_apply,factor_action,map_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro x _
  have hs : (Real.sqrt (R.w x):ℂ)*(Real.sqrt (R.w x):ℂ)=(R.w x:ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (R.positive x).le]
  calc
    _ = ((Real.sqrt (R.w x):ℂ)*(Real.sqrt (R.w x):ℂ))*
      star (action R F x)*action R G x := by simp only [Complex.star_def]; ring
    _ = _ := by rw [hs]; rfl

theorem mean_affine (R : Data d) (F : Fin d → ℂ) (a b : ℂ) :
    mean R (fun x => a+b*F x)=a+b*mean R F := by
  have hn : ∑ x,(R.w x:ℂ)=1 := by exact_mod_cast R.normalized
  simp only [mean,mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,hn,one_mul]
  congr 1
  simp only [mul_left_comm (R.w _:ℂ) b,Finset.mul_sum]

theorem mean_action (R : Data d) (F : Fin d → ℂ) : mean R (action R F)=mean R F := by
  have he : action R F=fun x => (1-(Real.exp (-R.γ*R.t):ℂ))*mean R F+
      (Real.exp (-R.γ*R.t):ℂ)*F x := by funext x; rw [action_modes]; ring
  rw [he,mean_affine]; ring

/-- Explicit inverse at finite time; no limiting inverse is claimed. -/
def inverseAction (R : Data d) (F : Fin d → ℂ) (x : Fin d) : ℂ :=
  mean R F+(Real.exp (-R.γ*R.t):ℂ)⁻¹*(F x-mean R F)

theorem mean_inverse (R : Data d) (F : Fin d → ℂ) : mean R (inverseAction R F)=mean R F := by
  have he : inverseAction R F=fun x => (1-(Real.exp (-R.γ*R.t):ℂ)⁻¹)*mean R F+
      (Real.exp (-R.γ*R.t):ℂ)⁻¹*F x := by funext x; simp only [inverseAction]; ring
  rw [he,mean_affine]; ring

theorem action_inverse (R : Data d) (F : Fin d → ℂ) : action R (inverseAction R F)=F := by
  funext x
  rw [action_modes,mean_inverse,inverseAction]
  have h : (Real.exp (-R.γ*R.t):ℂ)≠0 := by exact_mod_cast (Real.exp_pos _).ne'
  field_simp
  ring

theorem inverse_action (R : Data d) (F : Fin d → ℂ) : inverseAction R (action R F)=F := by
  funext x
  rw [inverseAction,mean_action,action_modes]
  have h : (Real.exp (-R.γ*R.t):ℂ)≠0 := by exact_mod_cast (Real.exp_pos _).ne'
  field_simp
  ring

def actionLinear (R : Data d) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun := action R
  map_add' F G := by ext x; simp [action,mul_add,Finset.sum_add_distrib]
  map_smul' c F := by ext x; simp [action,Finset.mul_sum,mul_left_comm]

open GibbsObservable

def diagonalMap (R : Data d) : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun F := diagonal (action R F)
  map_add' F G := by
    change diagonal ((actionLinear R) (F+G))=_
    rw [(actionLinear R).map_add]; ext i j; by_cases h : i=j <;> simp [actionLinear,h]
  map_smul' c F := by
    change diagonal ((actionLinear R) (c • F))=_
    rw [(actionLinear R).map_smul]; exact Matrix.diagonal_smul _ _

def coefficientMap (R : Data d) : Coefficients (positive R) →ₗ[ℂ] WeightedSpace R.w R.positive :=
  (observableLinear (density_posDef R.w R.positive).posSemidef).comp (diagonalMap R)

theorem coefficientMap_apply (R : Data d) (F : Coefficients (positive R)) :
    coefficientMap R F=observable (density_posDef R.w R.positive).posSemidef (diagonal (action R F)) := rfl

theorem coefficientMap_inner (R : Data d) (F G : Coefficients (positive R)) :
    ⟪coefficientMap R F,coefficientMap R G⟫_ℂ=pairing (kernel R) F G := by
  rw [coefficientMap_apply,coefficientMap_apply,inner_observable,pairing_action]
  simp [density,Matrix.trace,mul_comm,mul_assoc]


theorem coefficientMap_injective (R : Data d) : Function.Injective (coefficientMap R) := by
  intro F G h
  rw [coefficientMap_apply,coefficientMap_apply] at h
  have hm := observable_injective (density_posDef R.w R.positive) h
  have ha : action R F=action R G := by
    funext i
    have hi := congrArg (fun X : Matrix (Fin d) (Fin d) ℂ => X i i) hm
    simpa using hi
  have hi := congrArg (inverseAction R) ha
  rw [inverse_action,inverse_action] at hi
  exact hi

theorem coefficientMap_null (R : Data d) : nullSpace (kernel R) (positive R) ≤ (coefficientMap R).ker := by
  intro F hF
  apply LinearMap.mem_ker.mpr
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [coefficientMap_inner]
  exact (mem_nullSpace_iff _ _ F).mp hF

abbrev Reconstructed (R : Data d) := Space (kernel R) (positive R)

/-- Cross-space quotient descent, justified by the actual history pairing. -/
def embeddingLinear (R : Data d) : Reconstructed R →ₗ[ℂ] WeightedSpace R.w R.positive :=
  ((nullSpace (kernel R) (positive R)).liftQ (coefficientMap R) (coefficientMap_null R)).comp
    (quotientEquiv (kernel R) (positive R)).symm.toLinearMap

theorem embeddingLinear_mk (R : Data d) (F : Coefficients (positive R)) :
    embeddingLinear R (mk _ (positive R) F)=coefficientMap R F := by
  rw [← quotientEquiv_mk (positive R) F]
  simp only [embeddingLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]

def embedding (R : Data d) : Reconstructed R →ₗᵢ[ℂ] WeightedSpace R.w R.positive :=
  (embeddingLinear R).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective _ (positive R) z
    obtain ⟨G,rfl⟩ := mk_surjective _ (positive R) w
    rw [embeddingLinear_mk,embeddingLinear_mk,inner_mk,coefficientMap_inner])

theorem embedding_mk (R : Data d) (F : Coefficients (positive R)) :
    embedding R (mk _ (positive R) F)=
      observable (density_posDef R.w R.positive).posSemidef (diagonal (action R F)) := embeddingLinear_mk R F

theorem null_iff (R : Data d) (F : Coefficients (positive R)) :
    pairing (kernel R) F F=0 ↔ F=0 := by
  constructor
  · intro h
    apply coefficientMap_injective R
    rw [(coefficientMap R).map_zero]
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [coefficientMap_inner,h]
  · rintro rfl
    change pairing (kernel R) (0 : Fin d → ℂ) 0=0
    simp [pairing]

theorem mk_injective (R : Data d) : Function.Injective (mk (kernel R) (positive R)) := by
  intro F G h
  apply coefficientMap_injective R
  have he := congrArg (embeddingLinear R) h
  simpa only [embeddingLinear_mk] using he

def coefficientEquiv (R : Data d) : Coefficients (positive R) ≃ₗ[ℂ] Reconstructed R :=
  LinearEquiv.ofBijective (mkLinear (kernel R) (positive R)) ⟨mk_injective R,mk_surjective _ _⟩

theorem reconstructed_finrank (R : Data d) : Module.finrank ℂ (Reconstructed R)=d := by
  rw [← (coefficientEquiv R).finrank_eq]
  change Module.finrank ℂ (Fin d → ℂ)=d
  simp

/-- The range is all diagonal observable classes, not all matrices. -/
theorem embedding_range (R : Data d) (z : WeightedSpace R.w R.positive) :
    (∃ x,embedding R x=z) ↔
      ∃ F : Fin d → ℂ,z=observable (density_posDef R.w R.positive).posSemidef (diagonal F) := by
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨F,rfl⟩ := mk_surjective _ (positive R) x
    exact ⟨action R F,embedding_mk R F⟩
  · rintro ⟨F,rfl⟩
    refine ⟨mk _ (positive R) (inverseAction R F),?_⟩
    rw [embedding_mk,action_inverse]

theorem feature_image (R : Data d) (i : Fin d) :
    embedding R (feature _ (positive R) i)=observable (density_posDef R.w R.positive).posSemidef
      (diagonal (fun x => (transition R.w R.γ R.t x i:ℂ))) := by
  rw [feature,embedding_mk]
  congr 2
  funext x
  simp [action,Pi.single_apply]


theorem level_positive (R : Data d) : 0<d := by
  by_contra h
  have hd : d=0 := by omega
  subst d
  have hn := R.normalized
  simp at hn

theorem zero_rate_kernel (R : Data d) (h : R.γ=0) : kernel R=density R.w := by
  ext i j
  rw [kernel_apply]
  by_cases hij : i=j
  · subst j; simp [transition,h,density]
  · simp [transition,h,density,hij]

theorem zero_time_kernel (R : Data d) (h : R.t=0) : kernel R=density R.w := by
  ext i j
  rw [kernel_apply]
  by_cases hij : i=j
  · subst j; simp [transition,h,density]
  · simp [transition,h,density,hij]

def gibbsData (E : Fin (d+1) → ℝ) (β γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) : Data (d+1) where
  w := GibbsReset.gibbsWeights E β
  positive := GibbsReset.gibbsWeights_pos E β
  normalized := GibbsReset.gibbsWeights_normalized E β
  γ := γ
  rate_nonneg := hγ
  t := t
  time_nonneg := ht

/-- The actual initial density is the existing finite Gibbs matrix. -/
theorem gibbs_initial (E : Fin (d+1) → ℝ) (β γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    density (gibbsData E β γ t hγ ht).w=FiniteGibbsClock.gibbs (density E) β := GibbsReset.density_gibbsWeights E β

theorem pairing_centered (R : Data d) (F G : Fin d → ℂ) (hF : mean R F=0) (hG : mean R G=0) :
    pairing (kernel R) F G=(Real.exp (-R.γ*R.t):ℂ)^2*
      ∑ i,(R.w i:ℂ)*star (F i)*G i := by
  rw [pairing_action,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [action_modes,action_modes,hF,hG]
  simp only [sub_zero,zero_add,map_mul,Complex.star_def,Complex.conj_ofReal]
  ring

theorem pairing_constant (R : Data d) : pairing (kernel R) (fun _ => 1) (fun _ => 1)=1 := by
  have ha : action R (fun _ => 1)=fun _ => 1 := by
    funext x
    simp only [action,mul_one,← Complex.ofReal_sum,transition_sum R.w R.normalized,Complex.ofReal_one]
  rw [pairing_action,ha]
  simpa using congrArg Complex.ofReal R.normalized

/-- Explicit nonuniform weights; this example is separate from an energy identification. -/
def three : Data 3 where
  w := GibbsReset.threeWeights
  positive := GibbsReset.threeWeights_pos
  normalized := GibbsReset.threeWeights_normalized
  γ := 1
  rate_nonneg := by norm_num
  t := 1
  time_nonneg := by norm_num

def firstMode : Fin 3 → ℂ := ![1,-3/2,0]
def secondMode : Fin 3 → ℂ := ![1,1,-5]

theorem three_means : mean three firstMode=0 ∧ mean three secondMode=0 := by
  norm_num [mean,three,firstMode,secondMode,GibbsReset.threeWeights,Fin.sum_univ_succ]

theorem three_transition : kernel three 0 1=((1-Real.exp (-2))/6 : ℝ) := by
  rw [kernel_apply]
  norm_num [three,transition,GibbsReset.threeWeights]
  ring

theorem three_transition_positive : 0<(kernel three 0 1).re := by
  rw [three_transition,Complex.ofReal_re]
  have h : Real.exp (-2)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

theorem three_modes :
    pairing (kernel three) firstMode secondMode=0 ∧
    pairing (kernel three) firstMode firstMode=(5/4:ℂ)*(Real.exp (-2):ℂ) ∧
    pairing (kernel three) secondMode secondMode=5*(Real.exp (-2):ℂ) := by
  rw [pairing_centered three _ _ three_means.1 three_means.2,
    pairing_centered three _ _ three_means.1 three_means.1,
    pairing_centered three _ _ three_means.2 three_means.2]
  have he : Complex.exp (-1)^2=Complex.exp (-2) := by
    rw [pow_two,← Complex.exp_add]; norm_num
  norm_num [three,firstMode,secondMode,GibbsReset.threeWeights,Fin.sum_univ_succ,map_ofNat,he]
  constructor <;> ring

theorem three_modes_positive :
    0<(pairing (kernel three) firstMode firstMode).re ∧
    0<(pairing (kernel three) secondMode secondMode).re := by
  rw [three_modes.2.1,three_modes.2.2]
  norm_num [Complex.mul_re,Complex.exp_re]
  positivity

theorem three_rank : Module.finrank ℂ (Reconstructed three)=3 := reconstructed_finrank three

/-- Fin-one paths and their unique outcomes are explicitly equivalent. -/
def pathEquiv : GibbsCylinderHistory.Path 0 ≃ Fin 2 where
  toFun u := u 0
  invFun i := fun _ => i
  left_inv u := by
    funext i
    have h : i=0 := by apply Fin.ext; omega
    change u 0=u i
    rw [h]
  right_inv i := rfl

def qubitData (D : GibbsUnitalHistory.Data 0) : Data 2 where
  w := GibbsRelaxationProcess.weights D.β D.Δ
  positive := GibbsRelaxationProcess.weights_pos D.β D.Δ
  normalized := GibbsRelaxationProcess.weights_sum D.β D.Δ
  γ := D.γ
  rate_nonneg := D.rate_nonnegative
  t := D.times 0
  time_nonneg := D.nonnegative 0

/-- Equality of actual kernels, with no assertion that their full program trees agree. -/
theorem qubit_kernel (D : GibbsUnitalHistory.Data 0) (u v : GibbsCylinderHistory.Path 0) :
    GibbsCylinderHistory.kernel D u v=kernel (qubitData D) (pathEquiv u) (pathEquiv v) := by
  rw [GibbsCylinderHistory.kernel,GibbsCylinderHistory.mass_split,kernel_apply]
  simp only [GibbsCylinderHistory.pathProduct,Fin.prod_univ_zero,mul_one,pathEquiv,Equiv.coe_fn_mk,qubitData]
  congr 1
  unfold transition GibbsHistoryKernel.transition
  simp only [eq_comm]
  ring

/-- Re-reflection shifts the central lag to 2(t+a), retaining both endpoint shifts. -/
theorem qubit_shift_kernel (D : GibbsUnitalHistory.Data 0) (a : ℝ) (ha : 0 ≤ a)
    (u v : GibbsCylinderHistory.Path 0) :
    GibbsCylinderHistory.kernel (GibbsCylinderShift.shiftData D a ha) u v=
      (GibbsRelaxationProcess.weights D.β D.Δ (u 0)*
        transition (GibbsRelaxationProcess.weights D.β D.Δ) D.γ (2*(D.times 0+a)) (u 0) (v 0):ℝ) := by
  rw [qubit_kernel,kernel_apply]
  rfl


theorem qubit_pairing (D : GibbsUnitalHistory.Data 0) (F G : Fin 2 → ℂ) :
    pairing (GibbsCylinderHistory.kernel D) (fun u => F (pathEquiv u)) (fun u => G (pathEquiv u))=
      pairing (kernel (qubitData D)) F G := by
  simp only [pairing,dotProduct,Matrix.mulVec,Pi.star_apply,qubit_kernel]
  calc
    _ = ∑ u,star (F (pathEquiv u))*(∑ j,kernel (qubitData D) (pathEquiv u) j*G j) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [pathEquiv.sum_comp (fun j => kernel (qubitData D) (pathEquiv u) j*G j)]
    _ = _ := pathEquiv.sum_comp (fun i => star (F i)*∑ j,kernel (qubitData D) i j*G j)


/-- Two independent centered reconstructed modes, beyond the one qubit centered mode. -/
theorem three_centered_independent (a b : ℂ) :
    a • mk (kernel three) (positive three) firstMode+
      b • mk (kernel three) (positive three) secondMode=0 ↔ a=0 ∧ b=0 := by
  change a • (mkLinear _ (positive three)) firstMode+
    b • (mkLinear _ (positive three)) secondMode=0 ↔ _
  rw [← LinearMap.map_smul,← LinearMap.map_smul,← LinearMap.map_add]
  change mk _ (positive three) (a • firstMode+b • secondMode)=0 ↔ _
  rw [mk_eq_zero_iff,null_iff]
  constructor
  · intro h
    have h2 := congrFun h (2 : Fin 3)
    have h0 := congrFun h (0 : Fin 3)
    change a*0+b*(-5)=0 at h2
    change a*1+b*1=0 at h0
    have hb : b=0 := by linear_combination -h2/5
    exact ⟨by linear_combination h0-hb,hb⟩
  · rintro ⟨rfl,rfl⟩
    change (0 : ℂ) • firstMode+(0 : ℂ) • secondMode=0
    simp

end SKEFTHawking.QuantumNetwork.GibbsMultilevelReflection
