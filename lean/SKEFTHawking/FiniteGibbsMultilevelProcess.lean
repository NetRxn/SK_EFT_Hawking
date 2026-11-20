import SKEFTHawking.FiniteGibbsMultilevelReflection

/-! Actual finite computational reset histories and their product-observable transfer. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsMultilevelProcess
open Matrix FiniteInterventionProcess FinitePositiveKernel GibbsMultilevelReflection
open FinitePositiveKernel.DiagonalLindblad FinitePositiveKernel.GibbsObservable OpenSystems
open scoped ComplexOrder Kronecker InnerProductSpace
variable {d : ℕ}

theorem scalar_branch (R : Data d) (s : ℝ) (hs : 0 ≤ s)
    (c : ℂ) (i j : Fin d) :
    (step R.w R.positive R.normalized R.γ s R.rate_nonneg hs).branch (Fin d) Unit d j
      (joint (c • projector i))=
        joint ((c*(transition R.w R.γ s i j:ℂ)) • projector j) := by
  rw [step_branch,GibbsReset.time_state R.w (fun i => (R.positive i).le) _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one R.γ s R.rate_nonneg hs),instrument_branch]
  congr 2
  by_cases h : i=j
  · subst j
    simp [transition,projector,density,Matrix.trace_smul,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul]
    ring
  · simp [transition,projector,density,Matrix.trace_smul,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul,h,Ne.symm h]
    ring

def tripleTree (R : Data d) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) : Tree (Fin d) Unit d 3 :=
  .node (step R.w R.positive R.normalized R.γ 0 R.rate_nonneg le_rfl) (fun _ =>
    .node (step R.w R.positive R.normalized R.γ s R.rate_nonneg hs) (fun _ =>
      .node (step R.w R.positive R.normalized R.γ u R.rate_nonneg hu) (fun _ => .done)))

theorem triple_weight (R : Data d) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (i j k : Fin d) :
    weight (Fin d) Unit d (tripleTree R s u hs hu) (i,j,k,()) (joint (density R.w))=
      R.w i*transition R.w R.γ s i j*transition R.w R.γ u j k := by
  change ((step R.w R.positive R.normalized R.γ u R.rate_nonneg hu).branch (Fin d) Unit d k
    ((step R.w R.positive R.normalized R.γ s R.rate_nonneg hs).branch (Fin d) Unit d j
      ((step R.w R.positive R.normalized R.γ 0 R.rate_nonneg le_rfl).branch (Fin d) Unit d i
        (joint (density R.w))))).trace.re=_
  rw [first_collapse,scalar_branch,scalar_branch,joint_trace,Matrix.trace_smul,projector_trace]
  simp

theorem triple_middle (R : Data d) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (i k : Fin d) :
    (∑ j,weight (Fin d) Unit d (tripleTree R s u hs hu) (i,j,k,()) (joint (density R.w)))=
      R.w i*transition R.w R.γ (s+u) i k := by
  simp_rw [triple_weight,mul_assoc]
  rw [← Finset.mul_sum,transition_add R.w R.normalized]


def later {α : Type*} (f : ℕ → α) : ℕ → α := fun i => f (i+1)

def tailMass (R : Data d) : (n : ℕ) → (ℕ → ℝ) → Fin d → History d n → ℝ
  | 0,_,_,_ => 1
  | n+1,s,i,h => transition R.w R.γ (s 0) i h.1 * tailMass R n (later s) h.1 h.2

def tailTree (R : Data d) : (n : ℕ) → (s : ℕ → ℝ) → (∀ i,0 ≤ s i) → Tree (Fin d) Unit d n
  | 0,_,_ => .done
  | n+1,s,hs => .node (step R.w R.positive R.normalized R.γ (s 0) R.rate_nonneg (hs 0))
      (fun _ => tailTree R n (later s) (fun i => hs (i+1)))

def historyTree (R : Data d) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i) : Tree (Fin d) Unit d (n+1) :=
  .node (step R.w R.positive R.normalized R.γ 0 R.rate_nonneg le_rfl)
    (fun _ => tailTree R n s hs)

theorem tail_trace (R : Data d) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i)
    (i : Fin d) (h : History d n) (c : ℂ) :
    (run (Fin d) Unit d (tailTree R n s hs) h (joint (c • projector i))).trace=
      c*(tailMass R n s i h:ℂ) := by
  induction n generalizing s i c with
  | zero => simp [tailTree,run,joint_trace,Matrix.trace_smul,projector_trace,tailMass]
  | succ n ih =>
    change (run (Fin d) Unit d (tailTree R n (later s) _) h.2
      ((step R.w R.positive R.normalized R.γ (s 0) R.rate_nonneg (hs 0)).branch
        (Fin d) Unit d h.1 (joint (c • projector i)))).trace=_
    rw [scalar_branch,ih]
    simp [tailMass,mul_assoc]

def historyMass (R : Data d) (n : ℕ) (s : ℕ → ℝ) (h : History d (n+1)) : ℝ :=
  R.w h.1*tailMass R n s h.1 h.2

theorem history_weight (R : Data d) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i)
    (h : History d (n+1)) :
    weight (Fin d) Unit d (historyTree R n s hs) h (joint (density R.w))=historyMass R n s h := by
  change (run (Fin d) Unit d (tailTree R n s hs) h.2
    ((step R.w R.positive R.normalized R.γ 0 R.rate_nonneg le_rfl).branch
      (Fin d) Unit d h.1 (joint (density R.w)))).trace.re=_
  rw [first_collapse,tail_trace]
  simp [historyMass]

theorem history_probability (R : Data d) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i) :
    (∀ h,0 ≤ historyMass R n s h) ∧ (∑ h,historyMass R n s h)=1 := by
  simp_rw [← history_weight R n s hs]
  exact normalized_weights (Fin d) Unit d _ (initial_density R.w R.positive R.normalized)

def last : {n : ℕ} → Fin d → History d n → Fin d
  | 0,i,_ => i
  | _+1,_,h => last h.1 h.2

def elapsed : ℕ → (ℕ → ℝ) → ℝ
  | 0,_ => 0
  | n+1,s => s 0+elapsed n (later s)

theorem endpoint_expectation (R : Data d) (n : ℕ) (s : ℕ → ℝ) (i : Fin d) (F : Fin d → ℝ) :
    (∑ h,tailMass R n s i h*F (last i h))=
      ∑ j,transition R.w R.γ (elapsed n s) i j*F j := by
  induction n generalizing s i with
  | zero => simp [History,tailMass,last,elapsed,transition]
  | succ n ih =>
    change (∑ h : Fin d × History d n,_)=_
    rw [Fintype.sum_prod_type]
    simp only [tailMass,last,mul_assoc,← Finset.mul_sum]
    simp_rw [ih,Finset.mul_sum,← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,transition_add R.w R.normalized,elapsed]

/-- Includes the one-event case: the endpoint then is the already observed initial state. -/
theorem endpoint_marginal (R : Data d) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i) (i j : Fin d) :
    (∑ h : History d n,weight (Fin d) Unit d (historyTree R n s hs) (i,h)
      (joint (density R.w))*(if last i h=j then 1 else 0))=
      R.w i*transition R.w R.γ (elapsed n s) i j := by
  simp_rw [history_weight,historyMass,mul_assoc]
  rw [← Finset.mul_sum,endpoint_expectation R n s i (fun k => if k=j then 1 else 0)]
  simp

def probeProduct : (n : ℕ) → (ℕ → Fin d → ℂ) → History d n → ℂ
  | 0,_,_ => 1
  | n+1,F,h => F 0 h.1 * probeProduct n (later F) h.2

def transfer (R : Data d) : (n : ℕ) → (ℕ → ℝ) → (ℕ → Fin d → ℂ) → Fin d → ℂ
  | 0,_,_,_ => 1
  | n+1,s,F,i => ∑ j,(transition R.w R.γ (s 0) i j:ℂ)*
      (F 0 j*transfer R n (later s) (later F) j)

theorem tail_product (R : Data d) (n : ℕ) (s : ℕ → ℝ) (F : ℕ → Fin d → ℂ) (i : Fin d) :
    (∑ h,(tailMass R n s i h:ℂ)*probeProduct n F h)=transfer R n s F i := by
  induction n generalizing s F i with
  | zero => simp [History,tailMass,probeProduct,transfer]
  | succ n ih =>
    change (∑ h : Fin d × History d n,_)=_
    rw [Fintype.sum_prod_type]
    simp only [tailMass,probeProduct,Complex.ofReal_mul]
    simp_rw [show ∀ (a b c e : ℂ),a*b*(c*e)=a*(c*(b*e)) by intros; ring]
    simp only [← Finset.mul_sum,ih,transfer]

def productMoment (R : Data d) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i)
    (F : ℕ → Fin d → ℂ) : ℂ :=
  ∑ h,(weight (Fin d) Unit d (historyTree R n s hs) h (joint (density R.w)):ℂ)*probeProduct (n+1) F h

/-- Actual observed products obey the backward transition recursion. -/
theorem product_recursion (R : Data d) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i)
    (F : ℕ → Fin d → ℂ) :
    productMoment R n s hs F=∑ i,(R.w i:ℂ)*F 0 i*transfer R n s (later F) i := by
  unfold productMoment
  change (∑ h : Fin d × History d n,_)=_
  rw [Fintype.sum_prod_type]
  simp only [history_weight,historyMass,Complex.ofReal_mul,probeProduct]
  simp_rw [show ∀ (a b c e : ℂ),a*b*(c*e)=a*c*(b*e) by intros; ring]
  simp only [← Finset.mul_sum,tail_product]


def P (R : Data d) (s : ℝ) (F : Fin d → ℂ) (i : Fin d) : ℂ :=
  ∑ j,(transition R.w R.γ s i j:ℂ)*F j

def zeroData (R : Data d) : Data d := {R with t := 0, time_nonneg := le_rfl}

theorem P_modes (R : Data d) (s : ℝ) (hs : 0 ≤ s) (F : Fin d → ℂ) (i : Fin d) :
    P R s F i=mean R F+(Real.exp (-R.γ*s):ℂ)*(F i-mean R F) :=
  action_modes {R with t := s,time_nonneg := hs} F i

theorem action_zero (R : Data d) (F : Fin d → ℂ) : action (zeroData R) F=F := by
  funext i
  rw [action_modes]
  simp [zeroData]

def tripleMoment (R : Data d) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (F G H : Fin d → ℂ) : ℂ :=
  ∑ i,∑ j,∑ k,(weight (Fin d) Unit d (tripleTree R s u hs hu) (i,j,k,())
    (joint (density R.w)):ℂ)*F i*G j*H k

theorem triple_transfer (R : Data d) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (F G H : Fin d → ℂ) :
    tripleMoment R s u hs hu F G H=∑ i,(R.w i:ℂ)*F i*P R s (fun j => G j*P R u H j) i := by
  simp only [tripleMoment,triple_weight,Complex.ofReal_mul,P,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The first coefficient is conjugated because the actual history moment is unconjugated. -/
theorem triple_reconstruction (R : Data d) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (F G H : Fin d → ℂ) :
    tripleMoment R s u hs hu F G H=
      ⟪mk _ (positive (zeroData R)) (fun i => star (F i)),
        mk _ (positive (zeroData R)) (P R s (fun j => G j*P R u H j))⟫_ℂ := by
  rw [triple_transfer,inner_mk,pairing_action,action_zero,action_zero]
  simp [zeroData,mul_assoc]

/-- The transition action is the diagonal restriction of the actual Heisenberg channel. -/
theorem reset_diagonal (R : Data d) (s : ℝ) (hs : 0 ≤ s) (F : Fin d → ℂ) :
    Channel.heisenberg (GibbsReset.timeKraus R.w (Real.exp (-R.γ*s))) (diagonal F)=
      diagonal (P R s F) := by
  rw [GibbsReset.time_observable R.w (fun i => (R.positive i).le) _
    (Real.exp_pos _).le (GibbsReset.exp_rate_le_one R.γ s R.rate_nonneg hs)]
  ext i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq,Matrix.diagonal_mul_diagonal,Matrix.trace,Matrix.diag_diagonal,density,P_modes R s hs,mean]
    ring
  · simp [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_ne h,h]

theorem reset_embedding (R : Data d) (s : ℝ) (hs : 0 ≤ s) (F : Fin d → ℂ) :
    GibbsReset.evolution R.w R.positive R.normalized R.γ s R.rate_nonneg hs
      (embedding (zeroData R) (mk _ (positive (zeroData R)) F))=
    embedding (zeroData R) (mk _ (positive (zeroData R)) (P R s F)) := by
  rw [embedding_mk,embedding_mk,action_zero,action_zero]
  change GibbsReset.evolution R.w R.positive R.normalized R.γ s R.rate_nonneg hs
    (observable (density_posDef R.w R.positive).posSemidef (diagonal F))=_
  rw [GibbsReset.evolution,Channel.quotientChannel_observable,reset_diagonal R s hs]
  rfl

/-- Scalar old/new compatibility; no equality of independently constructed programs is needed. -/
theorem reflected_compatibility (R : Data d) (i j : Fin d) :
    (weight (Fin d) Unit d (historyTree R 1 (fun _ => 2*R.t) (fun _ => mul_nonneg (by norm_num) R.time_nonneg))
      (i,j,()) (joint (density R.w)):ℂ)=kernel R i j := by
  rw [history_weight,kernel_apply]
  simp [historyMass,tailMass]

theorem gibbs_history (E : Fin (d+1) → ℝ) (β γ : ℝ) (hγ : 0 ≤ γ)
    (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i) (h : History (d+1) (n+1)) :
    weight (Fin (d+1)) Unit (d+1) (historyTree (gibbsData E β γ 0 hγ le_rfl) n s hs) h
      (joint (FiniteGibbsClock.gibbs (density E) β))=
        historyMass (gibbsData E β γ 0 hγ le_rfl) n s h := by
  rw [← gibbs_initial E β γ 0 hγ le_rfl]
  exact history_weight _ _ _ _ _


def twoLags (s u : ℝ) (n : ℕ) : ℝ := if n=0 then s else u

theorem triple_history_weight (R : Data d) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (i j k : Fin d) :
    weight (Fin d) Unit d (historyTree R 2 (twoLags s u) (fun n => by
      unfold twoLags; split_ifs <;> assumption)) (i,j,k,()) (joint (density R.w))=
      weight (Fin d) Unit d (tripleTree R s u hs hu) (i,j,k,()) (joint (density R.w)) := by
  rw [history_weight,triple_weight]
  simp [historyMass,tailMass,twoLags,later,mul_assoc]

theorem P_zero (R : Data d) (F : Fin d → ℂ) : P R 0 F=F := by
  funext i
  rw [P_modes R 0 le_rfl]
  simp

theorem transition_zero_rate (R : Data d) (hγ : R.γ=0) (s : ℝ) (i j : Fin d) :
    transition R.w R.γ s i j=if i=j then 1 else 0 := by simp [transition,hγ]

def constantPath : {n : ℕ} → Fin d → History d n → Prop
  | 0,_,_ => True
  | _+1,i,h => i=h.1 ∧ constantPath h.1 h.2

instance constantPathDecidable : {n : ℕ} → (i : Fin d) → (h : History d n) → Decidable (constantPath i h)
  | 0,_,_ => inferInstanceAs (Decidable True)
  | _+1,i,h => @instDecidableAnd (i=h.1) (constantPath h.1 h.2) inferInstance (constantPathDecidable h.1 h.2)

theorem zero_rate_tail (R : Data d) (hγ : R.γ=0) (n : ℕ) (s : ℕ → ℝ) (i : Fin d) (h : History d n) :
    tailMass R n s i h=if constantPath i h then 1 else 0 := by
  induction n generalizing s i with
  | zero => simp [tailMass,constantPath]
  | succ n ih =>
    rw [tailMass,transition_zero_rate R hγ,ih]
    by_cases hi : i=h.1 <;> by_cases hh : constantPath h.1 h.2 <;> simp [constantPath,hi,hh]

theorem zero_rate_history (R : Data d) (hγ : R.γ=0) (n : ℕ) (s : ℕ → ℝ) (hs : ∀ i,0 ≤ s i)
    (h : History d (n+1)) :
    weight (Fin d) Unit d (historyTree R n s hs) h (joint (density R.w))=
      if constantPath h.1 h.2 then R.w h.1 else 0 := by
  rw [history_weight,historyMass,zero_rate_tail R hγ]
  split_ifs <;> simp

theorem repeated_time (R : Data d) (u : ℝ) (hu : 0 ≤ u) (F G H : Fin d → ℂ) :
    tripleMoment R 0 u le_rfl hu F G H=
      ∑ i,(R.w i:ℂ)*(F i*G i)*P R u H i := by
  rw [triple_transfer,P_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem three_branch :
    weight (Fin 3) Unit 3 (tripleTree three 1 1 (by norm_num) (by norm_num)) (0,1,2,())
      (joint (density three.w))=(1-Real.exp (-1))^2/36 := by
  rw [triple_weight]
  norm_num [three,transition,GibbsReset.threeWeights,
    show (1:Fin 3)≠2 by decide, show (0:Fin 3)≠2 by decide,
    show (![1/2,1/3,1/6] : Fin 3 → ℝ) 2=1/6 from rfl]
  ring

theorem three_branch_positive :
    0<weight (Fin 3) Unit 3 (tripleTree three 1 1 (by norm_num) (by norm_num)) (0,1,2,())
      (joint (density three.w)) := by
  rw [three_branch]
  have h : Real.exp (-1)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  positivity

theorem three_endpoint :
    (∑ j,weight (Fin 3) Unit 3 (tripleTree three 1 1 (by norm_num) (by norm_num)) (0,j,2,())
      (joint (density three.w)))=(1-Real.exp (-2))/12 := by
  rw [triple_middle]
  norm_num [three,transition,GibbsReset.threeWeights,
    show (1:Fin 3)≠2 by decide, show (0:Fin 3)≠2 by decide,
    show (![1/2,1/3,1/6] : Fin 3 → ℝ) 2=1/6 from rfl]
  ring

theorem modes_product : (fun i => firstMode i*secondMode i)=firstMode := by
  funext i
  fin_cases i <;> norm_num [firstMode,secondMode]

theorem P_smul (R : Data d) (s : ℝ) (c : ℂ) (F : Fin d → ℂ) :
    P R s (fun i => c*F i)=fun i => c*P R s F i := by
  funext i
  simp [P,Finset.mul_sum,mul_left_comm]

def threeRate (γ : ℝ) (hγ : 0 ≤ γ) : Data 3 := {three with γ := γ,rate_nonneg := hγ}

theorem higher_moment (γ s u : ℝ) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    tripleMoment (threeRate γ hγ) s u hs hu firstMode firstMode secondMode=
      (5/4:ℂ)*(Real.exp (-γ*(s+u)):ℂ) := by
  let R := threeRate γ hγ
  have hm1 : mean R firstMode=0 := three_means.1
  have hm2 : mean R secondMode=0 := three_means.2
  have hP1 : P R s firstMode=fun i => (Real.exp (-γ*s):ℂ)*firstMode i := by
    funext i; rw [P_modes R s hs,hm1]; simp [R,threeRate]
  have hP2 : P R u secondMode=fun i => (Real.exp (-γ*u):ℂ)*secondMode i := by
    funext i; rw [P_modes R u hu,hm2]; simp [R,threeRate]
  change tripleMoment R s u hs hu _ _ _=_
  rw [triple_transfer,hP2]
  have hi : (fun j => firstMode j*((Real.exp (-γ*u):ℂ)*secondMode j))=
      fun j => (Real.exp (-γ*u):ℂ)*firstMode j := by
    funext j
    have h := congrFun modes_product j
    linear_combination (Real.exp (-γ*u):ℂ)*h
  rw [hi,P_smul,hP1]
  have he : Real.exp (-γ*(s+u))=Real.exp (-γ*s)*Real.exp (-γ*u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he,Complex.ofReal_mul]
  norm_num [R,threeRate,three,firstMode,GibbsReset.threeWeights,Fin.sum_univ_succ]
  ring

theorem higher_positive :
    0<(tripleMoment three 1 1 (by norm_num) (by norm_num) firstMode firstMode secondMode).re := by
  have h := higher_moment 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  change tripleMoment three 1 1 _ _ _ _ _=_ at h
  rw [h]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  norm_num
  positivity

theorem higher_zero_rate (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    tripleMoment (threeRate 0 le_rfl) s u hs hu firstMode firstMode secondMode=5/4 := by
  rw [higher_moment]
  simp


def threeProbes (F G H : Fin d → ℂ) (n : ℕ) : Fin d → ℂ :=
  if n=0 then F else if n=1 then G else H

theorem triple_product_compatibility (R : Data d) (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (F G H : Fin d → ℂ) :
    productMoment R 2 (twoLags s u) (fun n => by unfold twoLags; split_ifs <;> assumption)
      (threeProbes F G H)=tripleMoment R s u hs hu F G H := by
  unfold productMoment
  simp_rw [history_weight]
  change (∑ h : Fin d × (Fin d × (Fin d × Unit)),_)=_
  simp only [Fintype.sum_prod_type,Fintype.sum_unique]
  simp only [historyMass,tailMass,probeProduct,threeProbes,later,twoLags,
    zero_add,one_ne_zero,ite_true,ite_false,Nat.reduceAdd,
    show (2:ℕ)≠0 by decide,show (2:ℕ)≠1 by decide,mul_one,Complex.ofReal_mul]
  unfold tripleMoment
  simp_rw [triple_weight,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end SKEFTHawking.QuantumNetwork.GibbsMultilevelProcess
