import SKEFTHawking.FiniteGibbsMultilevelProcess

/-! Reflected cylinder pairings of actual finite faithful multilevel reset histories. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsMultilevelCylinder
open Matrix FiniteInterventionProcess FinitePositiveKernel GibbsMultilevelReflection GibbsMultilevelProcess
open FinitePositiveKernel.DiagonalLindblad FinitePositiveKernel.GibbsObservable OpenSystems
open scoped ComplexOrder Kronecker InnerProductSpace
variable {d : ℕ}

abbrev TwoPath (d : ℕ) := Fin d × Fin d

def fourLags (a b : ℝ) (i : ℕ) : ℝ := if i=1 then 2*a else b

theorem fourLags_nonnegative {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (i : ℕ) :
    0≤fourLags a b i := by unfold fourLags; split_ifs <;> positivity

/-- Negative outcomes are indexed outward: the first actual event is u.2. -/
def fourKernel (R : Data d) (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (u v : TwoPath d) : ℝ :=
  weight (Fin d) Unit d (historyTree R 3 (fourLags a b) (fourLags_nonnegative ha hb))
    (u.2,u.1,v.1,v.2,()) (joint (density R.w))

def fourHalf (R : Data d) (a b : ℝ) (c : Fin d) (u : TwoPath d) : ℝ :=
  transition R.w R.γ a c u.1*transition R.w R.γ b u.1 u.2

theorem fourKernel_weight (R : Data d) (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (u v : TwoPath d) :
    fourKernel R a b ha hb u v=R.w u.2*transition R.w R.γ b u.2 u.1*
      transition R.w R.γ (2*a) u.1 v.1*transition R.w R.γ b v.1 v.2 := by
  rw [fourKernel,history_weight]
  simp [historyMass,tailMass,later,fourLags,mul_assoc]

/-- The midpoint is an algebraic index; the process has exactly four events. -/
theorem fourKernel_factor (R : Data d) (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (u v : TwoPath d) :
    fourKernel R a b ha hb u v=∑ c,R.w c*fourHalf R a b c u*fourHalf R a b c v := by
  rw [fourKernel_weight,transition_balance R.w R.γ b u.2 u.1]
  calc
    _ = (R.w u.1*transition R.w R.γ (2*a) u.1 v.1)*
      transition R.w R.γ b u.1 u.2*transition R.w R.γ b v.1 v.2 := by ring
    _ = _ := by
      rw [← central_factor R.w R.normalized R.γ a u.1 v.1,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      unfold fourHalf
      ring

def fourExpectation (R : Data d) (a b : ℝ) (F : TwoPath d → ℂ) (c : Fin d) : ℂ :=
  ∑ u,(fourHalf R a b c u:ℂ)*F u

def fourPairing (R : Data d) (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (F G : TwoPath d → ℂ) : ℂ :=
  ∑ u,∑ v,(fourKernel R a b ha hb u v:ℂ)*star (F u)*G v

theorem fourPairing_gram (R : Data d) (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (F G : TwoPath d → ℂ) :
    fourPairing R a b ha hb F G=
      ∑ c,(R.w c:ℂ)*star (fourExpectation R a b F c)*fourExpectation R a b G c := by
  unfold fourPairing
  simp_rw [fourKernel_factor,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  have hsum (f : TwoPath d → TwoPath d → Fin d → ℂ) :
      (∑ u,∑ v,∑ c,f u v c)=∑ c,∑ u,∑ v,f u v c := by
    calc
      _ = ∑ u,∑ c,∑ v,f u v c := by
        apply Finset.sum_congr rfl
        intro u hu
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hsum]
  unfold fourExpectation
  simp only [map_sum,map_mul,Complex.star_def,Complex.conj_ofReal,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring


structure Schedule (n : ℕ) where
  times : Fin (n+1) → ℝ
  ordered : Monotone times
  nonnegative : ∀ i,0≤times i

def historyEquiv : (k : ℕ) → History d k ≃ (Fin k → Fin d)
  | 0 => { toFun := fun _ i => Fin.elim0 i
           invFun := fun _ => ()
           left_inv := fun h => by cases h; rfl
           right_inv := fun f => by funext i; exact Fin.elim0 i }
  | k+1 => (Equiv.prodCongr (Equiv.refl (Fin d)) (historyEquiv k)).trans
      (Fin.consEquiv (fun _ : Fin (k+1) => Fin d))


abbrev Path (d n : ℕ) := Fin (n+1) → Fin d

def split (n : ℕ) : (Fin (2*n+1+1) → Fin d) ≃ Path d n × Path d n where
  toFun f := (fun i => f (GibbsReflectedHistory.reverse (GibbsReflectedHistory.positive n i)),
              fun i => f (GibbsReflectedHistory.positive n i))
  invFun p j := if h : j.val ≤ n then p.1 ⟨n-j.val,by omega⟩ else p.2 ⟨j.val-(n+1),by omega⟩
  left_inv f := by
    funext j
    dsimp only
    split_ifs with h
    · congr 1; apply Fin.ext; simp [GibbsReflectedHistory.reverse,GibbsReflectedHistory.positive]; omega
    · congr 1; apply Fin.ext; simp [GibbsReflectedHistory.positive]; omega
  right_inv p := by
    apply Prod.ext <;> funext i
    · dsimp only
      simp only [GibbsReflectedHistory.reverse,GibbsReflectedHistory.positive,Function.Embedding.coeFn_mk]
      split_ifs with h
      · apply congrArg p.1; apply Fin.ext; change n-(2*n+1-(n+1+i.val))=i.val; omega
      · omega
    · dsimp only
      simp only [GibbsReflectedHistory.positive,Function.Embedding.coeFn_mk]
      split_ifs with h
      · omega
      · apply congrArg p.2; apply Fin.ext; change n+1+i.val-(n+1)=i.val; omega

def pairEquiv (n : ℕ) : History d (2*n+1+1) ≃ Path d n × Path d n :=
  (historyEquiv _).trans (split n)



theorem tailMass_product (R : Data d) (n : ℕ) (s : ℕ → ℝ) (i : Fin d) (h : History d n) :
    tailMass R n s i h=∏ j : Fin n,transition R.w R.γ (s j.val)
      (historyEquiv (n+1) (i,h) j.castSucc) (historyEquiv (n+1) (i,h) j.succ) := by
  induction n generalizing s i with
  | zero => simp [tailMass]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change transition R.w R.γ (s 0) i h.1*tailMass R n (later s) h.1 h.2=
      transition R.w R.γ (s 0) i h.1*(∏ j : Fin n,transition R.w R.γ (s (j.val+1))
        (historyEquiv (n+1) (h.1,h.2) j.castSucc) (historyEquiv (n+1) (h.1,h.2) j.succ))
    rw [ih]
    rfl

def lags {n : ℕ} (S : Schedule n) (i : ℕ) : ℝ :=
  if h : i<2*n+1 then GibbsReflectedHistory.symmetricSchedule S.times ⟨i+1,by omega⟩-
    GibbsReflectedHistory.symmetricSchedule S.times ⟨i,by omega⟩ else 0

theorem lags_nonnegative {n : ℕ} (S : Schedule n) (i : ℕ) : 0≤lags S i := by
  unfold lags
  split_ifs with h
  · exact sub_nonneg.mpr (GibbsReflectedHistory.symmetric_monotone S.ordered S.nonnegative (by change i ≤ i+1; omega))
  · exact le_rfl

def history {n : ℕ} (R : Data d) (S : Schedule n) : Tree (Fin d) Unit d (2*n+1+1) :=
  historyTree R (2*n+1) (lags S) (lags_nonnegative S)

def mass {n : ℕ} (R : Data d) (S : Schedule n) (h : History d (2*n+1+1)) : ℝ :=
  weight (Fin d) Unit d (history R S) h (joint (density R.w))

theorem mass_product {n : ℕ} (R : Data d) (S : Schedule n) (h : History d (2*n+1+1)) :
    mass R S h=R.w (historyEquiv _ h 0)*∏ i : Fin (2*n+1),
      transition R.w R.γ
        (GibbsReflectedHistory.symmetricSchedule S.times i.succ-
          GibbsReflectedHistory.symmetricSchedule S.times i.castSucc)
        (historyEquiv _ h i.castSucc) (historyEquiv _ h i.succ) := by
  rw [mass,history,history_weight,historyMass,tailMass_product]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [lags,i.isLt,dif_pos]
  rfl

/-- Forward and reversed edge products share the same outward labels. -/
def pathProduct (R : Data d) {n : ℕ} (τ : Fin (n+1) → ℝ) (u : Path d n) : ℝ :=
  ∏ i : Fin n,transition R.w R.γ (τ i.succ-τ i.castSucc) (u i.castSucc) (u i.succ)

def reverseProduct (R : Data d) {n : ℕ} (τ : Fin (n+1) → ℝ) (u : Path d n) : ℝ :=
  ∏ i : Fin n,transition R.w R.γ (τ i.succ-τ i.castSucc) (u i.succ) (u i.castSucc)

/-- Weighted reversal telescopes without dividing by any transition probability. -/
theorem path_reversal (R : Data d) (n : ℕ) (τ : Fin (n+1) → ℝ) (u : Path d n) :
    R.w (u (Fin.last n))*reverseProduct R τ u=
      R.w (u 0)*pathProduct R τ u := by
  induction n with
  | zero => simp [reverseProduct,pathProduct]
  | succ n ih =>
    let τ' : Fin (n+1) → ℝ := fun i => τ i.castSucc
    let u' : Path d n := fun i => u i.castSucc
    have hr : reverseProduct R τ u=reverseProduct R τ' u'*
        transition R.w R.γ (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
          (u (Fin.last (n+1))) (u (Fin.last n).castSucc) := by
      unfold reverseProduct
      rw [Fin.prod_univ_castSucc]
      rfl
    have hp : pathProduct R τ u=pathProduct R τ' u'*
        transition R.w R.γ (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
          (u (Fin.last n).castSucc) (u (Fin.last (n+1))) := by
      unfold pathProduct
      rw [Fin.prod_univ_castSucc]
      rfl
    rw [hr,hp]
    have hb := transition_balance R.w R.γ
      (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
      (u (Fin.last (n+1))) (u (Fin.last n).castSucc)
    calc
      _ = (R.w (u (Fin.last (n+1)))*
          transition R.w R.γ (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
            (u (Fin.last (n+1))) (u (Fin.last n).castSucc))*reverseProduct R τ' u' := by ring
      _ = (R.w (u' (Fin.last n))*reverseProduct R τ' u')*
          transition R.w R.γ (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
            (u (Fin.last n).castSucc) (u (Fin.last (n+1))) := by rw [hb]; ring
      _ = _ := by rw [ih τ' u']; simp [u',mul_assoc]


variable {n : ℕ}

theorem tuple_mass (R : Data d) (S : Schedule n) (u v : Path d n) :
    mass R S ((pairEquiv n).symm (u,v))=
      R.w ((split n).symm (u,v) 0)*
      ∏ i : Fin (2*n+1),transition R.w R.γ
        (GibbsReflectedHistory.symmetricSchedule S.times i.succ-
          GibbsReflectedHistory.symmetricSchedule S.times i.castSucc)
        ((split n).symm (u,v) i.castSucc) ((split n).symm (u,v) i.succ) := by
  rw [mass_product]
  have he : historyEquiv _ ((pairEquiv n).symm (u,v))=(split n).symm (u,v) := by
    change historyEquiv _ ((historyEquiv _).symm ((split n).symm (u,v)))=_
    exact Equiv.apply_symm_apply _ _
  rw [he]


def edge (R : Data d) (S : Schedule n) (u v : Path d n) (i : Fin (2*n+1)) : ℝ :=
  transition R.w R.γ
    (GibbsReflectedHistory.symmetricSchedule S.times i.succ-
      GibbsReflectedHistory.symmetricSchedule S.times i.castSucc)
    ((split n).symm (u,v) i.castSucc) ((split n).symm (u,v) i.succ)

theorem edge_negative (R : Data d) (S : Schedule n) (u v : Path d n) (i : Fin n) :
    edge R S u v ⟨i.val,by omega⟩=
      transition R.w R.γ
        (S.times i.rev.succ-S.times i.rev.castSucc) (u i.rev.succ) (u i.rev.castSucc) := by
  unfold edge GibbsReflectedHistory.symmetricSchedule split
  simp only [Equiv.coe_fn_symm_mk,Fin.val_succ,Fin.val_castSucc]
  simp only [show i.val ≤ n by omega,show i.val+1 ≤ n by omega,dif_pos]
  have ha : (⟨n-i.val,by omega⟩ : Fin (n+1))=i.rev.succ := by apply Fin.ext; simp [Fin.rev]; omega
  have hb : (⟨n-(i.val+1),by omega⟩ : Fin (n+1))=i.rev.castSucc := by apply Fin.ext; simp [Fin.rev]
  rw [ha,hb]
  congr 1
  ring

theorem edge_central (R : Data d) (S : Schedule n) (u v : Path d n) :
    edge R S u v ⟨n,by omega⟩=transition R.w R.γ (2*S.times 0) (u 0) (v 0) := by
  unfold edge GibbsReflectedHistory.symmetricSchedule split
  simp only [Equiv.coe_fn_symm_mk,Fin.val_succ,Fin.val_castSucc]
  simp only [show n ≤ n by omega,show ¬n+1 ≤ n by omega,dif_pos,dite_false,Nat.sub_self]
  change transition R.w R.γ (S.times 0- -S.times 0) (u 0) (v 0)=_
  congr 1
  ring

theorem edge_positive (R : Data d) (S : Schedule n) (u v : Path d n) (i : Fin n) :
    edge R S u v ⟨n+1+i.val,by omega⟩=
      transition R.w R.γ (S.times i.succ-S.times i.castSucc) (v i.castSucc) (v i.succ) := by
  unfold edge GibbsReflectedHistory.symmetricSchedule split
  simp only [Equiv.coe_fn_symm_mk,Fin.val_succ,Fin.val_castSucc]
  simp only [show ¬n+1+i.val ≤ n by omega,show ¬n+1+i.val+1 ≤ n by omega,dite_false]
  have ha : (⟨n+1+i.val-(n+1),by omega⟩ : Fin (n+1))=i.castSucc := by apply Fin.ext; dsimp; omega
  have hb : (⟨n+1+i.val+1-(n+1),by omega⟩ : Fin (n+1))=i.succ := by apply Fin.ext; dsimp; omega
  rw [ha,hb]

/-- The full tree law is split and reversed before the latent-state identity is used. -/
theorem mass_split (R : Data d) (S : Schedule n) (u v : Path d n) :
    mass R S ((pairEquiv n).symm (u,v))=
      R.w (u 0)*pathProduct R S.times u*
        transition R.w R.γ (2*S.times 0) (u 0) (v 0)*
        pathProduct R S.times v := by
  rw [tuple_mass]
  change R.w ((split n).symm (u,v) 0)*(∏ i,edge R S u v i)=_
  have h0 : (split n).symm (u,v) 0=u (Fin.last n) := by simp [split]; rfl
  rw [h0,GibbsCylinderHistory.product_split]
  simp_rw [edge_negative,edge_central,edge_positive]
  have hr := Equiv.prod_comp Fin.revPerm (fun i : Fin n =>
    transition R.w R.γ (S.times i.succ-S.times i.castSucc) (u i.succ) (u i.castSucc))
  change (∏ i : Fin n,transition R.w R.γ (S.times i.rev.succ-S.times i.rev.castSucc) (u i.rev.succ) (u i.rev.castSucc))=reverseProduct R S.times u at hr
  rw [hr]
  change _=R.w (u 0)*pathProduct R S.times u*_*pathProduct R S.times v
  rw [← mul_assoc,← mul_assoc,path_reversal]
  rfl

/-- Conditional path law through a latent finite-state index. -/
def conditional (R : Data d) (S : Schedule n) (x : Fin d) (u : Path d n) : ℝ :=
  transition R.w R.γ (S.times 0) x (u 0)*pathProduct R S.times u

theorem mass_factor (R : Data d) (S : Schedule n) (u v : Path d n) :
    mass R S ((pairEquiv n).symm (u,v))=
      ∑ x,R.w x*conditional R S x u*conditional R S x v := by
  rw [mass_split]
  calc
    _ = (R.w (u 0)*transition R.w R.γ (2*S.times 0) (u 0) (v 0))*
        pathProduct R S.times u*pathProduct R S.times v := by ring
    _ = _ := by
      rw [← central_factor R.w R.normalized R.γ,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      unfold conditional
      ring


/-- Arbitrary complex functions on the finite positive history. -/
def expectation (R : Data d) (S : Schedule n) (F : Path d n → ℂ) (x : Fin d) : ℂ :=
  ∑ u,(conditional R S x u:ℂ)*F u

def cylinderPairing (R : Data d) (S : Schedule n) (F G : Path d n → ℂ) : ℂ :=
  ∑ h,(mass R S h:ℂ)*star (F ((pairEquiv n h).1))*G ((pairEquiv n h).2)

/-- Indicator cylinders index a finite kernel containing all complex cylinder functions. -/
def kernel (R : Data d) (S : Schedule n) : Matrix (Path d n) (Path d n) ℂ :=
  fun u v => (mass R S ((pairEquiv n).symm (u,v)):ℂ)

theorem kernel_factor (R : Data d) (S : Schedule n) (u v : Path d n) :
    kernel R S u v=∑ x,(R.w x:ℂ)*(conditional R S x u:ℂ)*(conditional R S x v:ℂ) := by
  simp only [kernel,mass_factor,Complex.ofReal_sum,Complex.ofReal_mul]

theorem pairing_actual (R : Data d) (S : Schedule n) (F G : Path d n → ℂ) :
    pairing (kernel R S) F G=cylinderPairing R S F G := by
  have he := Equiv.sum_comp (pairEquiv n).symm
    (fun h => (mass R S h:ℂ)*star (F ((pairEquiv n h).1))*G ((pairEquiv n h).2))
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type] at he
  unfold cylinderPairing
  rw [← he]
  simp only [pairing,dotProduct,mulVec,Finset.mul_sum,kernel]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.star_apply,Complex.star_def]
  ring

theorem pairing_factor (R : Data d) (S : Schedule n) (F G : Path d n → ℂ) :
    pairing (kernel R S) F G=
      ∑ x,(R.w x:ℂ)*star (expectation R S F x)*expectation R S G x := by
  simp only [pairing,dotProduct,mulVec,kernel_factor,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [expectation,star_sum,map_mul,Complex.star_def,Complex.conj_ofReal,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.star_apply,Complex.star_def]
  ring

theorem cylinder_factor (R : Data d) (S : Schedule n) (F G : Path d n → ℂ) :
    cylinderPairing R S F G=
      ∑ x,(R.w x:ℂ)*star (expectation R S F x)*expectation R S G x := by
  rw [← pairing_actual,pairing_factor]

def gram (R : Data d) (S : Schedule n) : Matrix (Fin d) (Path d n) ℂ :=
  fun x u => (Real.sqrt (R.w x):ℂ)*(conditional R S x u:ℂ)

theorem kernel_gram (R : Data d) (S : Schedule n) : kernel R S=(gram R S)ᴴ*gram R S := by
  ext u v
  rw [kernel_factor]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,gram,map_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro x _
  have hs : (Real.sqrt (R.w x):ℂ)^2=(R.w x:ℂ) := by
    exact_mod_cast Real.sq_sqrt (R.positive x).le
  linear_combination -(conditional R S x u:ℂ)*(conditional R S x v:ℂ)*hs

theorem positive (R : Data d) (S : Schedule n) : (kernel R S).PosSemidef := by
  rw [kernel_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

abbrev Reconstructed (R : Data d) (S : Schedule n) := Space (kernel R S) (positive R S)



def expectationLinear (R : Data d) (S : Schedule n) : (Path d n → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun := expectation R S
  map_add' F G := by ext x; simp [expectation,mul_add,Finset.sum_add_distrib]
  map_smul' c F := by ext x; simp [expectation,Finset.mul_sum,mul_left_comm]

def diagonalMap (R : Data d) (S : Schedule n) : (Path d n → ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun F := diagonal (expectation R S F)
  map_add' F G := by
    change diagonal ((expectationLinear R S) (F+G))=_
    rw [(expectationLinear R S).map_add]; ext i j; by_cases h : i=j <;> simp [expectationLinear,h]
  map_smul' c F := by
    change diagonal ((expectationLinear R S) (c • F))=_
    rw [(expectationLinear R S).map_smul]; exact Matrix.diagonal_smul _ _

def coefficientMap (R : Data d) (S : Schedule n) : Coefficients (positive R S) →ₗ[ℂ] WeightedSpace R.w R.positive :=
  (observableLinear (density_posDef R.w R.positive).posSemidef).comp (diagonalMap R S)

theorem coefficientMap_apply (R : Data d) (S : Schedule n) (F : Coefficients (positive R S)) :
    coefficientMap R S F=observable (density_posDef R.w R.positive).posSemidef (diagonal (expectation R S F)) := rfl

theorem coefficientMap_inner (R : Data d) (S : Schedule n) (F G : Coefficients (positive R S)) :
    ⟪coefficientMap R S F,coefficientMap R S G⟫_ℂ=pairing (kernel R S) F G := by
  rw [coefficientMap_apply,coefficientMap_apply,inner_observable,pairing_factor]
  simp [density,Matrix.trace,mul_comm,mul_assoc]


theorem coefficientMap_null (R : Data d) (S : Schedule n) : nullSpace (kernel R S) (positive R S) ≤ (coefficientMap R S).ker := by
  intro F hF
  apply LinearMap.mem_ker.mpr
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [coefficientMap_inner]
  exact (mem_nullSpace_iff _ _ F).mp hF



/-- Cross-space quotient descent, justified by the actual history pairing. -/
def embeddingLinear (R : Data d) (S : Schedule n) : Reconstructed R S →ₗ[ℂ] WeightedSpace R.w R.positive :=
  ((nullSpace (kernel R S) (positive R S)).liftQ (coefficientMap R S) (coefficientMap_null R S)).comp
    (quotientEquiv (kernel R S) (positive R S)).symm.toLinearMap

theorem embeddingLinear_mk (R : Data d) (S : Schedule n) (F : Coefficients (positive R S)) :
    embeddingLinear R S (mk _ (positive R S) F)=coefficientMap R S F := by
  rw [← quotientEquiv_mk (positive R S) F]
  simp only [embeddingLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]

def embedding (R : Data d) (S : Schedule n) : Reconstructed R S →ₗᵢ[ℂ] WeightedSpace R.w R.positive :=
  (embeddingLinear R S).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective _ (positive R S) z
    obtain ⟨G,rfl⟩ := mk_surjective _ (positive R S) w
    rw [embeddingLinear_mk,embeddingLinear_mk,inner_mk,coefficientMap_inner])

theorem embedding_mk (R : Data d) (S : Schedule n) (F : Coefficients (positive R S)) :
    embedding R S (mk _ (positive R S) F)=
      observable (density_posDef R.w R.positive).posSemidef (diagonal (expectation R S F)) := embeddingLinear_mk R S F



/-- The null directions are precisely the cylinders with zero conditional value at every state. -/
theorem null_iff (R : Data d) (S : Schedule n) (F : Path d n → ℂ) :
    mk (kernel R S) (positive R S) F=0 ↔ expectation R S F=0 := by
  constructor
  · intro h
    have he := congrArg (embedding R S) h
    rw [embedding_mk,map_zero] at he
    have hm : diagonal (expectation R S F)=0 := by
      apply observable_injective (density_posDef R.w R.positive)
      have hz : observable (density_posDef R.w R.positive).posSemidef (0 : Matrix (Fin d) (Fin d) ℂ)=0 := by
        change (mkLinear _ _) 0=0
        exact map_zero _
      rw [hz]
      exact he
    funext i
    have hi := congrArg (fun X : Matrix (Fin d) (Fin d) ℂ => X i i) hm
    simpa using hi
  · intro h
    apply (embedding R S).injective
    rw [embedding_mk,map_zero,h]
    have hz : diagonal (0 : Fin d → ℂ)=(0 : Matrix (Fin d) (Fin d) ℂ) := Matrix.diagonal_zero
    rw [hz]
    change (mkLinear _ _) 0=0
    exact map_zero _

def gaps {n : ℕ} (τ : Fin (n+1) → ℝ) (k : ℕ) : ℝ :=
  if h : k<n then τ ⟨k+1,by omega⟩-τ ⟨k,by omega⟩ else 0

theorem historyEquiv_cons (k : ℕ) (i : Fin d) (h : History d k) :
    historyEquiv (k+1) (i,h)=Fin.cons i (historyEquiv k h) := rfl

theorem pathProduct_tail (R : Data d) (τ : Fin (n+1) → ℝ) (u : Path d n) :
    pathProduct R τ u=tailMass R n (gaps τ) (u 0)
      ((historyEquiv n).symm (fun j => u j.succ)) := by
  rw [tailMass_product]
  have he : historyEquiv (n+1) (u 0,(historyEquiv n).symm (fun j => u j.succ))=u := by
    rw [historyEquiv_cons,Equiv.apply_symm_apply]
    exact Fin.cons_self_tail u
  rw [he]
  unfold pathProduct
  apply Finset.prod_congr rfl
  intro i hi
  simp only [gaps,i.isLt,dif_pos]
  rfl

theorem tailMass_sum (R : Data d) (k : ℕ) (s : ℕ → ℝ) (i : Fin d) :
    ∑ h : History d k,tailMass R k s i h=1 := by
  induction k generalizing s i with
  | zero => change (∑ _ : Unit,(1 : ℝ))=1; simp
  | succ k ih =>
    change (∑ h : Fin d × History d k,_)=1
    rw [Fintype.sum_prod_type]
    simp only [tailMass,← Finset.mul_sum,ih,mul_one]
    exact transition_sum R.w R.normalized R.γ (s 0) i



theorem pathProduct_history (R : Data d) (τ : Fin (n+1) → ℝ) (i : Fin d) (h : History d n) :
    pathProduct R τ (historyEquiv (n+1) (i,h))=tailMass R n (gaps τ) i h := by
  rw [pathProduct_tail,historyEquiv_cons]
  simp only [Fin.cons_zero,Fin.cons_succ,Equiv.symm_apply_apply]

def firstData (R : Data d) (S : Schedule n) : Data d :=
  { R with t := S.times 0, time_nonneg := S.nonnegative 0 }

def firstProbe (A : Fin d → ℂ) (u : Path d n) : ℂ := A (u 0)

theorem expectation_first (R : Data d) (S : Schedule n) (A : Fin d → ℂ) :
    expectation R S (firstProbe A)=action (firstData R S) A := by
  funext c
  unfold expectation
  rw [← Equiv.sum_comp (historyEquiv (n+1))]
  change (∑ h : Fin d × History d n,_)=_
  rw [Fintype.sum_prod_type]
  unfold conditional firstProbe
  simp only [pathProduct_history]
  simp only [historyEquiv_cons,Fin.cons_zero,Complex.ofReal_mul]
  simp_rw [mul_right_comm _ _ (A _),← Finset.mul_sum,← Complex.ofReal_sum,tailMass_sum]
  simp only [Complex.ofReal_one,mul_one]
  rfl

/-- An explicit first-coordinate right inverse; no positivity of transition entries is needed. -/
def representative (R : Data d) (S : Schedule n) (A : Fin d → ℂ) : Path d n → ℂ :=
  firstProbe (inverseAction (firstData R S) A)

theorem expectation_representative (R : Data d) (S : Schedule n) (A : Fin d → ℂ) :
    expectation R S (representative R S A)=A := by
  rw [representative,expectation_first,action_inverse]



theorem expectation_null (R : Data d) (S : Schedule n) :
    nullSpace (kernel R S) (positive R S) ≤ (expectationLinear R S).ker := by
  intro F hF
  change expectation R S F=0
  apply (null_iff R S F).mp
  rw [mk_eq_zero_iff]
  exact (mem_nullSpace_iff _ _ F).mp hF

def coordinates (R : Data d) (S : Schedule n) : Reconstructed R S →ₗ[ℂ] (Fin d → ℂ) :=
  ((nullSpace (kernel R S) (positive R S)).liftQ (expectationLinear R S) (expectation_null R S)).comp
    (quotientEquiv (kernel R S) (positive R S)).symm.toLinearMap

theorem coordinates_mk (R : Data d) (S : Schedule n) (F : Path d n → ℂ) :
    coordinates R S (mk _ (positive R S) F)=expectation R S F := by
  rw [← quotientEquiv_mk (positive R S) F]
  simp only [coordinates,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
    Submodule.liftQ_apply]
  rfl

theorem coordinates_bijective (R : Data d) (S : Schedule n) : Function.Bijective (coordinates R S) := by
  constructor
  · intro x y h
    obtain ⟨F,rfl⟩ := mk_surjective _ (positive R S) x
    obtain ⟨G,rfl⟩ := mk_surjective _ (positive R S) y
    rw [coordinates_mk,coordinates_mk] at h
    apply (embedding R S).injective
    rw [embedding_mk,embedding_mk,h]
  · intro A
    exact ⟨mk _ (positive R S) (representative R S A),by rw [coordinates_mk,expectation_representative]⟩

def coordinateEquiv (R : Data d) (S : Schedule n) : Reconstructed R S ≃ₗ[ℂ] (Fin d → ℂ) :=
  LinearEquiv.ofBijective (coordinates R S) (coordinates_bijective R S)

theorem reconstructed_finrank (R : Data d) (S : Schedule n) : Module.finrank ℂ (Reconstructed R S)=d := by
  rw [(coordinateEquiv R S).finrank_eq]
  simp

/-- All diagonal classes occur, even at zero rate and repeated times. -/
theorem embedding_range (R : Data d) (S : Schedule n) (z : WeightedSpace R.w R.positive) :
    (∃ x,embedding R S x=z) ↔
      ∃ A : Fin d → ℂ,z=observable (density_posDef R.w R.positive).posSemidef (diagonal A) := by
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨F,rfl⟩ := mk_surjective _ (positive R S) x
    exact ⟨expectation R S F,embedding_mk R S F⟩
  · rintro ⟨A,rfl⟩
    refine ⟨mk _ (positive R S) (representative R S A),?_⟩
    rw [embedding_mk,expectation_representative]



/-- The existing product recursion evaluates the actual positive-half cylinder. -/
def productProbe (F : ℕ → Fin d → ℂ) (u : Path d n) : ℂ :=
  F 0 (u 0)*probeProduct n (later F) ((historyEquiv n).symm (fun i => u i.succ))

theorem expectation_product (R : Data d) (S : Schedule n) (F : ℕ → Fin d → ℂ) :
    expectation R S (productProbe F)=
      P R (S.times 0) (fun i => F 0 i*transfer R n (gaps S.times) (later F) i) := by
  funext c
  unfold expectation
  rw [← Equiv.sum_comp (historyEquiv (n+1))]
  change (∑ h : Fin d × History d n,_)=_
  rw [Fintype.sum_prod_type]
  unfold conditional productProbe
  simp only [pathProduct_history]
  simp only [historyEquiv_cons,Fin.cons_zero,Fin.cons_succ,Equiv.symm_apply_apply,Complex.ofReal_mul]
  change (∑ i,∑ h,(transition R.w R.γ (S.times 0) c i:ℂ)*
    (tailMass R n (gaps S.times) i h:ℂ)*(F 0 i*probeProduct n (later F) h))=_
  have he (i : Fin d) (h : History d n) :
      (transition R.w R.γ (S.times 0) c i:ℂ)*(tailMass R n (gaps S.times) i h:ℂ)*
        (F 0 i*probeProduct n (later F) h)=
      (transition R.w R.γ (S.times 0) c i:ℂ)*F 0 i*
        ((tailMass R n (gaps S.times) i h:ℂ)*probeProduct n (later F) h) := by ring
  simp_rw [he,← Finset.mul_sum,tail_product]
  simp only [P,mul_assoc]



theorem expectation_two (R : Data d) (S : Schedule 1) (F G : Fin d → ℂ) :
    expectation R S (fun u => F (u 0)*G (u 1))=
      P R (S.times 0) (fun i => F i*P R (S.times 1-S.times 0) G i) := by
  have h := expectation_product R S (fun k => if k=0 then F else G)
  have hp : productProbe (n := 1) (fun k => if k=0 then F else G)=(fun u => F (u 0)*G (u 1)) := by
    funext u
    change F (u 0)*(G (u 1)*1)=_
    rw [mul_one]
  rw [hp] at h
  simpa [later,transfer,gaps,P] using h

/-- At depth zero the actual two-event kernel is exactly the accepted scalar-probe kernel. -/
theorem singleton_kernel (R : Data d) (S : Schedule 0) (u v : Path d 0) :
    kernel R S u v=GibbsMultilevelReflection.kernel (firstData R S) (u 0) (v 0) := by
  rw [kernel,mass_split,GibbsMultilevelReflection.kernel_apply]
  simp [pathProduct,firstData]

theorem zero_rate_mass (R : Data d) (S : Schedule n) (hγ : R.γ=0) (h : History d (2*n+1+1)) :
    mass R S h=R.w (historyEquiv _ h 0)*∏ i : Fin (2*n+1),
      if historyEquiv _ h i.castSucc=historyEquiv _ h i.succ then (1 : ℝ) else 0 := by
  rw [mass_product]
  simp [transition,hγ]

theorem zero_rate_support (R : Data d) (S : Schedule n) (hγ : R.γ=0)
    (h : History d (2*n+1+1)) (hm : mass R S h≠0) :
    ∀ i,historyEquiv _ h i=historyEquiv _ h 0 := by
  rw [zero_rate_mass R S hγ] at hm
  have hp := (mul_ne_zero_iff.mp hm).2
  have he (i : Fin (2*n+1)) : historyEquiv _ h i.castSucc=historyEquiv _ h i.succ := by
    have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
    split_ifs at hi with hi'
    · exact hi'
    · exact False.elim (hi rfl)
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (he i).symm.trans ih

theorem repeated_edge (R : Data d) (S : Schedule n) (i : Fin n)
    (ht : S.times i.succ=S.times i.castSucc) (u : Path d n) :
    transition R.w R.γ (S.times i.succ-S.times i.castSucc) (u i.castSucc) (u i.succ)=
      if u i.castSucc=u i.succ then 1 else 0 := by
  simp [ht,transition]

/-- The concrete positive half is (1,2), with reflected full history (-2,-1,1,2). -/
def twoTimes : Schedule 1 where
  times := ![1,2]
  ordered := by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *
  nonnegative := by intro i; fin_cases i <;> norm_num

def nonlinear : Path 3 1 → ℂ := fun u => firstMode (u 0)*secondMode (u 1)

theorem nonlinear_expectation : expectation three twoTimes nonlinear=
    fun i => (Real.exp (-2):ℂ)*firstMode i := by
  change expectation three twoTimes (fun u => firstMode (u 0)*secondMode (u 1))=_
  rw [expectation_two]
  have hg : P three 1 secondMode=fun i => (Real.exp (-1):ℂ)*secondMode i := by
    funext i
    rw [P_modes three 1 (by norm_num),three_means.2]
    simp [three]
  have hf : P three 1 firstMode=fun i => (Real.exp (-1):ℂ)*firstMode i := by
    funext i
    rw [P_modes three 1 (by norm_num),three_means.1]
    simp [three]
  change P three 1 (fun i => firstMode i*P three (2-1) secondMode i)=_
  norm_num only [show (2:ℝ)-1=1 by norm_num]
  rw [hg]
  have hi : (fun i => firstMode i*((Real.exp (-1):ℂ)*secondMode i))=
      fun i => (Real.exp (-1):ℂ)*firstMode i := by
    funext i
    have h := congrFun modes_product i
    linear_combination (Real.exp (-1):ℂ)*h
  rw [hi]
  have hs (F : Fin 3 → ℂ) : P three 1 (fun i => (Real.exp (-1):ℂ)*F i)=
      fun i => (Real.exp (-1):ℂ)*P three 1 F i := by
    funext i
    simp [P,Finset.mul_sum,mul_left_comm]
  rw [hs,hf]
  funext i
  have he : (Real.exp (-1):ℂ)*(Real.exp (-1):ℂ)=(Real.exp (-2):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    norm_num
  rw [← mul_assoc,he]



theorem nonlinear_pairing : cylinderPairing three twoTimes nonlinear nonlinear=
    (5/4:ℂ)*(Real.exp (-4):ℂ) := by
  rw [cylinder_factor,nonlinear_expectation]
  have he : (Real.exp (-2):ℂ)*(Real.exp (-2):ℂ)=(Real.exp (-4):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    norm_num
  have hs (i : Fin 3) : (three.w i:ℂ)*star ((Real.exp (-2):ℂ)*firstMode i)*
      ((Real.exp (-2):ℂ)*firstMode i)=
      (Real.exp (-4):ℂ)*((three.w i:ℂ)*star (firstMode i)*firstMode i) := by
    simp only [map_mul,Complex.star_def,Complex.conj_ofReal]
    linear_combination (three.w i:ℂ)*star (firstMode i)*firstMode i*he
  simp_rw [hs]
  rw [← Finset.mul_sum]
  norm_num [three,firstMode,GibbsReset.threeWeights,Fin.sum_univ_succ,map_ofNat]
  ring

theorem nonlinear_positive : 0<(cylinderPairing three twoTimes nonlinear nonlinear).re := by
  rw [nonlinear_pairing]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  norm_num
  positivity

def nullCylinder : Path 3 1 → ℂ := nonlinear-(Real.exp (-1):ℂ) • firstProbe firstMode

theorem nullCylinder_expectation : expectation three twoTimes nullCylinder=0 := by
  have hf : expectation three twoTimes (firstProbe firstMode)=fun i => (Real.exp (-1):ℂ)*firstMode i := by
    rw [expectation_first]
    funext i
    rw [action_modes]
    have hm : mean (firstData three twoTimes) firstMode=0 := three_means.1
    rw [hm]
    simp [firstData,three,twoTimes]
  change (expectationLinear three twoTimes) (nonlinear-(Real.exp (-1):ℂ) • firstProbe firstMode)=0
  rw [map_sub,map_smul]
  change expectation three twoTimes nonlinear-(Real.exp (-1):ℂ) •
    expectation three twoTimes (firstProbe firstMode)=0
  rw [nonlinear_expectation,hf]
  funext i
  change (Real.exp (-2):ℂ)*firstMode i-(Real.exp (-1):ℂ)*((Real.exp (-1):ℂ)*firstMode i)=0
  have he : (Real.exp (-1):ℂ)*(Real.exp (-1):ℂ)=(Real.exp (-2):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    norm_num
  rw [← mul_assoc,he,sub_self]

theorem nullCylinder_class : mk (kernel three twoTimes) (positive three twoTimes) nullCylinder=0 :=
  (null_iff three twoTimes nullCylinder).mpr nullCylinder_expectation

theorem nullCylinder_value : nullCylinder ![0,2]= -5-(Real.exp (-1):ℂ) := by
  change firstMode (0 : Fin 3)*secondMode (2 : Fin 3)-
    (Real.exp (-1):ℂ)*firstMode (0 : Fin 3)=_
  change (1:ℂ)*(-5)-(Real.exp (-1):ℂ)*1=_
  ring

theorem nullCylinder_nonzero : nullCylinder≠0 := by
  intro h
  have he := congrFun h ![0,2]
  rw [nullCylinder_value] at he
  have hr := congrArg Complex.re he
  simp only [Complex.sub_re,Complex.neg_re,Complex.ofReal_re,Pi.zero_apply,Complex.zero_re] at hr
  norm_num at hr
  have hp := Real.exp_pos (-1)
  linarith

theorem nonlinear_class_nonzero : mk (kernel three twoTimes) (positive three twoTimes) nonlinear≠0 := by
  intro h
  have he := (null_iff three twoTimes nonlinear).mp h
  rw [nonlinear_expectation] at he
  have hi := congrFun he (0 : Fin 3)
  norm_num [firstMode] at hi

theorem three_rank_drop : Fintype.card (Path 3 1)=9 ∧
    Module.finrank ℂ (Reconstructed three twoTimes)=3 := by
  constructor
  · norm_num [Path]
  · exact reconstructed_finrank three twoTimes

theorem twoTimes_actual : GibbsReflectedHistory.symmetricSchedule twoTimes.times= ![-2,-1,1,2] := by
  funext i
  fin_cases i <;> norm_num [GibbsReflectedHistory.symmetricSchedule,twoTimes]



/-- Explicit index identification for the one-coordinate cylinder space. -/
def singletonEquiv : Fin d ≃ Path d 0 where
  toFun i := fun _ => i
  invFun u := u 0
  left_inv i := rfl
  right_inv u := by funext i; fin_cases i; rfl

theorem singleton_pairing (R : Data d) (S : Schedule 0) (F G : Fin d → ℂ) :
    cylinderPairing R S (F ∘ singletonEquiv.symm) (G ∘ singletonEquiv.symm)=
      pairing (GibbsMultilevelReflection.kernel (firstData R S)) F G := by
  change cylinderPairing R S (firstProbe F) (firstProbe G)=_
  rw [cylinder_factor,expectation_first,expectation_first,
    GibbsMultilevelReflection.pairing_action]
  rfl

theorem singleton_kernel_equiv (R : Data d) (S : Schedule 0) (i j : Fin d) :
    kernel R S (singletonEquiv i) (singletonEquiv j)=
      GibbsMultilevelReflection.kernel (firstData R S) i j := singleton_kernel R S _ _

/-- Zero-rate support restricts histories, but does not collapse the d-dimensional quotient. -/
theorem zero_rate_guard (R : Data d) (S : Schedule n) (hγ : R.γ=0) :
    (∀ h,mass R S h≠0 → ∀ i,historyEquiv _ h i=historyEquiv _ h 0) ∧
      Module.finrank ℂ (Reconstructed R S)=d :=
  ⟨fun h hm => zero_rate_support R S hγ h hm,reconstructed_finrank R S⟩


end SKEFTHawking.QuantumNetwork.GibbsMultilevelCylinder
