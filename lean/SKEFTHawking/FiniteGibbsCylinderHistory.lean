import SKEFTHawking.FiniteGibbsUnitalHistory

/-! Reflected complex cylinder probes of one actual finite computational Gibbs history.
The state at zero used in the factorization is an algebraic index, not another
measurement. All history probabilities retain the original intervention tree. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.GibbsCylinderHistory
open Matrix FiniteInterventionProcess GibbsRelaxationProcess GibbsTwoTimeProcess GibbsHistoryKernel
open FinitePositiveKernel
open scoped ComplexOrder InnerProductSpace

/-- The recursive history contains exactly one outcome for each finite label. -/
def historyEquiv : (k : ℕ) → History 2 k ≃ (Fin k → Qubit)
  | 0 => { toFun := fun _ i => Fin.elim0 i
           invFun := fun _ => ()
           left_inv := fun h => by cases h; rfl
           right_inv := fun f => by funext i; exact Fin.elim0 i }
  | k+1 => (Equiv.prodCongr (Equiv.refl Qubit) (historyEquiv k)).trans
      (Fin.consEquiv (fun _ : Fin (k+1) => Qubit))

theorem historyEquiv_outcome (k : ℕ) (h : History 2 k) (i : Fin k) :
    historyEquiv k h i=outcome h i.val := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih h.2 j

abbrev Path (n : ℕ) := Fin (n+1) → Qubit

/-- The negative tuple is read outwards, and the positive tuple chronologically. -/
def split (n : ℕ) : (Fin (2*n+1+1) → Qubit) ≃ Path n × Path n where
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

def pairEquiv (n : ℕ) : History 2 (2*n+1+1) ≃ Path n × Path n :=
  (historyEquiv _).trans (split n)

theorem pair_left (n : ℕ) (h : History 2 (2*n+1+1)) (i : Fin (n+1)) :
    (pairEquiv n h).1 i=outcome h (GibbsReflectedHistory.reverse (GibbsReflectedHistory.positive n i)).val :=
  historyEquiv_outcome _ _ _

theorem pair_right (n : ℕ) (h : History 2 (2*n+1+1)) (i : Fin (n+1)) :
    (pairEquiv n h).2 i=outcome h (GibbsReflectedHistory.positive n i).val :=
  historyEquiv_outcome _ _ _

/-- Detailed balance is proved for the actual transition, including zero elapsed time. -/
theorem detailed_balance (β Δ γ t : ℝ) (a b : Qubit) :
    weights β Δ a*transition β Δ γ t a b=weights β Δ b*transition β Δ γ t b a := by
  fin_cases a <;> fin_cases b <;> simp [transition] <;> ring

/-- Chapman--Kolmogorov inserts a latent state into the original central transition. -/
theorem central_factor (β Δ γ s : ℝ) (a b : Qubit) :
    weights β Δ a*transition β Δ γ (2*s) a b=
      ∑ x,weights β Δ x*transition β Δ γ s x a*transition β Δ γ s x b := by
  simp_rw [detailed_balance β Δ γ s _ a]
  rw [mul_comm 2 s,show s*2=s+s by ring,← chapman_kolmogorov,Finset.mul_sum]
  simp only [mul_assoc]

/-- Forward and reversed edge products share the same outward labels. -/
def pathProduct (β Δ γ : ℝ) {n : ℕ} (τ : Fin (n+1) → ℝ) (u : Path n) : ℝ :=
  ∏ i : Fin n,transition β Δ γ (τ i.succ-τ i.castSucc) (u i.castSucc) (u i.succ)

def reverseProduct (β Δ γ : ℝ) {n : ℕ} (τ : Fin (n+1) → ℝ) (u : Path n) : ℝ :=
  ∏ i : Fin n,transition β Δ γ (τ i.succ-τ i.castSucc) (u i.succ) (u i.castSucc)

/-- Weighted reversal telescopes without dividing by any transition probability. -/
theorem path_reversal (β Δ γ : ℝ) (n : ℕ) (τ : Fin (n+1) → ℝ) (u : Path n) :
    weights β Δ (u (Fin.last n))*reverseProduct β Δ γ τ u=
      weights β Δ (u 0)*pathProduct β Δ γ τ u := by
  induction n with
  | zero => simp [reverseProduct,pathProduct]
  | succ n ih =>
    let τ' : Fin (n+1) → ℝ := fun i => τ i.castSucc
    let u' : Path n := fun i => u i.castSucc
    have hr : reverseProduct β Δ γ τ u=reverseProduct β Δ γ τ' u'*
        transition β Δ γ (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
          (u (Fin.last (n+1))) (u (Fin.last n).castSucc) := by
      unfold reverseProduct
      rw [Fin.prod_univ_castSucc]
      rfl
    have hp : pathProduct β Δ γ τ u=pathProduct β Δ γ τ' u'*
        transition β Δ γ (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
          (u (Fin.last n).castSucc) (u (Fin.last (n+1))) := by
      unfold pathProduct
      rw [Fin.prod_univ_castSucc]
      rfl
    rw [hr,hp]
    have hb := detailed_balance β Δ γ
      (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
      (u (Fin.last (n+1))) (u (Fin.last n).castSucc)
    calc
      _ = (weights β Δ (u (Fin.last (n+1)))*
          transition β Δ γ (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
            (u (Fin.last (n+1))) (u (Fin.last n).castSucc))*reverseProduct β Δ γ τ' u' := by ring
      _ = (weights β Δ (u' (Fin.last n))*reverseProduct β Δ γ τ' u')*
          transition β Δ γ (τ (Fin.last (n+1))-τ (Fin.last n).castSucc)
            (u (Fin.last n).castSucc) (u (Fin.last (n+1))) := by rw [hb]; ring
      _ = _ := by rw [ih τ' u']; simp [u',mul_assoc]

/-- The edge product is split into negative edges, the central edge, and positive edges. -/
theorem product_split (n : ℕ) (f : Fin (2*n+1) → ℝ) :
    ∏ i,f i = (∏ i : Fin n,f ⟨i.val,by omega⟩)*f ⟨n,by omega⟩*
      ∏ i : Fin n,f ⟨n+1+i.val,by omega⟩ := by
  let g : Fin (n+(n+1)) → ℝ := fun i => f ⟨i.val,by omega⟩
  have he : (∏ i,f i)=∏ i,g i := by
    apply Fintype.prod_equiv (finCongr (show 2*n+1=n+(n+1) by omega))
    intro i
    rfl
  rw [he,Fin.prod_univ_add,Fin.prod_univ_succ]
  simp only [g]
  simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,Fin.val_succ,Nat.add_zero]
  simp only [Nat.add_comm,Nat.add_left_comm,mul_assoc]

variable {n : ℕ}

theorem outcome_pair (u v : Path n) (i : Fin (2*n+1+1)) :
    outcome ((pairEquiv n).symm (u,v)) i.val=(split n).symm (u,v) i := by
  rw [← historyEquiv_outcome]
  change historyEquiv _ ((historyEquiv _).symm ((split n).symm (u,v))) i=_
  rw [Equiv.apply_symm_apply]

theorem tuple_mass (d : GibbsUnitalHistory.Data n) (u v : Path n) :
    GibbsUnitalHistory.mass d ((pairEquiv n).symm (u,v))=
      weights d.β d.Δ ((split n).symm (u,v) 0)*
      ∏ i : Fin (2*n+1),transition d.β d.Δ d.γ
        (GibbsReflectedHistory.symmetricSchedule d.times i.succ-
          GibbsReflectedHistory.symmetricSchedule d.times i.castSucc)
        ((split n).symm (u,v) i.castSucc) ((split n).symm (u,v) i.succ) := by
  simp only [GibbsUnitalHistory.mass,GibbsUnitalHistory.history,history_product]
  change weights d.β d.Δ (outcome ((pairEquiv n).symm (u,v)) 0)*_= _
  have hz := outcome_pair u v ⟨0,by omega⟩
  rw [hz]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have ha := outcome_pair u v ⟨i.val,by omega⟩
  have hb := outcome_pair u v ⟨i.val+1,by omega⟩
  rw [ha,hb]
  unfold GibbsUnitalHistory.schedule
  rw [extendSchedule_eval (GibbsReflectedHistory.symmetricSchedule d.times) ⟨i.val+1,by omega⟩,
    extendSchedule_eval (GibbsReflectedHistory.symmetricSchedule d.times) ⟨i.val,by omega⟩]
  rfl

def edge (d : GibbsUnitalHistory.Data n) (u v : Path n) (i : Fin (2*n+1)) : ℝ :=
  transition d.β d.Δ d.γ
    (GibbsReflectedHistory.symmetricSchedule d.times i.succ-
      GibbsReflectedHistory.symmetricSchedule d.times i.castSucc)
    ((split n).symm (u,v) i.castSucc) ((split n).symm (u,v) i.succ)

theorem edge_negative (d : GibbsUnitalHistory.Data n) (u v : Path n) (i : Fin n) :
    edge d u v ⟨i.val,by omega⟩=
      transition d.β d.Δ d.γ
        (d.times i.rev.succ-d.times i.rev.castSucc) (u i.rev.succ) (u i.rev.castSucc) := by
  unfold edge GibbsReflectedHistory.symmetricSchedule split
  simp only [Equiv.coe_fn_symm_mk,Fin.val_succ,Fin.val_castSucc]
  simp only [show i.val ≤ n by omega,show i.val+1 ≤ n by omega,dif_pos]
  have ha : (⟨n-i.val,by omega⟩ : Fin (n+1))=i.rev.succ := by apply Fin.ext; simp [Fin.rev]; omega
  have hb : (⟨n-(i.val+1),by omega⟩ : Fin (n+1))=i.rev.castSucc := by apply Fin.ext; simp [Fin.rev]
  rw [ha,hb]
  congr 1
  ring

theorem edge_central (d : GibbsUnitalHistory.Data n) (u v : Path n) :
    edge d u v ⟨n,by omega⟩=transition d.β d.Δ d.γ (2*d.times 0) (u 0) (v 0) := by
  unfold edge GibbsReflectedHistory.symmetricSchedule split
  simp only [Equiv.coe_fn_symm_mk,Fin.val_succ,Fin.val_castSucc]
  simp only [show n ≤ n by omega,show ¬n+1 ≤ n by omega,dif_pos,dite_false,Nat.sub_self]
  change transition d.β d.Δ d.γ (d.times 0- -d.times 0) (u 0) (v 0)=_
  congr 1
  ring

theorem edge_positive (d : GibbsUnitalHistory.Data n) (u v : Path n) (i : Fin n) :
    edge d u v ⟨n+1+i.val,by omega⟩=
      transition d.β d.Δ d.γ (d.times i.succ-d.times i.castSucc) (v i.castSucc) (v i.succ) := by
  unfold edge GibbsReflectedHistory.symmetricSchedule split
  simp only [Equiv.coe_fn_symm_mk,Fin.val_succ,Fin.val_castSucc]
  simp only [show ¬n+1+i.val ≤ n by omega,show ¬n+1+i.val+1 ≤ n by omega,dite_false]
  have ha : (⟨n+1+i.val-(n+1),by omega⟩ : Fin (n+1))=i.castSucc := by apply Fin.ext; dsimp; omega
  have hb : (⟨n+1+i.val+1-(n+1),by omega⟩ : Fin (n+1))=i.succ := by apply Fin.ext; dsimp; omega
  rw [ha,hb]

/-- The full tree law is split and reversed before the latent-state identity is used. -/
theorem mass_split (d : GibbsUnitalHistory.Data n) (u v : Path n) :
    GibbsUnitalHistory.mass d ((pairEquiv n).symm (u,v))=
      weights d.β d.Δ (u 0)*pathProduct d.β d.Δ d.γ d.times u*
        transition d.β d.Δ d.γ (2*d.times 0) (u 0) (v 0)*
        pathProduct d.β d.Δ d.γ d.times v := by
  rw [tuple_mass]
  change weights d.β d.Δ ((split n).symm (u,v) 0)*(∏ i,edge d u v i)=_
  have h0 : (split n).symm (u,v) 0=u (Fin.last n) := by simp [split]; rfl
  rw [h0,product_split]
  simp_rw [edge_negative,edge_central,edge_positive]
  have hr := Equiv.prod_comp Fin.revPerm (fun i : Fin n =>
    transition d.β d.Δ d.γ (d.times i.succ-d.times i.castSucc) (u i.succ) (u i.castSucc))
  change (∏ i : Fin n,transition d.β d.Δ d.γ (d.times i.rev.succ-d.times i.rev.castSucc) (u i.rev.succ) (u i.rev.castSucc))=reverseProduct d.β d.Δ d.γ d.times u at hr
  rw [hr]
  change _=weights d.β d.Δ (u 0)*pathProduct d.β d.Δ d.γ d.times u*_*pathProduct d.β d.Δ d.γ d.times v
  rw [← mul_assoc,← mul_assoc,path_reversal]
  rfl

/-- Conditional path law through a latent two-state index. -/
def conditional (d : GibbsUnitalHistory.Data n) (x : Qubit) (u : Path n) : ℝ :=
  transition d.β d.Δ d.γ (d.times 0) x (u 0)*pathProduct d.β d.Δ d.γ d.times u

theorem mass_factor (d : GibbsUnitalHistory.Data n) (u v : Path n) :
    GibbsUnitalHistory.mass d ((pairEquiv n).symm (u,v))=
      ∑ x,weights d.β d.Δ x*conditional d x u*conditional d x v := by
  rw [mass_split]
  calc
    _ = (weights d.β d.Δ (u 0)*transition d.β d.Δ d.γ (2*d.times 0) (u 0) (v 0))*
        pathProduct d.β d.Δ d.γ d.times u*pathProduct d.β d.Δ d.γ d.times v := by ring
    _ = _ := by
      rw [central_factor,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      unfold conditional
      ring

theorem transition_nonnegative (β Δ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (a b : Qubit) :
    0 ≤ transition β Δ γ t a b := by
  have he : Real.exp (-γ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold transition
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr he) (weights_pos β Δ b).le)
    (mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num))

theorem conditional_nonnegative (d : GibbsUnitalHistory.Data n) (x : Qubit) (u : Path n) :
    0 ≤ conditional d x u := by
  apply mul_nonneg (transition_nonnegative _ _ _ _ d.rate_nonnegative (d.nonnegative 0) _ _)
  apply Finset.prod_nonneg
  intro i _
  exact transition_nonnegative _ _ _ _ d.rate_nonnegative
    (sub_nonneg.mpr (d.ordered (by exact Fin.castSucc_le_succ i))) _ _

/-- This auxiliary schedule is used only to evaluate a conditional finite sum. -/
def latentSchedule (d : GibbsUnitalHistory.Data n) : ℕ → ℝ
  | 0 => 0
  | k+1 => extendSchedule d.times k

theorem conditional_tail (d : GibbsUnitalHistory.Data n) (x : Qubit) (u : Path n) :
    conditional d x u=tailMass d.β d.Δ d.γ (n+1) (latentSchedule d) x ((historyEquiv (n+1)).symm u) := by
  rw [tailMass_product,Fin.prod_univ_succ]
  have ho (i : Fin (n+1)) : outcome ((historyEquiv (n+1)).symm u) i.val=u i := by
    rw [← historyEquiv_outcome,Equiv.apply_symm_apply]
  change transition d.β d.Δ d.γ (d.times 0) x (u 0)*pathProduct d.β d.Δ d.γ d.times u=
    transition d.β d.Δ d.γ (extendSchedule d.times 0-0) x
      (outcome ((historyEquiv (n+1)).symm u) 0)*_
  rw [extendSchedule_eval d.times ⟨0,by omega⟩,ho ⟨0,by omega⟩,sub_zero]
  congr 1
  unfold pathProduct
  apply Finset.prod_congr rfl
  intro i _
  change transition d.β d.Δ d.γ (d.times i.succ-d.times i.castSucc) (u i.castSucc) (u i.succ)=
    transition d.β d.Δ d.γ (extendSchedule d.times (i.val+1)-extendSchedule d.times i.val)
      (outcome ((historyEquiv (n+1)).symm u) i.val)
      (outcome ((historyEquiv (n+1)).symm u) (i.val+1))
  rw [extendSchedule_eval d.times ⟨i.val+1,by omega⟩,extendSchedule_eval d.times ⟨i.val,by omega⟩,
    ho ⟨i.val,by omega⟩,ho ⟨i.val+1,by omega⟩]
  rfl

theorem conditional_sum (d : GibbsUnitalHistory.Data n) (x : Qubit) : ∑ u,conditional d x u=1 := by
  simp_rw [conditional_tail]
  rw [Equiv.sum_comp (historyEquiv (n+1)).symm,tailMass_sum]

/-- Arbitrary complex functions on the finite positive history. -/
def expectation (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) (x : Qubit) : ℂ :=
  ∑ u,(conditional d x u:ℂ)*F u

def cylinderPairing (d : GibbsUnitalHistory.Data n) (F G : Path n → ℂ) : ℂ :=
  ∑ h,(GibbsUnitalHistory.mass d h:ℂ)*star (F ((pairEquiv n h).1))*G ((pairEquiv n h).2)

/-- Indicator cylinders index a finite kernel containing all complex cylinder functions. -/
def kernel (d : GibbsUnitalHistory.Data n) : Matrix (Path n) (Path n) ℂ :=
  fun u v => (GibbsUnitalHistory.mass d ((pairEquiv n).symm (u,v)):ℂ)

theorem kernel_factor (d : GibbsUnitalHistory.Data n) (u v : Path n) :
    kernel d u v=∑ x,(weights d.β d.Δ x:ℂ)*(conditional d x u:ℂ)*(conditional d x v:ℂ) := by
  simp only [kernel,mass_factor,Complex.ofReal_sum,Complex.ofReal_mul]

theorem pairing_actual (d : GibbsUnitalHistory.Data n) (F G : Path n → ℂ) :
    pairing (kernel d) F G=cylinderPairing d F G := by
  have he := Equiv.sum_comp (pairEquiv n).symm
    (fun h => (GibbsUnitalHistory.mass d h:ℂ)*star (F ((pairEquiv n h).1))*G ((pairEquiv n h).2))
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

theorem pairing_factor (d : GibbsUnitalHistory.Data n) (F G : Path n → ℂ) :
    pairing (kernel d) F G=
      ∑ x,(weights d.β d.Δ x:ℂ)*star (expectation d F x)*expectation d G x := by
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

theorem cylinder_factor (d : GibbsUnitalHistory.Data n) (F G : Path n → ℂ) :
    cylinderPairing d F G=
      ∑ x,(weights d.β d.Δ x:ℂ)*star (expectation d F x)*expectation d G x := by
  rw [← pairing_actual,pairing_factor]

def gram (d : GibbsUnitalHistory.Data n) : Matrix Qubit (Path n) ℂ :=
  fun x u => (Real.sqrt (weights d.β d.Δ x):ℂ)*(conditional d x u:ℂ)

theorem kernel_gram (d : GibbsUnitalHistory.Data n) : kernel d=(gram d)ᴴ*gram d := by
  ext u v
  rw [kernel_factor]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,gram,map_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro x _
  have hs : (Real.sqrt (weights d.β d.Δ x):ℂ)^2=(weights d.β d.Δ x:ℂ) := by
    exact_mod_cast Real.sq_sqrt (weights_pos d.β d.Δ x).le
  linear_combination -(conditional d x u:ℂ)*(conditional d x v:ℂ)*hs

theorem positive (d : GibbsUnitalHistory.Data n) : (kernel d).PosSemidef := by
  rw [kernel_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

abbrev Reconstructed (d : GibbsUnitalHistory.Data n) := Space (kernel d) (positive d)

/-- Faithfulness makes the null criterion exactly two vanishing conditional values. -/
theorem null_iff (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) :
    mk (kernel d) (positive d) F=0 ↔ expectation d F 0=0 ∧ expectation d F 1=0 := by
  rw [mk_eq_zero_iff,pairing_factor,Fin.sum_univ_two]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hn0 := Complex.normSq_nonneg (expectation d F 0)
    have hn1 := Complex.normSq_nonneg (expectation d F 1)
    have hw0 := weights_pos d.β d.Δ 0
    have hw1 := weights_pos d.β d.Δ 1
    have he (w : ℝ) (z : ℂ) : ((w:ℂ)*star z*z).re=w*Complex.normSq z := by
      rw [mul_assoc,mul_comm (star z) z,Complex.star_def,Complex.mul_conj]
      simp
    simp only [Complex.add_re,he,Complex.zero_re] at hr
    constructor <;> apply Complex.normSq_eq_zero.mp
    · nlinarith [mul_nonneg hw1.le hn1]
    · nlinarith [mul_nonneg hw0.le hn0]
  · rintro ⟨h0,h1⟩
    rw [h0,h1]
    simp

theorem expectation_add (d : GibbsUnitalHistory.Data n) (F G : Path n → ℂ) (x : Qubit) :
    expectation d (F+G) x=expectation d F x+expectation d G x := by
  simp [expectation,mul_add,Finset.sum_add_distrib]

theorem expectation_smul (d : GibbsUnitalHistory.Data n) (a : ℂ) (F : Path n → ℂ) (x : Qubit) :
    expectation d (a • F) x=a*expectation d F x := by
  simp [expectation,Finset.mul_sum,mul_left_comm]

theorem expectation_one (d : GibbsUnitalHistory.Data n) (x : Qubit) : expectation d (fun _ => 1) x=1 := by
  simp only [expectation,mul_one,← Complex.ofReal_sum,conditional_sum,Complex.ofReal_one]

theorem transition_centered (β Δ γ t : ℝ) (x : Qubit) :
    (∑ a,transition β Δ γ t x a*centered β Δ a)=Real.exp (-γ*t)*centered β Δ x := by
  have hn : weights β Δ 0+weights β Δ 1=1 := by simpa only [Fin.sum_univ_two] using weights_sum β Δ
  have hw : weights β Δ 1=1-weights β Δ 0 := by linarith
  fin_cases x <;> norm_num [Fin.sum_univ_two,transition,centered,sign,meanZ] <;> rw [hw] <;> ring

theorem conditional_centered (d : GibbsUnitalHistory.Data n) (i : Fin (n+1)) (x : Qubit) :
    (∑ u,conditional d x u*centered d.β d.Δ (u i))=
      Real.exp (-d.γ*d.times i)*centered d.β d.Δ x := by
  have he := Equiv.sum_comp (historyEquiv (n+1)).symm
    (fun h => tailMass d.β d.Δ d.γ (n+1) (latentSchedule d) x h*centered d.β d.Δ (outcome h i.val))
  have ho (u : Path n) : outcome ((historyEquiv (n+1)).symm u) i.val=u i := by
    rw [← historyEquiv_outcome,Equiv.apply_symm_apply]
  simp_rw [ho,← conditional_tail] at he
  rw [he,endpoint_expectation _ _ _ _ _ _ i.val i.isLt,transition_centered]
  simp only [latentSchedule,sub_zero,extendSchedule_eval]

def centeredProbe (d : GibbsUnitalHistory.Data n) (i : Fin (n+1)) (u : Path n) : ℂ :=
  (centered d.β d.Δ (u i):ℂ)

theorem expectation_centered (d : GibbsUnitalHistory.Data n) (i : Fin (n+1)) (x : Qubit) :
    expectation d (centeredProbe d i) x=
      GibbsReflectedHistory.decay d.γ (d.times i)*(centered d.β d.Δ x:ℂ) := by
  unfold expectation centeredProbe GibbsReflectedHistory.decay
  exact_mod_cast conditional_centered d i x

def centeredAmplitude (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) : ℂ :=
  (expectation d F 0-expectation d F 1)/2

def constantAmplitude (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) : ℂ :=
  expectation d F 0-centeredAmplitude d F*(centered d.β d.Δ 0:ℂ)

theorem expectation_modes (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) (x : Qubit) :
    expectation d F x=constantAmplitude d F+centeredAmplitude d F*(centered d.β d.Δ x:ℂ) := by
  fin_cases x <;> simp [constantAmplitude,centeredAmplitude,centered,sign]; ring

theorem weighted_modes (β Δ : ℝ) (a b c e : ℂ) :
    (∑ x : Qubit,(weights β Δ x:ℂ)*star (a+b*(centered β Δ x:ℂ))*(c+e*(centered β Δ x:ℂ)))=
      star a*c+((1-meanZ β Δ^2:ℝ):ℂ)*star b*e := by
  have hn : weights β Δ 0+weights β Δ 1=1 := by simpa only [Fin.sum_univ_two] using weights_sum β Δ
  have hw : weights β Δ 1=1-weights β Δ 0 := by linarith
  simp only [Fin.sum_univ_two,centered,sign,meanZ,hw,map_add,map_mul,Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring

theorem pairing_modes (d : GibbsUnitalHistory.Data n) (F G : Path n → ℂ) :
    pairing (kernel d) F G=star (constantAmplitude d F)*constantAmplitude d G+
      ((1-meanZ d.β d.Δ^2:ℝ):ℂ)*star (centeredAmplitude d F)*centeredAmplitude d G := by
  rw [pairing_factor]
  simp_rw [expectation_modes]
  exact weighted_modes _ _ _ _ _ _

/-- The previously reconstructed probes embed as genuine functions of the positive path. -/
def unitalProbe (d : GibbsUnitalHistory.Data n) (c : Option (Fin (n+1)) → ℂ) (u : Path n) : ℂ :=
  c none+∑ i,c (some i)*centeredProbe d i u

theorem expectation_unital (d : GibbsUnitalHistory.Data n) (c : Option (Fin (n+1)) → ℂ) (x : Qubit) :
    expectation d (unitalProbe d c) x=c none+GibbsUnitalHistory.amplitude d c*(centered d.β d.Δ x:ℂ) := by
  unfold expectation unitalProbe
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  rw [← Finset.sum_mul,show (∑ u,(conditional d x u:ℂ))=1 by exact_mod_cast conditional_sum d x,one_mul]
  rw [Finset.sum_comm]
  have he (i : Fin (n+1)) :
      (∑ u,(conditional d x u:ℂ)*(c (some i)*centeredProbe d i u))=
        c (some i)*(GibbsReflectedHistory.decay d.γ (d.times i)*(centered d.β d.Δ x:ℂ)) := by
    rw [← expectation_centered d i x]
    simp only [expectation,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp_rw [he]
  simp only [GibbsUnitalHistory.amplitude,GibbsReflectedHistory.amplitude,Finset.sum_mul,mul_assoc]

theorem unital_amplitudes (d : GibbsUnitalHistory.Data n) (c : Option (Fin (n+1)) → ℂ) :
    constantAmplitude d (unitalProbe d c)=c none ∧
      centeredAmplitude d (unitalProbe d c)=GibbsUnitalHistory.amplitude d c := by
  unfold constantAmplitude centeredAmplitude
  rw [expectation_unital,expectation_unital]
  norm_num [centered,sign]
  constructor <;> ring

theorem pairing_unital (d : GibbsUnitalHistory.Data n) (c e : Option (Fin (n+1)) → ℂ) :
    pairing (kernel d) (unitalProbe d c) (unitalProbe d e)=
      pairing (GibbsUnitalHistory.reflection d).kernel c e := by
  rw [pairing_modes,GibbsUnitalHistory.pairing_modes,
    (unital_amplitudes d c).1,(unital_amplitudes d c).2,
    (unital_amplitudes d e).1,(unital_amplitudes d e).2]

def amplitudeLinear (d : GibbsUnitalHistory.Data n) : Coefficients (positive d) →ₗ[ℂ] ℂ × ℂ where
  toFun F := (constantAmplitude d F,centeredAmplitude d F)
  map_add' F G := by
    have he (x : Qubit) : expectation d (F+G) x=expectation d F x+expectation d G x :=
      expectation_add d F G x
    apply Prod.ext <;> simp [constantAmplitude,centeredAmplitude,he] <;> ring
  map_smul' r F := by
    have he (x : Qubit) : expectation d (r • F) x=r*expectation d F x := expectation_smul d r F x
    apply Prod.ext <;> simp [constantAmplitude,centeredAmplitude,he] <;> ring

def transferCoefficients (d : GibbsUnitalHistory.Data n) :
    Coefficients (positive d) →ₗ[ℂ] GibbsUnitalHistory.Reconstructed d :=
  (GibbsUnitalHistory.stateLinear d).comp (amplitudeLinear d)

theorem transferCoefficients_inner (d : GibbsUnitalHistory.Data n) (F G : Coefficients (positive d)) :
    ⟪transferCoefficients d F,transferCoefficients d G⟫_ℂ=pairing (kernel d) F G := by
  change ⟪GibbsUnitalHistory.state d (constantAmplitude d F) (centeredAmplitude d F),
    GibbsUnitalHistory.state d (constantAmplitude d G) (centeredAmplitude d G)⟫_ℂ=_
  rw [GibbsUnitalHistory.state,GibbsUnitalHistory.state,inner_mk,
    GibbsUnitalHistory.pairing_modes,GibbsUnitalHistory.representative_amplitude,
    GibbsUnitalHistory.representative_amplitude,pairing_modes]
  rfl

theorem transferCoefficients_null (d : GibbsUnitalHistory.Data n) :
    nullSpace (kernel d) (positive d) ≤ (transferCoefficients d).ker := by
  intro F hF
  apply LinearMap.mem_ker.mpr
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [transferCoefficients_inner]
  exact (mem_nullSpace_iff _ _ F).mp hF

/-- Cross-space descent into the existing unital reconstruction. -/
def transferLinear (d : GibbsUnitalHistory.Data n) : Reconstructed d →ₗ[ℂ] GibbsUnitalHistory.Reconstructed d :=
  ((nullSpace (kernel d) (positive d)).liftQ (transferCoefficients d) (transferCoefficients_null d)).comp
    (quotientEquiv (kernel d) (positive d)).symm.toLinearMap

theorem transferLinear_mk (d : GibbsUnitalHistory.Data n) (F : Coefficients (positive d)) :
    transferLinear d (mk _ (positive d) F)=transferCoefficients d F := by
  rw [← quotientEquiv_mk (positive d) F]
  simp only [transferLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]

def transfer (d : GibbsUnitalHistory.Data n) : Reconstructed d →ₗᵢ[ℂ] GibbsUnitalHistory.Reconstructed d :=
  (transferLinear d).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective _ (positive d) z
    obtain ⟨G,rfl⟩ := mk_surjective _ (positive d) w
    rw [transferLinear_mk,transferLinear_mk,inner_mk,transferCoefficients_inner])

theorem transfer_unital (d : GibbsUnitalHistory.Data n) (c : Option (Fin (n+1)) → ℂ) :
    transfer d (mk _ (positive d) (unitalProbe d c))=mk _ (GibbsUnitalHistory.positive d) c := by
  change transferLinear d (mk _ (positive d) (unitalProbe d c))=_
  rw [transferLinear_mk]
  change GibbsUnitalHistory.state d (constantAmplitude d (unitalProbe d c))
    (centeredAmplitude d (unitalProbe d c))=_
  rw [(unital_amplitudes d c).1,(unital_amplitudes d c).2]
  apply (GibbsUnitalHistory.embedding d).injective
  rw [GibbsUnitalHistory.embedding_state,GibbsUnitalHistory.embedding_mk]

theorem transfer_surjective (d : GibbsUnitalHistory.Data n) : Function.Surjective (transfer d) := by
  intro z
  obtain ⟨c,rfl⟩ := mk_surjective _ (GibbsUnitalHistory.positive d) z
  exact ⟨mk _ (positive d) (unitalProbe d c),transfer_unital d c⟩

/-- The full cylinder quotient is isometrically the already constructed unital quotient. -/
def unitalEquiv (d : GibbsUnitalHistory.Data n) : Reconstructed d ≃ₗᵢ[ℂ] GibbsUnitalHistory.Reconstructed d :=
  LinearIsometryEquiv.ofSurjective (transfer d) (transfer_surjective d)

/-- Every cylinder class has an old constant/centered representative. -/
theorem unital_complete (d : GibbsUnitalHistory.Data n) (F : Path n → ℂ) :
    ∃ c : Option (Fin (n+1)) → ℂ,mk _ (positive d) F=mk _ (positive d) (unitalProbe d c) := by
  obtain ⟨c,hc⟩ := mk_surjective _ (GibbsUnitalHistory.positive d) (transfer d (mk _ (positive d) F))
  refine ⟨c,(transfer d).injective ?_⟩
  rw [transfer_unital,hc]

/-- The full indicator family has rank two, even at zero reset or repeated times. -/
theorem reconstructed_finrank (d : GibbsUnitalHistory.Data n) : Module.finrank ℂ (Reconstructed d)=2 := by
  rw [(unitalEquiv d).toLinearEquiv.finrank_eq,GibbsUnitalHistory.reconstructed_finrank]

/-- A two-label path sum is an ordinary sum over its two outcomes. -/
theorem path_two_sum (f : Path 1 → ℂ) : (∑ u,f u)=∑ a : Qubit,∑ b : Qubit,f ![a,b] := by
  rw [← Equiv.sum_comp (historyEquiv 2) f]
  change (∑ h : Qubit × (Qubit × Unit),f (historyEquiv 2 h))=_
  simp only [Fintype.sum_prod_type,Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1

theorem centered_square (β Δ : ℝ) (x : Qubit) :
    centered β Δ x^2=(1-meanZ β Δ^2)-2*meanZ β Δ*centered β Δ x := by
  fin_cases x <;> norm_num [centered,sign] <;> ring

def productProbe (d : GibbsUnitalHistory.Data 1) (u : Path 1) : ℂ :=
  centeredProbe d 0 u*centeredProbe d 1 u

/-- A genuine two-time product, evaluated from the finite conditional path sum. -/
theorem expectation_product (d : GibbsUnitalHistory.Data 1) (x : Qubit) :
    expectation d (productProbe d) x=
      ((1-meanZ d.β d.Δ^2)*Real.exp (-d.γ*(d.times 1-d.times 0)):ℝ)-
        (2*meanZ d.β d.Δ*Real.exp (-d.γ*d.times 1):ℝ)*(centered d.β d.Δ x:ℂ) := by
  unfold expectation
  rw [path_two_sum]
  have hreal : (∑ a : Qubit,∑ b : Qubit,
      transition d.β d.Δ d.γ (d.times 0) x a*
        transition d.β d.Δ d.γ (d.times 1-d.times 0) a b*(centered d.β d.Δ a*centered d.β d.Δ b))=
      (1-meanZ d.β d.Δ^2)*Real.exp (-d.γ*(d.times 1-d.times 0))-
        2*meanZ d.β d.Δ*Real.exp (-d.γ*d.times 1)*centered d.β d.Δ x := by
    have hi (a : Qubit) :
        (∑ b,transition d.β d.Δ d.γ (d.times 0) x a*
          transition d.β d.Δ d.γ (d.times 1-d.times 0) a b*(centered d.β d.Δ a*centered d.β d.Δ b))=
        transition d.β d.Δ d.γ (d.times 0) x a*
          (Real.exp (-d.γ*(d.times 1-d.times 0))*centered d.β d.Δ a^2) := by
      have he := transition_centered d.β d.Δ d.γ (d.times 1-d.times 0) a
      calc
        _ = transition d.β d.Δ d.γ (d.times 0) x a*centered d.β d.Δ a*
            (∑ b,transition d.β d.Δ d.γ (d.times 1-d.times 0) a b*centered d.β d.Δ b) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
        _ = _ := by rw [he]; ring
    simp_rw [hi,centered_square]
    have he : Real.exp (-d.γ*(d.times 1-d.times 0))*Real.exp (-d.γ*d.times 0)=Real.exp (-d.γ*d.times 1) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (Real.exp (-d.γ*(d.times 1-d.times 0))*(1-meanZ d.β d.Δ^2))*
          (∑ a,transition d.β d.Δ d.γ (d.times 0) x a)-
          (2*meanZ d.β d.Δ*Real.exp (-d.γ*(d.times 1-d.times 0)))*
          (∑ a,transition d.β d.Δ d.γ (d.times 0) x a*centered d.β d.Δ a) := by
        rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [transition_sum,transition_centered]; linear_combination -2*meanZ d.β d.Δ*centered d.β d.Δ x*he
  simpa [conditional,pathProduct,productProbe,centeredProbe,Fin.prod_univ_one,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_sub,mul_assoc] using congrArg Complex.ofReal hreal

theorem product_amplitudes (d : GibbsUnitalHistory.Data 1) :
    constantAmplitude d (productProbe d)=((1-meanZ d.β d.Δ^2)*Real.exp (-d.γ*(d.times 1-d.times 0)):ℝ) ∧
    centeredAmplitude d (productProbe d)=(-(2*meanZ d.β d.Δ*Real.exp (-d.γ*d.times 1)):ℝ) := by
  unfold constantAmplitude centeredAmplitude
  rw [expectation_product,expectation_product]
  norm_num [centered,sign]
  constructor <;> ring

abbrev exampleData := GibbsUnitalHistory.exampleData

theorem example_same_history : GibbsReflectedHistory.symmetricSchedule exampleData.times= ![-2,-1,1,2] :=
  GibbsUnitalHistory.example_schedule

theorem example_times : exampleData.times 0=1 ∧ exampleData.times 1=2 := by
  norm_num [exampleData,GibbsUnitalHistory.exampleData,GibbsReflectedHistory.exampleTimes]

theorem example_decay : GibbsReflectedHistory.decay exampleData.γ (exampleData.times 0)=(Real.exp (-1):ℂ) := by
  unfold GibbsReflectedHistory.decay
  rw [example_times.1]
  change (Real.exp (-(1:ℝ)*1):ℂ)=_
  norm_num

theorem example_product_expectation (x : Qubit) :
    expectation exampleData (productProbe exampleData) x=
      ((1-meanZ 1 1^2)*Real.exp (-1):ℝ)-(2*meanZ 1 1*Real.exp (-2):ℝ)*(centered 1 1 x:ℂ) := by
  have he := expectation_product exampleData x
  rw [example_times.1,example_times.2] at he
  norm_num only [show exampleData.γ=1 by rfl,show exampleData.β=1 by rfl,show exampleData.Δ=1 by rfl] at he
  exact he

theorem example_product_modes :
    constantAmplitude exampleData (productProbe exampleData)≠0 ∧
      centeredAmplitude exampleData (productProbe exampleData)≠0 := by
  rw [(product_amplitudes exampleData).1,(product_amplitudes exampleData).2]
  constructor
  · exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (ne_of_gt (stationary_variance_pos _ _)) (Real.exp_ne_zero _))
  · apply Complex.ofReal_ne_zero.mpr
    apply neg_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt nonuniform_mean)) (Real.exp_ne_zero _)

theorem example_four_point :
    cylinderPairing exampleData (productProbe exampleData) (productProbe exampleData)=
      ((1-meanZ 1 1^2)^2*Real.exp (-2)+4*meanZ 1 1^2*(1-meanZ 1 1^2)*Real.exp (-4):ℝ) := by
  rw [← pairing_actual,pairing_modes,(product_amplitudes exampleData).1,(product_amplitudes exampleData).2]
  have h1 : Real.exp (-1)*Real.exp (-1)=Real.exp (-2) := by rw [← Real.exp_add]; norm_num
  have h2 : Real.exp (-2)*Real.exp (-2)=Real.exp (-4) := by rw [← Real.exp_add]; norm_num
  rw [example_times.1,example_times.2]
  change star (((1-meanZ 1 1^2)*Real.exp (-(1:ℝ)*(2-1)):ℝ):ℂ)*
      (((1-meanZ 1 1^2)*Real.exp (-(1:ℝ)*(2-1)):ℝ):ℂ)+
    ((1-meanZ 1 1^2:ℝ):ℂ)*star ((-(2*meanZ 1 1*Real.exp (-(1:ℝ)*2)):ℝ):ℂ)*
      ((-(2*meanZ 1 1*Real.exp (-(1:ℝ)*2)):ℝ):ℂ)=_
  simp only [Complex.star_def,Complex.conj_ofReal]
  norm_cast
  norm_num
  rw [← h2,← h1]
  ring

theorem example_constant_product :
    cylinderPairing exampleData (fun _ => 1) (productProbe exampleData)=
      ((1-meanZ 1 1^2)*Real.exp (-1):ℝ) := by
  rw [cylinder_factor]
  simp_rw [expectation_one,example_product_expectation]
  have he := weighted_modes 1 1 1 0
    (((1-meanZ 1 1^2)*Real.exp (-1):ℝ):ℂ) ((-(2*meanZ 1 1*Real.exp (-2)):ℝ):ℂ)
  simpa [exampleData,GibbsUnitalHistory.exampleData,sub_eq_add_neg] using he

theorem example_centered_product :
    cylinderPairing exampleData (centeredProbe exampleData 0) (productProbe exampleData)=
      (-2*meanZ 1 1*(1-meanZ 1 1^2)*Real.exp (-3):ℝ) := by
  rw [cylinder_factor]
  simp_rw [expectation_centered,example_product_expectation]
  have he := weighted_modes 1 1 0 ((Real.exp (-1):ℝ):ℂ)
    (((1-meanZ 1 1^2)*Real.exp (-1):ℝ):ℂ) ((-(2*meanZ 1 1*Real.exp (-2)):ℝ):ℂ)
  have hx : Real.exp (-1)*Real.exp (-2)=Real.exp (-3) := by rw [← Real.exp_add]; norm_num
  have he' : (∑ x : Qubit,(weights 1 1 x:ℂ)*star ((Real.exp (-1):ℂ)*(centered 1 1 x:ℂ))*
      (((1-meanZ 1 1^2)*Real.exp (-1):ℝ)-(2*meanZ 1 1*Real.exp (-2):ℝ)*(centered 1 1 x:ℂ)))=
      ((1-meanZ 1 1^2):ℂ)*star (Real.exp (-1):ℂ)*(-(2*meanZ 1 1*Real.exp (-2):ℝ):ℂ) := by
    simpa [sub_eq_add_neg] using he
  rw [example_decay]
  change (∑ x : Qubit,(weights 1 1 x:ℂ)*star ((Real.exp (-1):ℂ)*(centered 1 1 x:ℂ))*
    (((1-meanZ 1 1^2)*Real.exp (-1):ℝ)-(2*meanZ 1 1*Real.exp (-2):ℝ)*(centered 1 1 x:ℂ)))=_
  rw [he']
  simp only [Complex.star_def,Complex.conj_ofReal]
  norm_cast
  norm_num
  rw [← hx]
  ring

/-- A nonlinear cylinder direction annihilated by the two conditional modes. -/
def exampleNull (u : Path 1) : ℂ := productProbe exampleData u-
  ((1-meanZ 1 1^2)*Real.exp (-1):ℝ)+(2*meanZ 1 1*Real.exp (-1):ℝ)*centeredProbe exampleData 0 u

theorem expectation_sub (d : GibbsUnitalHistory.Data n) (F G : Path n → ℂ) (x : Qubit) :
    expectation d (F-G) x=expectation d F x-expectation d G x := by
  simp [expectation,mul_sub,Finset.sum_sub_distrib]

theorem example_null_expectation (x : Qubit) : expectation exampleData exampleNull x=0 := by
  have hf : exampleNull=
      (productProbe exampleData-(((1-meanZ 1 1^2)*Real.exp (-1):ℝ):ℂ) • (fun _ => 1))+
        ((2*meanZ 1 1*Real.exp (-1):ℝ):ℂ) • centeredProbe exampleData 0 := by
    funext u
    simp [exampleNull,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [hf]
  rw [expectation_add,expectation_sub,expectation_smul,expectation_smul,expectation_one,
    expectation_centered,example_product_expectation]
  have he : Real.exp (-1)*Real.exp (-1)=Real.exp (-2) := by rw [← Real.exp_add]; norm_num
  rw [example_decay]
  change (((1-meanZ 1 1^2)*Real.exp (-1):ℝ):ℂ)-(2*meanZ 1 1*Real.exp (-2):ℝ)*(centered 1 1 x:ℂ)-
    (((1-meanZ 1 1^2)*Real.exp (-1):ℝ):ℂ)*1+
    (2*meanZ 1 1*Real.exp (-1):ℝ)*((Real.exp (-1):ℂ)*(centered 1 1 x:ℂ))=0
  have hc : (Real.exp (-1):ℂ)*(Real.exp (-1):ℂ)=(Real.exp (-2):ℂ) := by exact_mod_cast he
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  linear_combination 2*(meanZ 1 1:ℂ)*(centered 1 1 x:ℂ)*hc

theorem example_null : mk _ (positive exampleData) exampleNull=0 :=
  (null_iff exampleData exampleNull).mpr ⟨example_null_expectation 0,example_null_expectation 1⟩

theorem example_null_difference : exampleNull ![0,0]-exampleNull ![0,1]=(2*(1-meanZ 1 1):ℝ) := by
  norm_num [exampleNull,productProbe,centeredProbe,centered,sign,exampleData,GibbsUnitalHistory.exampleData]
  ring

theorem example_null_nonzero : exampleNull≠0 := by
  intro h
  have he := example_null_difference
  rw [h] at he
  simp only [Pi.zero_apply,sub_self] at he
  have hn : weights 1 1 0+weights 1 1 1=1 := by simpa only [Fin.sum_univ_two] using weights_sum 1 1
  have hw := weights_pos 1 1 1
  have hr : 0 < 2*(1-meanZ 1 1) := by unfold meanZ; linarith
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) he.symm

end SKEFTHawking.QuantumNetwork.GibbsCylinderHistory
