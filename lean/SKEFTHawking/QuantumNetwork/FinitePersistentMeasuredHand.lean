import SKEFTHawking.QuantumNetwork.FiniteClockControlledRetainedMemoryExamples

/-!
# Persistent measured hand

The hand is measured and retained. Every external intervention carries the full
22 public records and two internal data operators; no hand replacement is used.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FinitePersistentMeasuredHand
open Matrix FiniteInterventionProcess
open scoped BigOperators ComplexOrder Kronecker
abbrev A := FiniteClockControlledRetainedMemory.A
abbrev B := FiniteClockControlledRetainedMemory.B
abbrev S := FiniteClockControlledRetainedMemory.S
abbrev DataMat := FiniteClockControlledRetainedMemory.DataMat
abbrev JointMat := FiniteClockControlledRetainedMemory.JointMat
abbrev FullMat := FiniteClockControlledRetainedMemory.FullMat
abbrev ReducedMat := FiniteClockControlledRetainedMemory.ReducedMat
abbrev outcomeEquiv := FiniteClockControlledRetainedMemory.outcomeEquiv

def handOperator (ω ℏ t : ℝ) (a : A) : FiniteClockHandReadout.Mat := FiniteClockHandReadout.Q a * FiniteClockHandReadout.U ω ℏ t

def N (ω ℏ t : ℝ) (o : Fin 22) (c : Fin 2) : JointMat :=
  FiniteClockControlledRetainedMemory.dataKraus (outcomeEquiv.symm o).1 (outcomeEquiv.symm o).2 c ⊗ₖ
    handOperator ω ℏ t (outcomeEquiv.symm o).1

theorem hand_gram (ω ℏ t : ℝ) (a : A) :
    (handOperator ω ℏ t a)ᴴ * handOperator ω ℏ t a =
      (FiniteClockHandReadout.U ω ℏ t)ᴴ * FiniteClockHandReadout.Q a * FiniteClockHandReadout.U ω ℏ t := by
  simp only [handOperator, Matrix.conjTranspose_mul, FiniteClockHandReadout.Q_adjoint,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (FiniteClockHandReadout.Q a), FiniteClockHandReadout.Q_mul, if_pos rfl]

theorem arm_gram (ω ℏ t : ℝ) (a : A) :
    (∑ i : Fin 11, ∑ c : A,
      (FiniteClockControlledRetainedMemory.dataKraus a i c ⊗ₖ handOperator ω ℏ t a)ᴴ *
      (FiniteClockControlledRetainedMemory.dataKraus a i c ⊗ₖ handOperator ω ℏ t a)) =
      (1 : DataMat) ⊗ₖ ((FiniteClockHandReadout.U ω ℏ t)ᴴ * FiniteClockHandReadout.Q a * FiniteClockHandReadout.U ω ℏ t) := by
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hand_gram]
  have hs (T : Fin 11 → A → DataMat) (G : FiniteClockHandReadout.Mat) :
      (∑ i, ∑ c, T i c ⊗ₖ G) = (∑ i, ∑ c, T i c) ⊗ₖ G := by
    ext ⟨b,u⟩ ⟨d,w⟩
    simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul, add_mul]
  rw [hs, FiniteClockControlledRetainedMemory.data_normalized]

theorem N_normalized {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    (∑ o : Fin 22, ∑ c : Fin 2, (N ω ℏ t o c)ᴴ * N ω ℏ t o c) = 1 := by
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, N, Equiv.symm_apply_apply, arm_gram]
  have hs (G : A → FiniteClockHandReadout.Mat) :
      (∑ a, (1 : DataMat) ⊗ₖ G a) = (1 : DataMat) ⊗ₖ (∑ a, G a) := by
    ext ⟨b,u⟩ ⟨d,w⟩
    simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum, mul_add]
  have hu : (FiniteClockHandReadout.U ω ℏ t)ᴴ * FiniteClockHandReadout.U ω ℏ t = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (FiniteClockHandReadout.U_unitary hℏ ω t)
  rw [hs, ← Finset.sum_mul, ← Finset.mul_sum, FiniteClockHandReadout.Q_complete,
    Matrix.mul_one, hu, Matrix.one_kronecker_one]

def instrument (ω ℏ t : ℝ) (hℏ : ℏ ≠ 0) : FiniteInstrument S 22 where
  count := 2
  operators := N ω ℏ t
  normalized := N_normalized hℏ ω t

def step (F : Type*) [Fintype F] [DecidableEq F]
    (ω ℏ t : ℝ) (hℏ : ℏ ≠ 0) : Step S F 22 :=
  localStep S F 22 (instrument ω ℏ t hℏ)

variable (F : Type*) [Fintype F] [DecidableEq F]

theorem branch_positive {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (o : Fin 22)
    {Z : FullMat F} (hZ : Z.PosSemidef) :
    ((step F ω ℏ t hℏ).branch S F 22 o Z).PosSemidef :=
  Step.branch_posSemidef S F 22 _ o hZ

theorem branches_trace {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (Z : FullMat F) :
    (∑ o : Fin 22, ((step F ω ℏ t hℏ).branch S F 22 o Z).trace) = Z.trace :=
  Step.sum_trace S F 22 _ Z

theorem branches_density {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    {Z : FullMat F} (hZ : IsDensityOperator Z) :
    IsDensityOperator (∑ o, (step F ω ℏ t hℏ).branch S F 22 o Z) := by
  refine ⟨Matrix.posSemidef_sum _ (fun o _ => branch_positive F hℏ ω t o hZ.1), ?_⟩
  rw [Matrix.trace_sum, branches_trace, hZ.2]

/-- Rectangular compression on the middle hand, scaled from a projector column. -/
def C (ω ℏ t : ℝ) (a : A) : Matrix S B ℂ := fun z b =>
  (1 : DataMat) z.1 b * star (handOperator ω ℏ t a 1 z.2)

def extract (ω ℏ t : ℝ) (a : A) (Z : FullMat F) : ReducedMat F :=
  (2 : ℂ) • ((C ω ℏ t a ⊗ₖ (1 : Matrix F F ℂ))ᴴ * Z *
    (C ω ℏ t a ⊗ₖ (1 : Matrix F F ℂ)))

theorem extract_positive (ω ℏ t : ℝ) (a : A) {Z : FullMat F}
    (hZ : Z.PosSemidef) : (extract F ω ℏ t a Z).PosSemidef :=
  (hZ.conjTranspose_mul_mul_same _).smul (by norm_num : (0 : ℂ) ≤ 2)

theorem extract_entry (ω ℏ t : ℝ) (a : A) (Z : FullMat F) (bf dg : B × F) :
    extract F ω ℏ t a Z bf dg =
      2 * ∑ r : A, ∑ s : A, handOperator ω ℏ t a 1 r *
        Z ((bf.1,r),bf.2) ((dg.1,s),dg.2) * star (handOperator ω ℏ t a 1 s) := by
  simp [extract, C, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite, mul_assoc]
  ring

/-- Rank-one row identity is independent of the input matrix and the phase. -/
theorem hand_rank_one (ω ℏ t : ℝ) (a u w r s : A) :
    handOperator ω ℏ t a u r * star (handOperator ω ℏ t a w s) =
      2 * handOperator ω ℏ t a 1 r * star (handOperator ω ℏ t a 1 s) *
        FiniteClockHandReadout.Q a u w := by
  fin_cases a <;> fin_cases u <;> fin_cases w <;>
    simp [handOperator, FiniteClockHandReadout.Q, Matrix.mul_apply,
      Fin.sum_univ_two, star_add, star_mul] <;> ring

/-- Unnormalized rank-one insertion; the factor two restores Q_a. -/
def J (a : A) : Matrix S B ℂ := fun z b =>
  (1 : DataMat) z.1 b * FiniteClockHandReadout.Q a z.2 1

theorem hand_row (ω ℏ t : ℝ) (a u r : A) :
    handOperator ω ℏ t a u r =
      2 * FiniteClockHandReadout.Q a u 1 * handOperator ω ℏ t a 1 r := by
  fin_cases a <;> fin_cases u <;>
    simp [handOperator, FiniteClockHandReadout.Q, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem operator_factor (ω ℏ t : ℝ) (a : A) (T : DataMat) :
    T ⊗ₖ handOperator ω ℏ t a = (2 : ℂ) • (J a * T * (C ω ℏ t a)ᴴ) := by
  ext ⟨b,u⟩ ⟨d,w⟩
  simp [J, C, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, hand_row ω ℏ t a u w, apply_ite, eq_comm]
  ring

theorem insertion_factor (a : A) (Y : ReducedMat F) :
    (2 : ℂ) • ((J a ⊗ₖ (1 : Matrix F F ℂ)) * Y *
      (J a ⊗ₖ (1 : Matrix F F ℂ))ᴴ) =
      FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a) := by
  ext ⟨⟨b,u⟩,f⟩ ⟨⟨d,w⟩,g⟩
  simp [J, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite,
    FiniteClockControlledRetainedMemory.insert]
  fin_cases a <;> fin_cases u <;> fin_cases w <;>
    norm_num [FiniteClockHandReadout.Q] <;> ring_nf <;>
    simp only [starRingEnd_apply, star_ofNat] <;> ring

theorem actual_sandwich (ω ℏ t : ℝ) (a : A) (T : DataMat) (Z : FullMat F) :
    ((T ⊗ₖ handOperator ω ℏ t a) ⊗ₖ (1 : Matrix F F ℂ)) * Z *
      ((T ⊗ₖ handOperator ω ℏ t a) ⊗ₖ (1 : Matrix F F ℂ))ᴴ =
      FiniteClockControlledRetainedMemory.insert F
        ((T ⊗ₖ (1 : Matrix F F ℂ)) * extract F ω ℏ t a Z *
          (T ⊗ₖ (1 : Matrix F F ℂ))ᴴ) (FiniteClockHandReadout.Q a) := by
  have hl : ((J a * T * (C ω ℏ t a)ᴴ) ⊗ₖ (1 : Matrix F F ℂ)) =
      (J a ⊗ₖ (1 : Matrix F F ℂ)) * (T ⊗ₖ (1 : Matrix F F ℂ)) *
        (C ω ℏ t a ⊗ₖ (1 : Matrix F F ℂ))ᴴ := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [operator_factor, Matrix.smul_kronecker, hl, ← insertion_factor F a]
  simp only [extract, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.mul_assoc, map_ofNat]
  norm_num

/-- The exact branch identity holds on every complex correlated full input. -/
theorem branch_action {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (i : Fin 11)
    (Z : FullMat F) :
    (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z =
      FiniteClockControlledRetainedMemory.insert F
        (FiniteClockControlledRetainedMemory.dataBranch F a i (extract F ω ℏ t a Z))
        (FiniteClockHandReadout.Q a) := by
  rw [step, localStep_branch]
  simp only [instrument, FiniteInstrument.branch, FiniteInstrument.lift, krausMap,
    N, Equiv.symm_apply_apply]
  simp only [actual_sandwich, ← FiniteClockControlledRetainedMemory.insert_sum]
  rfl

/-- The next measured label depends on the previous measured label. -/
def transition (ω t : ℝ) (next previous : A) : ℝ :=
  if next=previous then 1-FiniteClockHandReadout.p ω t else FiniteClockHandReadout.p ω t

theorem transition_nonneg (ω t : ℝ) (b a : A) : 0 ≤ transition ω t b a := by
  unfold transition
  split
  · exact sub_nonneg.mpr (FiniteClockHandReadout.p_le_one ω t)
  · exact FiniteClockHandReadout.p_nonneg ω t

theorem transition_sum (ω t : ℝ) (a : A) : (∑ b : A, transition ω t b a) = 1 := by
  fin_cases a <;> simp [transition, Fin.sum_univ_two]

theorem hand_sandwich {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (b a : A) :
    handOperator ω ℏ t b * FiniteClockHandReadout.Q a * (handOperator ω ℏ t b)ᴴ =
      (transition ω t b a : ℂ) • FiniteClockHandReadout.Q b := by
  have hfirst : handOperator ω ℏ t b * FiniteClockHandReadout.Q 1 *
      (handOperator ω ℏ t b)ᴴ =
        (FiniteClockHandReadout.mass ω t b : ℂ) • FiniteClockHandReadout.Q b := by
    simpa only [handOperator, Matrix.conjTranspose_mul, FiniteClockHandReadout.Q_adjoint,
      Matrix.mul_assoc, FiniteClockHandReadout.rho, FiniteClockHandReadout.rhoPlus_eq] using
      FiniteClockHandReadout.sandwich hℏ ω t b
  have hu : FiniteClockHandReadout.U ω ℏ t * (FiniteClockHandReadout.U ω ℏ t)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp (FiniteClockHandReadout.U_unitary hℏ ω t)
  have hall : handOperator ω ℏ t b * 1 * (handOperator ω ℏ t b)ᴴ =
      FiniteClockHandReadout.Q b := by
    simp only [handOperator, Matrix.conjTranspose_mul, FiniteClockHandReadout.Q_adjoint,
      Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (FiniteClockHandReadout.U ω ℏ t), hu, Matrix.one_mul,
      FiniteClockHandReadout.Q_mul, if_pos rfl]
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
  · have hzero : FiniteClockHandReadout.Q 0 = 1-FiniteClockHandReadout.Q 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [FiniteClockHandReadout.Q, Matrix.one_apply]
    rw [hzero, Matrix.mul_sub, Matrix.sub_mul, hall, hfirst]
    fin_cases b <;> ext i j <;>
      simp [transition, FiniteClockHandReadout.mass] <;> push_cast <;> ring
  · rw [hfirst]
    fin_cases b <;> simp [transition, FiniteClockHandReadout.mass]

theorem extract_insert {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (b a : A) (Y : ReducedMat F) :
    extract F ω ℏ t b
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) =
      (transition ω t b a : ℂ) • Y := by
  ext bf dg
  rw [extract_entry]
  have he : (2 : ℂ) * (∑ r : A, ∑ s : A,
      handOperator ω ℏ t b 1 r *
        FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)
          ((bf.1,r),bf.2) ((dg.1,s),dg.2) * star (handOperator ω ℏ t b 1 s)) =
      Y bf dg * (2 * (handOperator ω ℏ t b * FiniteClockHandReadout.Q a *
        (handOperator ω ℏ t b)ᴴ) 1 1) := by
    simp [FiniteClockControlledRetainedMemory.insert, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two]
    ring
  rw [he, hand_sandwich hℏ]
  fin_cases b <;> simp [FiniteClockHandReadout.Q] <;> ring

theorem insert_smul (c : ℂ) (Y : ReducedMat F) (Q : FiniteClockHandReadout.Mat) :
    FiniteClockControlledRetainedMemory.insert F (c • Y) Q =
      c • FiniteClockControlledRetainedMemory.insert F Y Q := by
  ext x y
  simp [FiniteClockControlledRetainedMemory.insert, mul_assoc]

theorem branch_posterior {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (b a : A) (i : Fin 11)
    (Y : ReducedMat F) :
    (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) =
      (transition ω t b a : ℂ) • FiniteClockControlledRetainedMemory.insert F
        (FiniteClockControlledRetainedMemory.dataBranch F b i Y) (FiniteClockHandReadout.Q b) := by
  rw [branch_action, extract_insert F hℏ]
  simp only [FiniteClockControlledRetainedMemory.dataBranch, krausMap_smul, insert_smul]

def phase (θ : ℝ) : ℂ := Complex.exp (-Complex.I * θ)
def sign (a : A) : ℂ := if a=0 then -1 else 1

theorem phase_star (θ : ℝ) : star (phase θ) = Complex.exp (Complex.I * θ) := by
  unfold phase
  rw [← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem phase_mul_star (θ : ℝ) : phase θ * star (phase θ) = 1 := by
  rw [phase_star, phase, ← Complex.exp_add]
  simp

theorem hand_row_entry {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a r : A) :
    handOperator ω ℏ t a 1 r = if r=0 then sign a/2 else phase (ω*t)/2 := by
  fin_cases a <;> fin_cases r <;>
    simp [handOperator, FiniteClockHandReadout.U_diagonal hℏ, FiniteClockHandReadout.Q,
      Matrix.mul_apply, Fin.sum_univ_two, sign, phase] <;> push_cast <;> ring

/-- Both coherent cross blocks remain in the first extraction. -/
theorem extract_phase {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (Z : FullMat F)
    (bf dg : B × F) :
    extract F ω ℏ t a Z bf dg =
      (Z ((bf.1,0),bf.2) ((dg.1,0),dg.2) + Z ((bf.1,1),bf.2) ((dg.1,1),dg.2) +
        sign a * Complex.exp (Complex.I*(ω*t)) * Z ((bf.1,0),bf.2) ((dg.1,1),dg.2) +
        sign a * Complex.exp (-Complex.I*(ω*t)) * Z ((bf.1,1),bf.2) ((dg.1,0),dg.2))/2 := by
  rw [extract_entry]
  simp only [Fin.sum_univ_two, hand_row_entry hℏ, if_pos rfl,
    show (1:A) ≠ 0 by decide, if_false, ite_true, star_div₀, star_ofNat, phase_star]
  have hp := phase_mul_star (ω*t)
  rw [phase_star] at hp
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
  all_goals
    norm_num [sign]
    unfold phase at *
    push_cast at *
    simp only [neg_mul, mul_assoc] at *
    linear_combination (Z ((bf.1,1),bf.2) ((dg.1,1),dg.2)/2)*hp

theorem extract_sum {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (Z : FullMat F) :
    (∑ a : A, extract F ω ℏ t a Z) = FiniteClockControlledRetainedMemory.handTrace F Z := by
  ext bf dg
  simp [Matrix.sum_apply, Fin.sum_univ_two, extract_phase F hℏ,
    sign, FiniteClockControlledRetainedMemory.handTrace]
  ring

theorem extract_sum_trace {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (Z : FullMat F) :
    (∑ a : A, (extract F ω ℏ t a Z).trace) = Z.trace := by
  rw [← Matrix.trace_sum, extract_sum F hℏ,
    FiniteClockControlledRetainedMemory.handTrace_trace]

theorem arm_trace {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (Z : FullMat F) :
    (∑ i : Fin 11, ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z).trace) =
      (extract F ω ℏ t a Z).trace := by
  simp only [branch_action, FiniteClockControlledRetainedMemory.insert_trace,
    FiniteClockHandReadout.Q_trace, mul_one,
    FiniteClockControlledRetainedMemory.dataBranch_sum_trace]

abbrev Duration := FiniteClockControlledRetainedMemory.Duration
abbrev Policy := FiniteClockControlledRetainedMemory.Policy

def policyTree (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) : {n : ℕ} → Policy n → Tree S F 22 n
  | 0, .done => .done
  | _+1, .node t next => .node (step F ω ℏ t hℏ) (fun o => policyTree ω ℏ hℏ (next o))

/-- Recurrence begins only after a measured label exists; it retains every micro-record. -/
def posteriorRun (ω : ℝ) : {n : ℕ} → Policy n → History 22 n → A → ReducedMat F → FullMat F
  | 0, .done, _, a, Y => FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)
  | _+1, .node t next, (o,h), a, Y =>
      (transition ω t (outcomeEquiv.symm o).1 a : ℂ) •
        posteriorRun ω (next o) h (outcomeEquiv.symm o).1
          (FiniteClockControlledRetainedMemory.dataBranch F (outcomeEquiv.symm o).1
            (outcomeEquiv.symm o).2 Y)

theorem run_posterior {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) {n : ℕ} (P : Policy n)
    (h : History 22 n) (a : A) (Y : ReducedMat F) :
    run S F 22 (policyTree F ω ℏ hℏ P) h
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) =
      posteriorRun F ω P h a Y := by
  induction P generalizing a Y with
  | done => rfl
  | @node n t next ih =>
    rcases h with ⟨o,h⟩
    obtain ⟨⟨b,i⟩,rfl⟩ := outcomeEquiv.surjective o
    change run S F 22 (policyTree F ω ℏ hℏ (next (outcomeEquiv (b,i)) )) h
      ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (b,i))
        (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a))) = _
    rw [branch_posterior F hℏ, run_smul, ih]
    simp only [posteriorRun, Equiv.symm_apply_apply]

/-- The first step compresses the arbitrary full input; later steps use the posterior law. -/
theorem run_first {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω : ℝ) {n : ℕ} (t : Duration)
    (next : Fin 22 → Policy n) (a : A) (i : Fin 11) (h : History 22 n) (Z : FullMat F) :
    run S F 22 (policyTree F ω ℏ hℏ (.node t next)) (outcomeEquiv (a,i),h) Z =
      posteriorRun F ω (next (outcomeEquiv (a,i))) h a
        (FiniteClockControlledRetainedMemory.dataBranch F a i (extract F ω ℏ t a Z)) := by
  change run S F 22 (policyTree F ω ℏ hℏ (next (outcomeEquiv (a,i)))) h
    ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z) = _
  rw [branch_action, run_posterior]

theorem zero_depth (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) (Z : FullMat F) :
    run S F 22 (policyTree F ω ℏ hℏ .done) () Z = Z := rfl

end SKEFTHawking.QuantumNetwork.FinitePersistentMeasuredHand
