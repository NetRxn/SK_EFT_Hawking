import SKEFTHawking.QuantumNetwork.FiniteClockHandReadout
import SKEFTHawking.QuantumNetwork.FiniteQutritRetainedClock
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveReadoutRobustness

/-!
# A fresh hand controlling retained parity or parity reset

The public outcomes retain the hand label and every original eleven-way record.
The internal indices retain both the old reset index and hand-discard index.
The spectator may be any finite type, including the empty algebraic carrier.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteClockControlledRetainedMemory
open Matrix FiniteInterventionProcess
open scoped BigOperators ComplexOrder Kronecker
abbrev A := Fin 2
abbrev B := FiniteQutritRetainedClock.Joint
abbrev S := B × A
abbrev DataMat := Matrix B B ℂ
abbrev JointMat := Matrix S S ℂ

def outcomeEquiv : (A × Fin 11) ≃ Fin 22 := finProdFinEquiv
def internalEquiv : (A × A) ≃ Fin 4 := finProdFinEquiv

def dataKraus (a : A) (i : Fin 11) (c : A) : DataMat :=
  if a=0 then (if c=0 then FiniteQutritRetainedClock.K i else 0) else FiniteQutritRetainedClock.K i * FiniteQutritRetainedClock.L c

theorem data_normalized (a : A) :
    (∑ i : Fin 11, ∑ c : A, (dataKraus a i c)ᴴ * dataKraus a i c) = 1 := by
  fin_cases a
  · simpa [dataKraus, Fin.sum_univ_two, IsKrausChannel] using FiniteQutritRetainedClock.K_normalized
  · have h (c : A) :
        (∑ i : Fin 11, (FiniteQutritRetainedClock.K i * FiniteQutritRetainedClock.L c)ᴴ * (FiniteQutritRetainedClock.K i * FiniteQutritRetainedClock.L c)) = (FiniteQutritRetainedClock.L c)ᴴ * FiniteQutritRetainedClock.L c := by
      calc
        _ = (FiniteQutritRetainedClock.L c)ᴴ *
            (∑ i : Fin 11, (FiniteQutritRetainedClock.K i)ᴴ * FiniteQutritRetainedClock.K i) *
            FiniteQutritRetainedClock.L c := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Finset.mul_sum, Finset.sum_mul]
        _ = _ := by rw [FiniteQutritRetainedClock.K_normalized, Matrix.mul_one]
    change (∑ i : Fin 11, ∑ c : A, (FiniteQutritRetainedClock.K i * FiniteQutritRetainedClock.L c)ᴴ *
      (FiniteQutritRetainedClock.K i * FiniteQutritRetainedClock.L c)) = 1
    rw [Finset.sum_comm]
    simp only [h]
    exact FiniteQutritRetainedClock.L_normalized

theorem data_action_keep (X : DataMat) :
    (∑ i : Fin 11, krausMap (dataKraus 0 i) X) = FiniteQutritRetainedClock.J X := by
  simp [krausMap, dataKraus, Fin.sum_univ_two, FiniteQutritRetainedClock.J]

theorem data_action_reset (X : DataMat) :
    (∑ i : Fin 11, krausMap (dataKraus 1 i) X) = FiniteQutritRetainedClock.J (FiniteQutritRetainedClock.resetClock X) := by
  rw [← FiniteQutritRetainedClock.reset_kraus_action]
  simp only [FiniteQutritRetainedClock.J, LinearMap.coe_mk, AddHom.coe_mk, krausMap,
    dataKraus, show (1 : A) ≠ 0 by decide, if_false, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

def M (ω ℏ t : ℝ) (a : Fin 22) (k : Fin 4) : JointMat :=
  dataKraus (outcomeEquiv.symm a).1 (outcomeEquiv.symm a).2 (internalEquiv.symm k).1 ⊗ₖ
    FiniteClockHandReadout.g ω ℏ t (outcomeEquiv.symm a).1 (internalEquiv.symm k).2

theorem hand_gram {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    (∑ r : A, (FiniteClockHandReadout.g ω ℏ t a r)ᴴ * FiniteClockHandReadout.g ω ℏ t a r) =
      (FiniteClockHandReadout.mass ω t a : ℂ) • 1 := by
  ext i j
  let X : FiniteClockHandReadout.Mat := Matrix.single j i 1
  have h := congrArg Matrix.trace (FiniteClockHandReadout.g_sandwich hℏ ω t a X)
  have he : (∑ r : A, (FiniteClockHandReadout.g ω ℏ t a r)ᴴ *
      FiniteClockHandReadout.g ω ℏ t a r) i j =
      (∑ r : A, FiniteClockHandReadout.g ω ℏ t a r * X *
        (FiniteClockHandReadout.g ω ℏ t a r)ᴴ).trace := by
    fin_cases i <;> fin_cases j <;>
      simp [X, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Matrix.single] <;> ring
  rw [he, h]
  simp only [Matrix.trace_smul, FiniteClockHandReadout.Q_trace, smul_eq_mul, mul_one]
  fin_cases i <;> fin_cases j <;> norm_num [X, Matrix.single, Matrix.trace,
    Fin.sum_univ_two, Matrix.one_apply]

private theorem sum_kron_right {κ : Type*} [Fintype κ]
    (T : DataMat) (G : κ → FiniteClockHandReadout.Mat) :
    (∑ k, T ⊗ₖ G k) = T ⊗ₖ (∑ k, G k) := by
  ext ⟨b,u⟩ ⟨d,w⟩
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]

private theorem sum_kron_left {κ : Type*} [Fintype κ]
    (T : κ → DataMat) (G : FiniteClockHandReadout.Mat) :
    (∑ k, T k ⊗ₖ G) = (∑ k, T k) ⊗ₖ G := by
  ext ⟨b,u⟩ ⟨d,w⟩
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

theorem arm_normalized {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    (∑ i : Fin 11, ∑ c : A, ∑ r : A,
      (dataKraus a i c ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r)ᴴ *
      (dataKraus a i c ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r)) =
      (FiniteClockHandReadout.mass ω t a : ℂ) • (1 : JointMat) := by
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    sum_kron_right, hand_gram hℏ, sum_kron_left]
  rw [data_normalized]
  ext ⟨b,u⟩ ⟨d,w⟩
  by_cases hb : b=d <;> by_cases hu : u=w <;> simp [Matrix.one_apply, hb, hu]

theorem M_normalized {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) :
    (∑ a : Fin 22, ∑ k : Fin 4, (M ω ℏ t a k)ᴴ * M ω ℏ t a k) = 1 := by
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  have h (a : A) (i : Fin 11) :
      (∑ k : Fin 4, (M ω ℏ t (outcomeEquiv (a,i)) k)ᴴ *
        M ω ℏ t (outcomeEquiv (a,i)) k) =
      ∑ c : A, ∑ r : A,
        (dataKraus a i c ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r)ᴴ *
        (dataKraus a i c ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r) := by
    rw [← internalEquiv.sum_comp]
    simp [M, Fintype.sum_prod_type]
  simp only [h, arm_normalized hℏ, ← Finset.sum_smul]
  have hm : (∑ a : A, (FiniteClockHandReadout.mass ω t a : ℂ)) = 1 := by
    exact_mod_cast FiniteClockHandReadout.mass_sum ω t
  rw [hm, one_smul]

def instrument (ω ℏ t : ℝ) (hℏ : ℏ ≠ 0) : FiniteInstrument S 22 where
  count := 4
  operators := M ω ℏ t
  normalized := M_normalized hℏ ω t

def step (F : Type*) [Fintype F] [DecidableEq F]
    (ω ℏ t : ℝ) (hℏ : ℏ ≠ 0) : Step S F 22 :=
  localStep S F 22 (instrument ω ℏ t hℏ)

/-- Rectangular isometry selecting a hand coordinate on the actual middle factor. -/
def W (r : A) : Matrix S B ℂ := fun z b =>
  (1 : DataMat) z.1 b * if z.2=r then 1 else 0

theorem W_isometry (r : A) : (W r)ᴴ * W r = 1 := by
  ext b d
  fin_cases r <;> simp [W, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, eq_comm]

theorem W_complete : (∑ r : A, W r * (W r)ᴴ) = 1 := by
  ext ⟨b,a⟩ ⟨d,c⟩
  fin_cases a <;> fin_cases c <;>
    simp [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.one_apply, eq_comm]

variable (F : Type*) [Fintype F] [DecidableEq F]
abbrev FullMat := Matrix (S × F) (S × F) ℂ
abbrev ReducedMat := Matrix (B × F) (B × F) ℂ

/-- Permute the middle hand past the spectator, preserving both data coordinates. -/
def handSpectatorEquiv : ((B × F) × A) ≃ ((B × A) × F) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def handTrace (Z : FullMat F) : ReducedMat F :=
  fun bf dg => ∑ r : A, Z ((bf.1,r),bf.2) ((dg.1,r),dg.2)

def insert (Y : ReducedMat F) (Q : FiniteClockHandReadout.Mat) : FullMat F :=
  fun z w => Y (z.1.1,z.2) (w.1.1,w.2) * Q z.1.2 w.1.2

theorem insert_reindex (Y : ReducedMat F) (Q : FiniteClockHandReadout.Mat) :
    insert F Y Q = (Y ⊗ₖ Q).submatrix (handSpectatorEquiv F).symm (handSpectatorEquiv F).symm := rfl

theorem handTrace_rectangular (Z : FullMat F) :
    handTrace F Z = ∑ r : A,
      (W r ⊗ₖ (1 : Matrix F F ℂ))ᴴ * Z * (W r ⊗ₖ (1 : Matrix F F ℂ)) := by
  ext ⟨b,f⟩ ⟨d,g⟩
  simp [handTrace, W, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Matrix.sum_apply, apply_ite]

theorem handTrace_positive {Z : FullMat F} (hZ : Z.PosSemidef) :
    (handTrace F Z).PosSemidef := by
  rw [handTrace_rectangular]
  exact Matrix.posSemidef_sum _ (fun _ _ => hZ.conjTranspose_mul_mul_same _)

theorem handTrace_trace (Z : FullMat F) : (handTrace F Z).trace = Z.trace := by
  rw [handTrace_rectangular]
  simp only [Matrix.trace_sum]
  have hc : ∀ r : A, (((W r ⊗ₖ (1 : Matrix F F ℂ))ᴴ * Z *
      (W r ⊗ₖ (1 : Matrix F F ℂ))).trace) =
      ((W r ⊗ₖ (1 : Matrix F F ℂ)) * (W r ⊗ₖ (1 : Matrix F F ℂ))ᴴ * Z).trace :=
    fun _ => Matrix.trace_mul_cycle _ _ _
  simp only [hc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  have hn : (∑ r : A, (W r ⊗ₖ (1 : Matrix F F ℂ)) *
      (W r ⊗ₖ (1 : Matrix F F ℂ))ᴴ) = 1 := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronOne_general, W_complete, Matrix.one_kronecker_one]
  rw [hn, Matrix.one_mul]

theorem insert_trace (Y : ReducedMat F) (Q : FiniteClockHandReadout.Mat) :
    (insert F Y Q).trace = Y.trace * Q.trace := by
  rw [insert_reindex, Matrix.trace_submatrix, Matrix.trace_kronecker]

def handVector (ω ℏ t : ℝ) (a : A) : A → ℂ :=
  (FiniteClockHandReadout.Q a * FiniteClockHandReadout.U ω ℏ t).mulVec FiniteClockHandReadout.v

theorem hand_operator_entry (ω ℏ t : ℝ) (a r u w : A) :
    FiniteClockHandReadout.g ω ℏ t a r u w = if w=r then handVector ω ℏ t a u else 0 := by
  unfold FiniteClockHandReadout.g
  rw [Matrix.mul_apply]
  fin_cases r <;> fin_cases w <;>
    simp [FiniteClockHandReadout.R, handVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem handVector_outer {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) :
    Matrix.vecMulVec (handVector ω ℏ t a) (star (handVector ω ℏ t a)) =
      (FiniteClockHandReadout.mass ω t a : ℂ) • FiniteClockHandReadout.Q a := by
  have h := FiniteClockHandReadout.g_sandwich hℏ ω t a (Matrix.single 0 0 1)
  ext u w
  have he := congrFun (congrFun h u) w
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hand_operator_entry,
    Fin.sum_univ_two, Matrix.single, Matrix.trace, Matrix.vecMulVec] using he

def handBlock (Z : JointMat) (r : A) : DataMat := fun b d => Z (b,r) (d,r)

theorem selected_sandwich {D : Type*} [Fintype D] [DecidableEq D]
    (ω ℏ t : ℝ) (a r : A) (T : Matrix D D ℂ) (Z : Matrix (D × A) (D × A) ℂ) :
    (T ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r) * Z *
      (T ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r)ᴴ =
      (T * Matrix.of (fun b d => Z (b,r) (d,r)) * Tᴴ) ⊗ₖ
        Matrix.vecMulVec (handVector ω ℏ t a) (star (handVector ω ℏ t a)) := by
  ext ⟨b,u⟩ ⟨d,w⟩
  fin_cases r <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      hand_operator_entry, Fin.sum_univ_two, Matrix.vecMulVec,
      Finset.sum_mul, Finset.mul_sum]
  all_goals
    apply Finset.sum_congr rfl
    intro b' _
    apply Finset.sum_congr rfl
    intro d' _
    ring

theorem discarded_sandwich {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A)
    (T : DataMat) (Z : JointMat) :
    (∑ r : A, (T ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r) * Z *
      (T ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r)ᴴ) =
      (FiniteClockHandReadout.mass ω t a : ℂ) •
        ((T * (handBlock Z 0 + handBlock Z 1) * Tᴴ) ⊗ₖ FiniteClockHandReadout.Q a) := by
  simp only [selected_sandwich, handVector_outer hℏ, Fin.sum_univ_two]
  have hb (r : A) : Matrix.of (fun b d => Z (b,r) (d,r)) = handBlock Z r := rfl
  simp only [hb]
  ext ⟨b,u⟩ ⟨d,w⟩
  simp [Matrix.mul_add, Matrix.add_mul]
  ring

def baseBranch (ω ℏ t : ℝ) (a : A) (i : Fin 11) (Z : JointMat) : JointMat :=
  ∑ c : A, ∑ r : A,
    (dataKraus a i c ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r) * Z *
      (dataKraus a i c ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r)ᴴ

theorem baseBranch_action {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A)
    (i : Fin 11) (Z : JointMat) :
    baseBranch ω ℏ t a i Z = (FiniteClockHandReadout.mass ω t a : ℂ) •
      (krausMap (dataKraus a i) (handBlock Z 0 + handBlock Z 1) ⊗ₖ FiniteClockHandReadout.Q a) := by
  simp only [baseBranch, discarded_sandwich hℏ, ← Finset.smul_sum,
    sum_kron_left, krausMap]

def fullBlock (Z : FullMat F) (f g : F) : JointMat := fun b d => Z (b,f) (d,g)
def dataBlock (Y : ReducedMat F) (f g : F) : DataMat := fun b d => Y (b,f) (d,g)

theorem lifted_sandwich_block (T : JointMat) (Z : FullMat F) (f g : F) :
    fullBlock F ((T ⊗ₖ (1 : Matrix F F ℂ)) * Z * (T ⊗ₖ (1 : Matrix F F ℂ))ᴴ) f g =
      T * fullBlock F Z f g * Tᴴ := by
  ext b d
  simp [fullBlock, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

theorem step_branch_block {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A)
    (i : Fin 11) (Z : FullMat F) (f g : F) :
    fullBlock F ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z) f g =
      baseBranch ω ℏ t a i (fullBlock F Z f g) := by
  rw [step, localStep_branch]
  change fullBlock F (∑ k : Fin 4,
    (M ω ℏ t (outcomeEquiv (a,i)) k ⊗ₖ (1 : Matrix F F ℂ)) * Z *
      (M ω ℏ t (outcomeEquiv (a,i)) k ⊗ₖ (1 : Matrix F F ℂ))ᴴ) f g = _
  rw [← internalEquiv.sum_comp]
  ext b d
  simp only [Fintype.sum_prod_type, Matrix.sum_apply, fullBlock,
    baseBranch, M, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro r _
  exact congrFun (congrFun (lifted_sandwich_block F
    (dataKraus a i c ⊗ₖ FiniteClockHandReadout.g ω ℏ t a r) Z f g) b) d

def dataBranch (a : A) (i : Fin 11) (Y : ReducedMat F) : ReducedMat F :=
  krausMap (fun c => dataKraus a i c ⊗ₖ (1 : Matrix F F ℂ)) Y

theorem dataBranch_block (a : A) (i : Fin 11) (Y : ReducedMat F) (f g : F) :
    dataBlock F (dataBranch F a i Y) f g = krausMap (dataKraus a i) (dataBlock F Y f g) := by
  ext b d
  simp [dataBlock, dataBranch, krausMap, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

theorem handTrace_block (Z : FullMat F) (f g : F) :
    dataBlock F (handTrace F Z) f g =
      handBlock (fullBlock F Z f g) 0 + handBlock (fullBlock F Z f g) 1 := by
  ext b d
  simp [dataBlock, handTrace, handBlock, fullBlock, Fin.sum_univ_two]

/-- Ambient identity on every complex correlated input, with no positivity premise. -/
theorem branch_action {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (i : Fin 11)
    (Z : FullMat F) :
    (step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z =
      (FiniteClockHandReadout.mass ω t a : ℂ) •
        insert F (dataBranch F a i (handTrace F Z)) (FiniteClockHandReadout.Q a) := by
  ext ⟨⟨b,u⟩,f⟩ ⟨⟨d,w⟩,g⟩
  have h := step_branch_block F hℏ ω t a i Z f g
  rw [baseBranch_action hℏ] at h
  have hc := dataBranch_block F a i (handTrace F Z) f g
  rw [handTrace_block] at hc
  have he := congrFun (congrFun h (b,u)) (d,w)
  simpa only [fullBlock, insert, Matrix.smul_apply, smul_eq_mul,
    Matrix.kronecker_apply, ← hc, dataBlock] using he

theorem insert_positive {Y : ReducedMat F} {Q : FiniteClockHandReadout.Mat}
    (hY : Y.PosSemidef) (hQ : Q.PosSemidef) : (insert F Y Q).PosSemidef := by
  rw [insert_reindex]
  exact (hY.kronecker hQ).submatrix _

def dataInstrument (a : A) : FiniteInstrument B 11 where
  count := 2
  operators := dataKraus a
  normalized := data_normalized a

theorem dataBranch_positive (a : A) (i : Fin 11) {Y : ReducedMat F} (hY : Y.PosSemidef) :
    (dataBranch F a i Y).PosSemidef := krausMap_posSemidef _ hY

theorem dataBranch_sum_trace (a : A) (Y : ReducedMat F) :
    (∑ i : Fin 11, (dataBranch F a i Y).trace) = Y.trace :=
  ((dataInstrument a).lift F).sum_trace Y

theorem branch_positive {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (k : Fin 22)
    {Z : FullMat F} (hZ : Z.PosSemidef) :
    ((step F ω ℏ t hℏ).branch S F 22 k Z).PosSemidef :=
  Step.branch_posSemidef S F 22 _ k hZ

theorem branches_trace {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (Z : FullMat F) :
    (∑ k : Fin 22, ((step F ω ℏ t hℏ).branch S F 22 k Z).trace) = Z.trace :=
  Step.sum_trace S F 22 _ Z

private theorem traceNorm_real_smul {D : Type*} [Fintype D] [DecidableEq D]
    (c : ℝ) (X : Matrix D D ℂ) : traceNorm ((c:ℂ) • X) = |c| * traceNorm X := by
  by_cases hc : 0 ≤ c
  · rw [traceNorm_smul_nonneg hc, abs_of_nonneg hc]
  · have hn : 0 ≤ -c := by linarith
    have he : (c:ℂ) • X = -(((-c:ℝ):ℂ) • X) := by simp
    rw [he, traceNorm_neg, traceNorm_smul_nonneg hn, abs_of_neg (lt_of_not_ge hc)]

theorem branch_difference_norm {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ) (a : A) (i : Fin 11)
    {Z : FullMat F} (hZ : Z.PosSemidef) :
    traceNorm ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z -
      (step F ω ℏ s hℏ).branch S F 22 (outcomeEquiv (a,i)) Z) =
      |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| *
        (dataBranch F a i (handTrace F Z)).trace.re := by
  rw [branch_action, branch_action, ← sub_smul, ← Complex.ofReal_sub, traceNorm_real_smul]
  rw [traceNorm_posSemidef (insert_positive F
    (dataBranch_positive F a i (handTrace_positive F hZ)) (FiniteClockHandReadout.Q_density a).1)]
  rw [insert_trace, FiniteClockHandReadout.Q_trace, mul_one]
  congr 1
  fin_cases a <;> simp [FiniteClockHandReadout.mass, abs_sub_comm]

theorem stepDistance_exact {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ)
    {Z : FullMat F} (hZ : Z.PosSemidef) :
    FiniteAdaptiveMapPerturbation.stepDistance S F 22 (step F ω ℏ t hℏ) (step F ω ℏ s hℏ) Z =
      |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| * Z.trace.re := by
  unfold FiniteAdaptiveMapPerturbation.stepDistance
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, branch_difference_norm F hℏ ω t s _ _ hZ,
    ← Finset.mul_sum, ← Complex.re_sum, dataBranch_sum_trace, handTrace_trace, Fin.sum_univ_two]
  norm_num [Complex.mul_re]
  <;> ring

theorem localError_exact {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ) :
    FiniteAdaptiveMapPerturbation.LocalError S F 22 (step F ω ℏ t hℏ) (step F ω ℏ s hℏ)
      |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| := by
  refine ⟨abs_nonneg _, fun Z hZ => ?_⟩
  rw [stepDistance_exact F hℏ ω t s hZ.1, hZ.2, Complex.one_re, mul_one]

abbrev Duration := {t : ℝ // 0 ≤ t}

/-- Every node specifies a duration and every one of its twenty-two continuations. -/
inductive Policy : ℕ → Type
  | done : Policy 0
  | node {n : ℕ} (duration : Duration) (next : Fin 22 → Policy n) : Policy (n+1)

def policyTree (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) : {n : ℕ} → Policy n → Tree S F 22 n
  | 0, .done => .done
  | _+1, .node t next => .node (step F ω ℏ t hℏ) (fun a => policyTree ω ℏ hℏ (next a))

/-- This evaluates the duration at every chronological prefix, reachable or not. -/
def durationAt : {n : ℕ} → Policy n → (j : Fin n) → History 22 j.val → Duration
  | 0, .done, j, _ => Fin.elim0 j
  | _+1, .node t next, j, h =>
      Fin.cases (fun _ => t) (fun k h => durationAt (next h.1) k h.2) j h

inductive PolicyErrors (ω : ℝ) : {n : ℕ} → Policy n → Policy n → List ℝ → Prop
  | done : PolicyErrors ω .done .done []
  | node {n : ℕ} {t s : Duration} {P Q : Fin 22 → Policy n} {e : ℝ} {es : List ℝ}
      (bound : |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| ≤ e)
      (length : es.length = n) (next : ∀ a, PolicyErrors ω (P a) (Q a) es) :
      PolicyErrors ω (.node t P) (.node s Q) (e::es)

theorem policy_pairedErrors {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n} {es : List ℝ}
    (h : PolicyErrors ω P Q es) :
    FiniteAdaptiveMapPerturbation.PairedErrors S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q) es := by
  induction h with
  | done => exact .done
  | @node n t s P Q e es hb hlen hn ih =>
    apply FiniteAdaptiveMapPerturbation.PairedErrors.node
    · have hl := localError_exact F hℏ ω t s
      exact ⟨(abs_nonneg _).trans hb, fun Z hZ => (hl.2 Z hZ).trans hb⟩
    · exact hlen
    · exact ih

theorem policy_capped {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n} {es : List ℝ}
    (h : PolicyErrors ω P Q es) {X Y : FullMat F}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    FiniteAdaptiveMapPerturbation.outputDistance S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q) X Y ≤ min 1 (traceDist X Y+es.sum) :=
  FiniteAdaptiveMapPerturbation.pairedErrors_capped S F 22 (policy_pairedErrors F hℏ h) hX hY

def terminalProbability (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    (effect : History 22 n → FullMat F) (X : FullMat F) : ℝ :=
  ∑ h, (effect h * run S F 22 (policyTree F ω ℏ hℏ P) h X).trace.re

theorem policy_event_error {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n} {es : List ℝ}
    (h : PolicyErrors ω P Q es) {X Y : FullMat F}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (effect : History 22 n → FullMat F) (he : ∀ h, IsBinaryPOVM (effect h)) :
    |terminalProbability F ω ℏ hℏ P effect X-terminalProbability F ω ℏ hℏ Q effect Y| ≤
      min 1 (traceDist X Y+es.sum) := by
  have hb := FiniteAdaptiveReadoutRobustness.bounded_observable_difference
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ P) hX)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ Q) hY) effect he
  rw [FiniteAdaptiveReadoutRobustness.tree_branchDistance] at hb
  exact hb.trans (policy_capped F hℏ h hX hY)

theorem terminalProbability_mem {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    {X : FullMat F} (hX : IsDensityOperator X)
    (effect : History 22 n → FullMat F) (he : ∀ h, IsBinaryPOVM (effect h)) :
    terminalProbability F ω ℏ hℏ P effect X ∈ Set.Icc (0:ℝ) 1 := by
  let fam := fun h => run S F 22 (policyTree F ω ℏ hℏ P) h X
  have hf := FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ P) hX
  have hn := FiniteAdaptiveReadoutDiscrimination.effectTable_nonneg he hf
  have ht := FiniteAdaptiveReadoutDiscrimination.effectTable_total effect hf
  have h0 := Finset.sum_nonneg (fun h (_ : h ∈ Finset.univ) => hn h 0)
  have h1 := Finset.sum_nonneg (fun h (_ : h ∈ Finset.univ) => hn h 1)
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib] at ht
  simp only [FiniteAdaptiveReadoutDiscrimination.effectTable, if_pos rfl] at h0
  exact ⟨h0, by
    have hh : (∑ h, FiniteAdaptiveReadoutDiscrimination.effectTable effect
      (fun h => run S F 22 (policyTree F ω ℏ hℏ P) h X) h 0) =
        terminalProbability F ω ℏ hℏ P effect X := by
      simp [FiniteAdaptiveReadoutDiscrimination.effectTable, terminalProbability]
    rw [hh] at ht
    linarith⟩

theorem policy_falsePositive {ω ℏ α : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ}
    {P Q : Policy n} {es : List ℝ} (h : PolicyErrors ω P Q es) {X Y : FullMat F}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (effect : History 22 n → FullMat F) (he : ∀ h, IsBinaryPOVM (effect h))
    (hα : terminalProbability F ω ℏ hℏ P effect X ≤ α) :
    terminalProbability F ω ℏ hℏ Q effect Y ≤ min 1 (α+min 1 (traceDist X Y+es.sum)) := by
  refine le_min (terminalProbability_mem F hℏ Q hY effect he).2 ?_
  have hb := (abs_le.mp (policy_event_error F hℏ h hX hY effect he)).1
  linarith

theorem policy_optimalReadout_stability {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ}
    {PA PB QA QB : Policy n} {esA esB : List ℝ}
    (hA : PolicyErrors ω PA QA esA) (hB : PolicyErrors ω PB QB esB)
    {XA XB YA YB : FullMat F}
    (hXA : IsDensityOperator XA) (hXB : IsDensityOperator XB)
    (hYA : IsDensityOperator YA) (hYB : IsDensityOperator YB) :
    |FiniteAdaptiveReadoutRobustness.instrumentError
      (fun h => run S F 22 (policyTree F ω ℏ hℏ QA) h YA)
      (fun h => run S F 22 (policyTree F ω ℏ hℏ QB) h YB)
      (FiniteAdaptiveReadoutDiscrimination.optimalReadout
        (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ PA) hXA)
        (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ PB) hXB)) -
      (1-FiniteAdaptiveMapPerturbation.outputDistance S F 22
        (policyTree F ω ℏ hℏ PA) (policyTree F ω ℏ hℏ PB) XA XB)/2| ≤
      (min 1 (traceDist XA YA+esA.sum)+min 1 (traceDist XB YB+esB.sum))/2 := by
  have h := FiniteAdaptiveReadoutRobustness.transported_optimalReadout_stability
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ PA) hXA)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ PB) hXB)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ QA) hYA)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ QB) hYB)
  simp only [FiniteAdaptiveReadoutRobustness.tree_branchDistance] at h
  exact h.trans (div_le_div_of_nonneg_right
    (add_le_add (policy_capped F hℏ hA hXA hYA) (policy_capped F hℏ hB hXB hYB)) (by norm_num))

theorem handTrace_insert (Y : ReducedMat F) (Q : FiniteClockHandReadout.Mat) :
    handTrace F (insert F Y Q) = Q.trace • Y := by
  ext ⟨b,f⟩ ⟨d,g⟩
  simp [handTrace, insert, Matrix.trace, Fin.sum_univ_two]
  ring

theorem dataBranch_keep (i : Fin 11) (Y : ReducedMat F) :
    dataBranch F 0 i Y =
      (localStep B F 11 FiniteQutritRetainedClock.instrument).branch B F 11 i Y := by
  rw [FiniteQutritRetainedClock.record_branch]
  simp [dataBranch, dataKraus, krausMap, Fin.sum_univ_two]

theorem dataBranch_reset (i : Fin 11) (Y : ReducedMat F) :
    dataBranch F 1 i Y =
      (localStep B F 11 FiniteQutritRetainedClock.instrument).branch B F 11 i
        (krausMap (fun c => FiniteQutritRetainedClock.L c ⊗ₖ (1 : Matrix F F ℂ)) Y) := by
  rw [FiniteQutritRetainedClock.record_branch]
  simp only [dataBranch, dataKraus, show (1:A) ≠ 0 by decide, if_false,
    krausMap, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_one]
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_assoc]
  apply Finset.sum_congr rfl
  intro c _
  conv_rhs => rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem keep_branch {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (a : A) (i : Fin 11)
    (Z : FullMat F) :
    (step F ω ℏ (Real.pi/ω) hℏ).branch S F 22 (outcomeEquiv (a,i)) Z =
      if a=0 then insert F
        ((localStep B F 11 FiniteQutritRetainedClock.instrument).branch B F 11 i (handTrace F Z))
        (FiniteClockHandReadout.Q 0) else 0 := by
  rw [branch_action]
  fin_cases a <;> simp [FiniteClockHandReadout.mass, FiniteClockHandReadout.p_keep hω,
    dataBranch_keep]

def constantPolicy (t : Duration) : (n : ℕ) → Policy n
  | 0 => .done
  | n+1 => .node t (fun _ => constantPolicy t n)

def keepTree (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) : (n : ℕ) → Tree S F 22 n
  | 0 => .done
  | n+1 => .node (step F ω ℏ (Real.pi/ω) hℏ) (fun _ => keepTree ω ℏ hℏ n)

def injectRecord : (n : ℕ) → History 11 n → History 22 n
  | 0, _ => ()
  | n+1, (i,h) => (outcomeEquiv (0,i), injectRecord n h)

theorem injectRecord_injective (n : ℕ) : Function.Injective (injectRecord n) := by
  induction n with
  | zero => intro a b _; cases a; cases b; rfl
  | succ n ih =>
    rintro ⟨i,h⟩ ⟨j,k⟩ he
    have hhead := congrArg Prod.snd (outcomeEquiv.injective (congrArg Prod.fst he))
    have htail := ih (congrArg Prod.snd he)
    cases hhead; cases htail; rfl

/-- Positive depth discards the old hand; zero depth preserves arbitrary coherences. -/
theorem injected_run {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (n : ℕ)
    (h : History 11 (n+1)) (Z : FullMat F) :
    run S F 22 (keepTree F ω ℏ hℏ (n+1)) (injectRecord (n+1) h) Z =
      insert F (run B F 11 (FiniteQutritRetainedClock.recordTree F (n+1)) h (handTrace F Z))
        (FiniteClockHandReadout.Q 0) := by
  induction n generalizing Z with
  | zero =>
    rcases h with ⟨i,h⟩
    cases h
    exact keep_branch F hω hℏ 0 i Z
  | succ n ih =>
    rcases h with ⟨i,h⟩
    change run S F 22 (keepTree F ω ℏ hℏ (n+1)) (injectRecord (n+1) h)
      ((step F ω ℏ (Real.pi/ω) hℏ).branch S F 22 (outcomeEquiv (0,i)) Z) = _
    rw [ih, keep_branch F hω hℏ, if_pos rfl, handTrace_insert, FiniteClockHandReadout.Q_trace,
      one_smul]
    rfl

theorem keep_zero_depth (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) (Z : FullMat F) :
    run S F 22 (keepTree F ω ℏ hℏ 0) () Z = Z := rfl

theorem forbidden_run {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (n : ℕ)
    (h : History 22 n) (hn : h ∉ Set.range (injectRecord n)) (Z : FullMat F) :
    run S F 22 (keepTree F ω ℏ hℏ n) h Z = 0 := by
  induction n generalizing Z with
  | zero => exact False.elim (hn ⟨(),by cases h; rfl⟩)
  | succ n ih =>
    rcases h with ⟨k,h⟩
    obtain ⟨⟨a,i⟩,rfl⟩ := outcomeEquiv.surjective k
    fin_cases a
    · change run S F 22 (keepTree F ω ℏ hℏ n) h
        ((step F ω ℏ (Real.pi/ω) hℏ).branch S F 22 (outcomeEquiv (0,i)) Z) = 0
      apply ih
      rintro ⟨w,hw⟩
      exact hn ⟨(i,w), by simp [injectRecord, hw]⟩
    · change run S F 22 (keepTree F ω ℏ hℏ n) h
        ((step F ω ℏ (Real.pi/ω) hℏ).branch S F 22 (outcomeEquiv (1,i)) Z) = 0
      rw [keep_branch F hω hℏ, if_neg (by decide), run_zero]

theorem insert_sum {I : Type*} [Fintype I] (Y : I → ReducedMat F)
    (Q : FiniteClockHandReadout.Mat) :
    insert F (∑ i, Y i) Q = ∑ i, insert F (Y i) Q := by
  ext ⟨⟨b,u⟩,f⟩ ⟨⟨d,w⟩,g⟩
  simp [insert, Matrix.sum_apply, Finset.sum_mul]

theorem keep_all_records {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (n : ℕ) (Z : FullMat F) :
    (∑ h, run S F 22 (keepTree F ω ℏ hℏ (n+1)) h Z) =
      insert F (FiniteQutritRetainedClock.amplifiedJointIterate F (n+1) (handTrace F Z))
        (FiniteClockHandReadout.Q 0) := by
  rw [← FiniteQutritRetainedClock.all_records_sum, insert_sum]
  symm
  exact Fintype.sum_of_injective (injectRecord (n+1)) (injectRecord_injective (n+1)) _ _
    (fun h hn => forbidden_run F hω hℏ (n+1) h hn Z)
    (fun h => (injected_run F hω hℏ n h Z).symm)

theorem keep_reduced_records {ω ℏ : ℝ} (hω : ω ≠ 0) (hℏ : ℏ ≠ 0) (n : ℕ) (Z : FullMat F) :
    handTrace F (∑ h, run S F 22 (keepTree F ω ℏ hℏ (n+1)) h Z) =
      FiniteQutritRetainedClock.amplifiedJointIterate F (n+1) (handTrace F Z) := by
  rw [keep_all_records F hω hℏ, handTrace_insert, FiniteClockHandReadout.Q_trace, one_smul]

theorem branch_difference_norm_frequency {ℏ ℏ' : ℝ} (hℏ : ℏ ≠ 0) (hℏ' : ℏ' ≠ 0)
    (ω ω' t s : ℝ) (a : A) (i : Fin 11) {Z : FullMat F} (hZ : Z.PosSemidef) :
    traceNorm ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z -
      (step F ω' ℏ' s hℏ').branch S F 22 (outcomeEquiv (a,i)) Z) =
      |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω' s| *
        (dataBranch F a i (handTrace F Z)).trace.re := by
  rw [branch_action, branch_action, ← sub_smul, ← Complex.ofReal_sub, traceNorm_real_smul]
  rw [traceNorm_posSemidef (insert_positive F
    (dataBranch_positive F a i (handTrace_positive F hZ)) (FiniteClockHandReadout.Q_density a).1)]
  rw [insert_trace, FiniteClockHandReadout.Q_trace, mul_one]
  congr 1
  fin_cases a <;> simp [FiniteClockHandReadout.mass, abs_sub_comm]

theorem stepDistance_frequency_exact {ℏ ℏ' : ℝ} (hℏ : ℏ ≠ 0) (hℏ' : ℏ' ≠ 0)
    (ω ω' t s : ℝ) {Z : FullMat F} (hZ : Z.PosSemidef) :
    FiniteAdaptiveMapPerturbation.stepDistance S F 22 (step F ω ℏ t hℏ) (step F ω' ℏ' s hℏ') Z =
      |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω' s| * Z.trace.re := by
  unfold FiniteAdaptiveMapPerturbation.stepDistance
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, branch_difference_norm_frequency F hℏ hℏ' ω ω' t s _ _ hZ,
    ← Finset.mul_sum, ← Complex.re_sum, dataBranch_sum_trace, handTrace_trace, Fin.sum_univ_two]
  norm_num [Complex.mul_re]
  <;> ring

theorem localError_frequency {ℏ ℏ' : ℝ} (hℏ : ℏ ≠ 0) (hℏ' : ℏ' ≠ 0)
    (ω ω' t s : ℝ) :
    FiniteAdaptiveMapPerturbation.LocalError S F 22 (step F ω ℏ t hℏ) (step F ω' ℏ' s hℏ')
      (min 1 (|ω*t-ω'*s|/2)) := by
  refine ⟨le_min (by norm_num) (by positivity), fun Z hZ => ?_⟩
  rw [stepDistance_frequency_exact F hℏ hℏ' _ _ _ _ hZ.1, hZ.2, Complex.one_re, mul_one]
  exact FiniteClockHandReadout.p_phase_bound ω ω' t s

theorem localError_frequency_duration {ω ℏ ℏ' : ℝ} (hω : 0 ≤ ω)
    (hℏ : ℏ ≠ 0) (hℏ' : ℏ' ≠ 0) (ω' t s : ℝ) :
    FiniteAdaptiveMapPerturbation.LocalError S F 22 (step F ω ℏ t hℏ) (step F ω' ℏ' s hℏ')
      (min 1 ((ω*|t-s|+|ω-ω'| * |s|)/2)) := by
  refine ⟨le_min (by norm_num) (by positivity), fun Z hZ => ?_⟩
  rw [stepDistance_frequency_exact F hℏ hℏ' _ _ _ _ hZ.1, hZ.2, Complex.one_re, mul_one]
  exact FiniteClockHandReadout.frequency_duration_bound hω t s

theorem zero_mass_error {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ)
    {Z : FullMat F} (hZ : Z.PosSemidef) (hz : Z.trace=0) :
    FiniteAdaptiveMapPerturbation.stepDistance S F 22 (step F ω ℏ t hℏ) (step F ω ℏ s hℏ) Z = 0 := by
  rw [stepDistance_exact F hℏ _ _ _ hZ, hz, Complex.zero_re, mul_zero]

theorem branches_density {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    {Z : FullMat F} (hZ : IsDensityOperator Z) :
    IsDensityOperator (∑ k, (step F ω ℏ t hℏ).branch S F 22 k Z) := by
  refine ⟨Matrix.posSemidef_sum _ (fun k _ => branch_positive F hℏ _ _ k hZ.1), ?_⟩
  rw [Matrix.trace_sum, branches_trace, hZ.2]

end SKEFTHawking.QuantumNetwork.FiniteClockControlledRetainedMemory
