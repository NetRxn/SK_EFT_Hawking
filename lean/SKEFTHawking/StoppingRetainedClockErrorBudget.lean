import SKEFTHawking.StoppingRetainedClockInstrument
import SKEFTHawking.QuantumNetwork.FiniteInstrumentBranchContraction
import SKEFTHawking.QuantumNetwork.UnitaryDiamond

/-! Additive branch-state error budgets for record-dependent stopping and clock perturbations. -/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork FiniteGibbsClock
open scoped Kronecker

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- An instrument at every nonterminal node of the same finite stopping tree. -/
def StoppingSchedule.Instruments (ι : Type u) [Fintype ι] [DecidableEq ι] :
    StoppingSchedule → Type u
  | .done => PUnit
  | .measure _ next => FiniteInstrument ι 3 × (∀ a : Fin 3, (next a).Instruments ι)

/-- The unnormalized state at the end of a terminal record. -/
def StoppingSchedule.leafState : (S : StoppingSchedule) →
    S.Instruments ι → S.Record → Matrix ι ι ℂ → Matrix ι ι ℂ
  | .done, _, _, X => X
  | .measure _ next, P, r, X =>
    (next r.1).leafState (P.2 r.1) r.2 (P.1.branch r.1 X)

/-- Sum of local discrepancies on the unnormalized reference node states. -/
def StoppingSchedule.errorBudget : (S : StoppingSchedule) →
    S.Instruments ι → S.Instruments ι → Matrix ι ι ℂ → ℝ
  | .done, _, _, _ => 0
  | .measure _ next, P, Q, Y =>
    (∑ a, QuantumNetwork.traceNorm (P.1.branch a Y - Q.1.branch a Y)) +
      ∑ a, (next a).errorBudget (P.2 a) (Q.2 a) (Q.1.branch a Y)

/-- Keeping all terminal states gives one additive error budget on a shared tree. -/
theorem StoppingSchedule.sum_leafState_error_le (S : StoppingSchedule)
    (P Q : S.Instruments ι) {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∑ r : S.Record, QuantumNetwork.traceNorm (S.leafState P r X - S.leafState Q r Y)) ≤
      QuantumNetwork.traceNorm (X - Y) + S.errorBudget P Q Y := by
  induction S generalizing X Y with
  | done =>
    change (∑ _ : Unit, QuantumNetwork.traceNorm (X-Y)) ≤ QuantumNetwork.traceNorm (X-Y) + 0
    simp
  | measure s next ih =>
    let cost (a : Fin 3) :=
      QuantumNetwork.traceNorm (P.1.branch a X - Q.1.branch a Y)
    let rest (a : Fin 3) := (next a).errorBudget (P.2 a) (Q.2 a) (Q.1.branch a Y)
    let localCost := ∑ a, QuantumNetwork.traceNorm (P.1.branch a Y - Q.1.branch a Y)
    let gap (a : Fin 3) (r : (next a).Record) :=
      QuantumNetwork.traceNorm
        ((next a).leafState (P.2 a) r (P.1.branch a X) -
          (next a).leafState (Q.2 a) r (Q.1.branch a Y))
    have hrec (a : Fin 3) : (∑ r, gap a r) ≤ cost a + rest a :=
      ih a (P.2 a) (Q.2 a) (P.1.branch_posSemidef a hX) (Q.1.branch_posSemidef a hY)
    have hroot : (∑ a, cost a) ≤ QuantumNetwork.traceNorm (X-Y) + localCost :=
      P.1.sum_traceNorm_branch_sub_le Q.1 hX.isHermitian hY.isHermitian
    have hsplit : (∑ r : Σ a : Fin 3, (next a).Record, gap r.1 r.2) =
        ∑ a, ∑ r, gap a r := Fintype.sum_sigma _
    change (∑ r : Σ a : Fin 3, (next a).Record, gap r.1 r.2) ≤
      QuantumNetwork.traceNorm (X - Y) + (localCost + ∑ a, rest a)
    calc
      _ = ∑ a, ∑ r, gap a r := hsplit
      _ ≤ ∑ a, (cost a + rest a) := Finset.sum_le_sum (fun a _ => hrec a)
      _ = (∑ a, cost a) + ∑ a, rest a := Finset.sum_add_distrib
      _ ≤ (QuantumNetwork.traceNorm (X-Y) + localCost) + ∑ a, rest a :=
        add_le_add_left hroot _
      _ = _ := add_assoc _ _ _

/-- An error allowance at each decision in the common tree. -/
def StoppingSchedule.Allowances : StoppingSchedule → Type
  | .done => Unit
  | .measure _ next => ℝ × (∀ a : Fin 3, (next a).Allowances)

def StoppingSchedule.LocalErrorBound : (S : StoppingSchedule) →
    S.Instruments ι → S.Instruments ι → S.Allowances → Prop
  | .done, _, _, _ => True
  | .measure _ next, P, Q, ε =>
    (∀ X : Matrix ι ι ℂ, X.PosSemidef →
      (∑ a, QuantumNetwork.traceNorm (P.1.branch a X - Q.1.branch a X)) ≤ ε.1 * X.trace.re) ∧
      ∀ a, (next a).LocalErrorBound (P.2 a) (Q.2 a) (ε.2 a)

/-- Each local allowance is multiplied by the probability mass reaching its node. -/
def StoppingSchedule.weightedBudget : (S : StoppingSchedule) →
    S.Allowances → S.Instruments ι → Matrix ι ι ℂ → ℝ
  | .done, _, _, _ => 0
  | .measure _ next, ε, Q, Y =>
    ε.1 * Y.trace.re + ∑ a, (next a).weightedBudget (ε.2 a) (Q.2 a) (Q.1.branch a Y)

theorem StoppingSchedule.errorBudget_le_weightedBudget (S : StoppingSchedule)
    (P Q : S.Instruments ι) (ε : S.Allowances) (h : S.LocalErrorBound P Q ε)
    {Y : Matrix ι ι ℂ} (hY : Y.PosSemidef) :
    S.errorBudget P Q Y ≤ S.weightedBudget ε Q Y := by
  induction S generalizing Y with
  | done => exact le_rfl
  | measure s next ih =>
    change (∀ X : Matrix ι ι ℂ, X.PosSemidef →
      (∑ a, QuantumNetwork.traceNorm (P.1.branch a X - Q.1.branch a X)) ≤ ε.1 * X.trace.re) ∧
      (∀ a, (next a).LocalErrorBound (P.2 a) (Q.2 a) (ε.2 a)) at h
    exact add_le_add (h.1 Y hY)
      (Finset.sum_le_sum (fun a _ => ih a (P.2 a) (Q.2 a) (ε.2 a) (h.2 a)
        (Q.1.branch_posSemidef a hY)))

theorem StoppingSchedule.sum_leafState_error_le_weightedBudget (S : StoppingSchedule)
    (P Q : S.Instruments ι) (ε : S.Allowances) (h : S.LocalErrorBound P Q ε)
    {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∑ r : S.Record, QuantumNetwork.traceNorm (S.leafState P r X - S.leafState Q r Y)) ≤
      QuantumNetwork.traceNorm (X - Y) + S.weightedBudget ε Q Y :=
  (S.sum_leafState_error_le P Q hX hY).trans
    (add_le_add_right (S.errorBudget_le_weightedBudget P Q ε h hY) _)

/-- Realize a clock at every node. Each shift can depend on the preceding record. -/
def StoppingSchedule.clockPolicy (ω ℏ E β : ℝ) (A : Type u) [Fintype A] [DecidableEq A] :
    (S : StoppingSchedule) → (List (Fin 3) → ℝ) → S.Instruments (Level × A)
  | .done, _ => PUnit.unit
  | .measure s next, shift =>
    ⟨(clockInstrument ω ℏ E (-β * ℏ * (s + shift []))).lift A,
      fun a => (next a).clockPolicy ω ℏ E β A (fun pre => shift (a :: pre))⟩

private theorem clockInstrument_lift_branch_sandwich (ω ℏ E t : ℝ) (A : Type u)
    [Fintype A] [DecidableEq A] (a : Fin 3) (X : Matrix (Level × A) (Level × A) ℂ) :
    let W := evolvedProjector ω ℏ E t a ⊗ₖ (1 : Matrix A A ℂ)
    ((clockInstrument ω ℏ E t).lift A).branch a X = W * X * Wᴴ := by
  intro W
  change (∑ _ : Fin 1, W * X * Wᴴ) = _
  rw [Fin.sum_univ_one]

/-- A zero shift gives exactly the previously defined lifted stopped record. -/
theorem StoppingSchedule.zero_clockPolicy_leafState (ω ℏ E β : ℝ) (A : Type u)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule) (r : S.Record)
    (X : Matrix (Level × A) (Level × A) ℂ) :
    S.leafState (S.clockPolicy ω ℏ E β A (fun _ => 0)) r X =
      ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) X := by
  rw [S.instrument_lift_branch]
  induction S generalizing X with
  | done => simp [StoppingSchedule.leafState, StoppingSchedule.recordOperator]
  | measure s next ih =>
    simp only [StoppingSchedule.leafState, StoppingSchedule.clockPolicy, add_zero, ih,
      clockInstrument_lift_branch_sandwich, StoppingSchedule.recordOperator]
    let U := (next r.1).recordOperator ω ℏ E β r.2
    let V := evolvedProjector ω ℏ E (-β * ℏ * s) r.1
    have hprod : (U ⊗ₖ (1 : Matrix A A ℂ)) * (V ⊗ₖ (1 : Matrix A A ℂ)) =
        (U * V) ⊗ₖ (1 : Matrix A A ℂ) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
    change (U ⊗ₖ (1 : Matrix A A ℂ)) * ((V ⊗ₖ (1 : Matrix A A ℂ)) * X *
      (V ⊗ₖ (1 : Matrix A A ℂ))ᴴ) * (U ⊗ₖ (1 : Matrix A A ℂ))ᴴ =
        ((U * V) ⊗ₖ (1 : Matrix A A ℂ)) * X * ((U * V) ⊗ₖ (1 : Matrix A A ℂ))ᴴ
    rw [← hprod, Matrix.conjTranspose_mul]
    simp only [mul_assoc]

/-- A prefix-dependent time perturbation can be charged against the nominal stopped clock. -/
theorem StoppingSchedule.shiftedClock_leaf_error_le (ω ℏ E β : ℝ) (A : Type u)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule) (shift : List (Fin 3) → ℝ)
    (ε : S.Allowances)
    (h : S.LocalErrorBound (S.clockPolicy ω ℏ E β A shift)
      (S.clockPolicy ω ℏ E β A (fun _ => 0)) ε)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∑ r : S.Record, QuantumNetwork.traceNorm
      (S.leafState (S.clockPolicy ω ℏ E β A shift) r X -
        ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y)) ≤
      QuantumNetwork.traceNorm (X - Y) +
        S.weightedBudget ε (S.clockPolicy ω ℏ E β A (fun _ => 0)) Y := by
  simp_rw [← S.zero_clockPolicy_leafState ω ℏ E β A]
  exact S.sum_leafState_error_le_weightedBudget _ _ ε h hX hY

/-- Use one per-decision allowance throughout the shared tree. -/
def StoppingSchedule.uniformAllowance (ε : ℝ) : (S : StoppingSchedule) → S.Allowances
  | .done => ()
  | .measure _ next => ⟨ε, fun a => (next a).uniformAllowance ε⟩

theorem StoppingSchedule.sum_leafState_trace (S : StoppingSchedule)
    (Q : S.Instruments ι) (Y : Matrix ι ι ℂ) :
    (∑ r : S.Record, (S.leafState Q r Y).trace.re) = Y.trace.re := by
  induction S generalizing Y with
  | done =>
    change (∑ _ : Unit, Y.trace.re) = _
    simp
  | measure s next ih =>
    let f (a : Fin 3) (r : (next a).Record) :=
      ((next a).leafState (Q.2 a) r (Q.1.branch a Y)).trace.re
    change (∑ r : Σ a : Fin 3, (next a).Record, f r.1 r.2) = _
    calc
      _ = ∑ a, ∑ r, f a r := Fintype.sum_sigma _
      _ = ∑ a, (Q.1.branch a Y).trace.re :=
        Finset.sum_congr rfl (fun a _ => ih a (Q.2 a) (Q.1.branch a Y))
      _ = _ := Q.1.sum_weight Y

/-- A uniform per-decision allowance is multiplied by the reference mean
number of actual measurements, computed on the terminal records. -/
theorem StoppingSchedule.weightedBudget_uniform_eq (S : StoppingSchedule)
    (Q : S.Instruments ι) (Y : Matrix ι ι ℂ) (ε : ℝ) :
    S.weightedBudget (S.uniformAllowance ε) Q Y =
      ε * ∑ r : S.Record, ((S.path r).length : ℝ) * (S.leafState Q r Y).trace.re := by
  induction S generalizing Y with
  | done =>
    simp [weightedBudget, path, leafState]
  | measure s next ih =>
    let f (a : Fin 3) (r : (next a).Record) :=
      ((next a).leafState (Q.2 a) r (Q.1.branch a Y)).trace.re
    let d (a : Fin 3) (r : (next a).Record) := ((next a).path r).length
    let moment (a : Fin 3) := ∑ r, (d a r : ℝ) * f a r
    let mass (a : Fin 3) := (Q.1.branch a Y).trace.re
    have hm (a : Fin 3) : (∑ r, ((d a r : ℝ) + 1) * f a r) = moment a + mass a := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib, moment, mass]
      exact congrArg ((∑ r, (d a r : ℝ) * f a r) + ·)
        ((next a).sum_leafState_trace (Q.2 a) (Q.1.branch a Y))
    have hbudget (a : Fin 3) : (next a).weightedBudget ((next a).uniformAllowance ε)
        (Q.2 a) (Q.1.branch a Y) = ε * moment a := ih a (Q.2 a) (Q.1.branch a Y)
    have hmass : (∑ a, mass a) = Y.trace.re := Q.1.sum_weight Y
    have hsplit : (∑ r : Σ a : Fin 3, (next a).Record,
        ((d r.1 r.2 : ℝ) + 1) * f r.1 r.2) =
        ∑ a, ∑ r, ((d a r : ℝ) + 1) * f a r := Fintype.sum_sigma _
    change ε * Y.trace.re + (∑ a, (next a).weightedBudget ((next a).uniformAllowance ε)
        (Q.2 a) (Q.1.branch a Y)) =
        ε * ∑ r : Σ a : Fin 3, (next a).Record, ((d r.1 r.2 + 1 : ℕ) : ℝ) * f r.1 r.2
    simp only [Nat.cast_add, Nat.cast_one, hsplit, hm, hbudget]
    rw [Finset.sum_add_distrib, hmass, ← Finset.mul_sum, mul_add, add_comm]

/-- The existing duration instrument reports exactly the terminal length moment. -/
theorem StoppingSchedule.durationInstrument_lift_mean_eq (ω ℏ E β : ℝ) (A : Type u)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule)
    (Y : Matrix (Level × A) (Level × A) ℂ) :
    (∑ b : Fin (S.height + 1), (b.val : ℝ) * ((S.durationInstrument ω ℏ E β).lift A).weight b Y) =
      ∑ r : S.Record, ((S.path r).length : ℝ) *
        (((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y).trace.re := by
  let f (r : S.Record) := (((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y).trace.re
  let J := (S.durationInstrument ω ℏ E β).lift A
  have hw (b : Fin (S.height + 1)) :
      J.weight b Y = ∑ r ∈ Finset.univ.filter (fun r => S.duration r = b), f r := by
    change (((S.durationInstrument ω ℏ E β).lift A).branch b Y).trace.re = _
    rw [StoppingSchedule.durationInstrument, S.reportedInstrument_lift_branch]
    simp only [Matrix.trace_sum, Complex.re_sum, f, S.instrument_lift_branch]
  change (∑ b : Fin (S.height + 1), (b.val : ℝ) * J.weight b Y) = _
  calc
    _ = ∑ b : Fin (S.height + 1), ∑ r : S.Record,
        if S.duration r = b then (b.val : ℝ) * f r else 0 := by
      simp_rw [hw, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ r : S.Record, ∑ b : Fin (S.height + 1),
        if S.duration r = b then (b.val : ℝ) * f r else 0 := Finset.sum_comm
    _ = ∑ r : S.Record, ((S.path r).length : ℝ) * f r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_eq_single (S.duration r)]
      · rw [if_pos rfl]
        rfl
      · intro b _ hb
        exact if_neg hb.symm
      · intro h
        exact (h (Finset.mem_univ _)).elim

/-- With a uniform local allowance the full branch-state error grows with
the nominal mean stopping duration. For a normalized reference this is an expectation. -/
theorem StoppingSchedule.shiftedClock_leaf_error_le_meanDuration (ω ℏ E β : ℝ) (A : Type u)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule) (shift : List (Fin 3) → ℝ)
    (ε : ℝ)
    (h : S.LocalErrorBound (S.clockPolicy ω ℏ E β A shift)
      (S.clockPolicy ω ℏ E β A (fun _ => 0)) (S.uniformAllowance ε))
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∑ r : S.Record, QuantumNetwork.traceNorm
      (S.leafState (S.clockPolicy ω ℏ E β A shift) r X -
        ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y)) ≤
      QuantumNetwork.traceNorm (X - Y) + ε *
        ∑ b : Fin (S.height + 1), (b.val : ℝ) * ((S.durationInstrument ω ℏ E β).lift A).weight b Y := by
  have hb := S.shiftedClock_leaf_error_le ω ℏ E β A shift (S.uniformAllowance ε) h hX hY
  rw [S.weightedBudget_uniform_eq] at hb
  simp_rw [S.zero_clockPolicy_leafState ω ℏ E β A] at hb
  rwa [S.durationInstrument_lift_mean_eq ω ℏ E β A Y]

section ProjectorDrift

open scoped Matrix.Norms.L2Operator

private theorem evolvedProjector_opNorm_le_one (ω ℏ E t : ℝ) (a : Fin 3) :
    ‖evolvedProjector ω ℏ E t a‖ ≤ 1 := by
  let P := evolvedProjector ω ℏ E t a
  have ha : Pᴴ = P := evolvedProjector_adjoint ω ℏ E t a
  have hp : P * P = P := by simpa using evolvedProjector_mul ω ℏ E t a a
  apply opNorm_le_one_of_mul_conjTranspose_le_one
  change ((1 : Mat) - P * Pᴴ).PosSemidef
  rw [ha, hp]
  have hc : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, ha, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, Matrix.mul_one, hp, sub_self, sub_zero]
  rw [← hc]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- A single decision's allowance is computed on the clock Hilbert space. -/
def clockProjectorAllowance (ω ℏ E t t' : ℝ) : ℝ :=
  2 * ∑ a, ‖evolvedProjector ω ℏ E t a - evolvedProjector ω ℏ E t' a‖

/-- The same allowance bounds the joint branch-state error for any finite auxiliary system. -/
theorem clockInstrument_lift_localError_le (ω ℏ E t t' : ℝ) (A : Type u)
    [Fintype A] [DecidableEq A] {Y : Matrix (Level × A) (Level × A) ℂ} (hY : Y.PosSemidef) :
    (∑ a, QuantumNetwork.traceNorm (((clockInstrument ω ℏ E t).lift A).branch a Y -
      ((clockInstrument ω ℏ E t').lift A).branch a Y)) ≤
      clockProjectorAllowance ω ℏ E t t' * Y.trace.re := by
  let I : Matrix A A ℂ := 1
  let P := evolvedProjector ω ℏ E t
  let Q := evolvedProjector ω ℏ E t'
  calc
    _ ≤ ∑ a, (2 * ‖P a - Q a‖) * Y.trace.re := by
      apply Finset.sum_le_sum
      intro a _
      rw [clockInstrument_lift_branch_sandwich, clockInstrument_lift_branch_sandwich]
      change QuantumNetwork.traceNorm
          ((P a ⊗ₖ I) * Y * (P a ⊗ₖ I)ᴴ - (Q a ⊗ₖ I) * Y * (Q a ⊗ₖ I)ᴴ) ≤ _
      have hP := (KroneckerOpNorm.l2_opNorm_kronecker_one_le (p := A) (P a)).trans
        (evolvedProjector_opNorm_le_one ω ℏ E t a)
      have hQ := (KroneckerOpNorm.l2_opNorm_kronecker_one_le (p := A) (Q a)).trans
        (evolvedProjector_opNorm_le_one ω ℏ E t' a)
      have hdiff : ‖P a ⊗ₖ I - Q a ⊗ₖ I‖ ≤ ‖P a - Q a‖ := by
        have he : (P a - Q a) ⊗ₖ I = P a ⊗ₖ I - Q a ⊗ₖ I := by
          ext i j
          exact sub_mul (P a i.1 j.1) (Q a i.1 j.1) (I i.2 j.2)
        rw [← he]
        exact KroneckerOpNorm.l2_opNorm_kronecker_one_le _
      rw [← traceNorm_posSemidef hY]
      exact (traceNorm_conj_diff_le hP hQ Y).trans <|
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by norm_num))
          (traceNorm_nonneg Y)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, clockProjectorAllowance]

/-- Use the two actual clock times at each prefix to compute the allowances. -/
def StoppingSchedule.projectorAllowance (ω ℏ E β : ℝ) :
    (S : StoppingSchedule) → (List (Fin 3) → ℝ) → S.Allowances
  | .done, _ => ()
  | .measure s next, shift =>
    ⟨clockProjectorAllowance ω ℏ E (-β * ℏ * (s + shift [])) (-β * ℏ * s),
      fun a => (next a).projectorAllowance ω ℏ E β (fun pre => shift (a :: pre))⟩

theorem StoppingSchedule.localErrorBound_projectorAllowance (ω ℏ E β : ℝ) (A : Type u)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule) (shift : List (Fin 3) → ℝ) :
    S.LocalErrorBound (S.clockPolicy ω ℏ E β A shift) (S.clockPolicy ω ℏ E β A (fun _ => 0))
      (S.projectorAllowance ω ℏ E β shift) := by
  induction S generalizing shift with
  | done => trivial
  | measure s next ih =>
    refine ⟨?_, fun a => ih a (fun pre => shift (a :: pre))⟩
    intro X hX
    simpa only [StoppingSchedule.clockPolicy, StoppingSchedule.projectorAllowance, add_zero] using
      clockInstrument_lift_localError_le ω ℏ E (-β * ℏ * (s + shift [])) (-β * ℏ * s) A hX

/-- Projector drift bounds the terminal branch-state error without a separate local premise. -/
theorem StoppingSchedule.shiftedClock_leaf_error_le_projectorBudget (ω ℏ E β : ℝ) (A : Type u)
    [Fintype A] [DecidableEq A] (S : StoppingSchedule) (shift : List (Fin 3) → ℝ)
    {X Y : Matrix (Level × A) (Level × A) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∑ r : S.Record, QuantumNetwork.traceNorm
      (S.leafState (S.clockPolicy ω ℏ E β A shift) r X -
        ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) Y)) ≤
      QuantumNetwork.traceNorm (X - Y) +
        S.weightedBudget (S.projectorAllowance ω ℏ E β shift)
          (S.clockPolicy ω ℏ E β A (fun _ => 0)) Y := by
  exact S.shiftedClock_leaf_error_le ω ℏ E β A shift _
    (S.localErrorBound_projectorAllowance ω ℏ E β A shift) hX hY

end ProjectorDrift

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
