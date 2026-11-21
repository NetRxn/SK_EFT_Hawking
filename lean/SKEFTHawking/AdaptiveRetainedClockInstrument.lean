import SKEFTHawking.ProperRetainedClockInstrument
import Mathlib.Data.Fin.Tuple.Basic

/-! A finite record can select the next modular time of the actual retained clock. -/
noncomputable section
open Matrix
open scoped ComplexOrder Kronecker
namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork FiniteGibbsClock
open QuantumNetwork.FiniteClockHandReadout (mass p p_keep p_reflection rhoPlus_eq)

/-- A fixed-depth schedule with one continuation for each of the three records. -/
inductive Schedule : ℕ → Type
  | done : Schedule 0
  | measure {n : ℕ} (s : ℝ) (next : Fin 3 → Schedule n) : Schedule (n + 1)

/-- Each record carries the unnormalized branch state of the actual instruments. -/
def Schedule.branch (ω ℏ E β : ℝ) :
    {n : ℕ} → Schedule n → (Fin n → Fin 3) → Mat → Mat
  | _, .done, _, X => X
  | _, .measure s next, a, X =>
    (next (a 0)).branch ω ℏ E β (Fin.tail a)
      ((clockInstrument ω ℏ E (-β * ℏ * s)).branch (a 0) X)

theorem Schedule.branch_cons (ω ℏ E β s : ℝ) {n : ℕ}
    (next : Fin 3 → Schedule n) (a : Fin 3) (r : Fin n → Fin 3) (X : Mat) :
    (Schedule.measure s next).branch ω ℏ E β (Fin.cons a r) X =
      (next a).branch ω ℏ E β r ((clockInstrument ω ℏ E (-β * ℏ * s)).branch a X) := by
  simp only [Schedule.branch, Fin.cons_zero, Fin.tail_cons]

theorem Schedule.branch_posSemidef (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n)
    (r : Fin n → Fin 3) {X : Mat} (hX : X.PosSemidef) :
    (S.branch ω ℏ E β r X).PosSemidef := by
  induction S generalizing X with
  | done => exact hX
  | measure s next ih =>
    exact ih (r 0) (Fin.tail r) ((clockInstrument ω ℏ E (-β * ℏ * s)).branch_posSemidef _ hX)

theorem Schedule.branch_mem_fixedAlgebra (ω ℏ E β : ℝ) (hℏ : 0 < ℏ) {n : ℕ}
    (S : Schedule n) (r : Fin n → Fin 3) {X : Mat} (hX : X ∈ fixedAlgebra signatures) :
    S.branch ω ℏ E β r X ∈ fixedAlgebra signatures := by
  induction S generalizing X with
  | done => exact hX
  | measure s next ih =>
    exact ih (r 0) (Fin.tail r) (clockInstrument_branch_mem_fixedAlgebra ω ℏ E β s hℏ _ _ hX)

theorem Schedule.sum_trace (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n) (X : Mat) :
    ∑ r : Fin n → Fin 3, (S.branch ω ℏ E β r X).trace = X.trace := by
  induction S generalizing X with
  | done => simp [Schedule.branch]
  | @measure n s next ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3)
    calc
      _ = ∑ r : Fin 3 × (Fin n → Fin 3),
          ((Schedule.measure s next).branch ω ℏ E β (e r) X).trace := by
        symm
        exact Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∑ a : Fin 3, ((clockInstrument ω ℏ E (-β * ℏ * s)).branch a X).trace := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a _
        change (∑ r : Fin n → Fin 3, ((Schedule.measure s next).branch ω ℏ E β (Fin.cons a r) X).trace) = _
        simp only [Schedule.branch_cons]
        exact ih a _
      _ = X.trace := (clockInstrument ω ℏ E (-β * ℏ * s)).sum_trace X

theorem Schedule.first_marginal (ω ℏ E β s : ℝ) {n : ℕ} (next : Fin 3 → Schedule n)
    (a : Fin 3) (X : Mat) :
    ∑ r : Fin n → Fin 3, ((Schedule.measure s next).branch ω ℏ E β (Fin.cons a r) X).trace =
      ((clockInstrument ω ℏ E (-β * ℏ * s)).branch a X).trace := by
  simp only [Schedule.branch_cons]
  exact (next a).sum_trace ω ℏ E β _

theorem Schedule.path_law (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n) {X : Mat}
    (hX : IsDensityOperator X) :
    (∀ r : Fin n → Fin 3, 0 ≤ (S.branch ω ℏ E β r X).trace.re) ∧
      (∑ r : Fin n → Fin 3, (S.branch ω ℏ E β r X).trace.re) = 1 := by
  refine ⟨fun r => (Complex.le_def.mp (S.branch_posSemidef ω ℏ E β r hX.1).trace_nonneg).1, ?_⟩
  have h := congrArg Complex.re ((S.sum_trace ω ℏ E β X).trans hX.2)
  simpa only [map_sum, Complex.reCLM_apply, Complex.one_re] using
    (show Complex.reCLM (∑ r : Fin n → Fin 3, (S.branch ω ℏ E β r X).trace) =
      Complex.reCLM 1 from h)

/-- The Kraus operator is the ordered product along the actual record. -/
def Schedule.recordOperator (ω ℏ E β : ℝ) :
    {n : ℕ} → Schedule n → (Fin n → Fin 3) → Mat
  | _, .done, _ => 1
  | _, .measure s next, a =>
    (next (a 0)).recordOperator ω ℏ E β (Fin.tail a) *
      evolvedProjector ω ℏ E (-β * ℏ * s) (a 0)

theorem Schedule.branch_eq_sandwich (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n)
    (r : Fin n → Fin 3) (X : Mat) :
    S.branch ω ℏ E β r X =
      S.recordOperator ω ℏ E β r * X * (S.recordOperator ω ℏ E β r)ᴴ := by
  induction S generalizing X with
  | done => simp [Schedule.branch, Schedule.recordOperator]
  | measure s next ih =>
    rw [Schedule.branch, Schedule.recordOperator, ih, clockInstrument_branch]
    rw [Matrix.conjTranspose_mul, evolvedProjector_adjoint]
    simp only [mul_assoc]

theorem Schedule.recordOperator_normalized (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n) :
    (∑ r : Fin n → Fin 3, (S.recordOperator ω ℏ E β r)ᴴ * S.recordOperator ω ℏ E β r) = 1 := by
  induction S with
  | done => simp [Schedule.recordOperator]
  | @measure n s next ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3)
    let A := Schedule.measure s next
    let P := evolvedProjector ω ℏ E (-β * ℏ * s)
    calc
      _ = ∑ b : Fin 3 × (Fin n → Fin 3),
          (A.recordOperator ω ℏ E β (e b))ᴴ * A.recordOperator ω ℏ E β (e b) := by
        symm
        exact Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∑ a : Fin 3, P a := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a _
        let L := (next a).recordOperator ω ℏ E β
        have eq (r : Fin n → Fin 3) : A.recordOperator ω ℏ E β (e (a,r)) = L r * P a := by
          change A.recordOperator ω ℏ E β (Fin.cons a r) = _
          simp only [A, Schedule.recordOperator, Fin.cons_zero, Fin.tail_cons, L, P]
        simp_rw [eq, Matrix.conjTranspose_mul, ← mul_assoc]
        rw [← Finset.sum_mul]
        simp_rw [show ∀ r, (P a)ᴴ * (L r)ᴴ * L r = (P a)ᴴ * ((L r)ᴴ * L r) by
          intro r; rw [mul_assoc]]
        rw [← Finset.mul_sum, show (∑ r, (L r)ᴴ * L r) = 1 from ih a, Matrix.mul_one]
        change (P a)ᴴ * P a = P a
        rw [show (P a)ᴴ = P a from evolvedProjector_adjoint _ _ _ _ _]
        simpa only [if_true] using evolvedProjector_mul ω ℏ E (-β * ℏ * s) a a
      _ = 1 := evolvedProjector_complete ω ℏ E (-β * ℏ * s)

def Schedule.recordEquiv (n : ℕ) :
    (Fin n → Fin 3) ≃ Fin (Fintype.card (Fin n → Fin 3)) := Fintype.equivFin _

/-- A whole adaptive experiment is a normalized instrument, with the record as its outcome. -/
def Schedule.instrument (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n) :
    FiniteInstrument Level (Fintype.card (Fin n → Fin 3)) where
  count := 1
  operators a _ := S.recordOperator ω ℏ E β ((Schedule.recordEquiv n).symm a)
  normalized := by
    change (∑ a : Fin (Fintype.card (Fin n → Fin 3)), ∑ _ : Fin 1,
      (S.recordOperator ω ℏ E β ((Schedule.recordEquiv n).symm a))ᴴ *
        S.recordOperator ω ℏ E β ((Schedule.recordEquiv n).symm a)) = 1
    simp only [Fin.sum_univ_one]
    let g (r : Fin n → Fin 3) := (S.recordOperator ω ℏ E β r)ᴴ * S.recordOperator ω ℏ E β r
    exact ((Schedule.recordEquiv n).symm.sum_comp g).trans (S.recordOperator_normalized ω ℏ E β)

theorem Schedule.instrument_branch (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n)
    (r : Fin n → Fin 3) (X : Mat) :
    (S.instrument ω ℏ E β).branch (Schedule.recordEquiv n r) X = S.branch ω ℏ E β r X := by
  change (∑ _ : Fin 1,
    S.recordOperator ω ℏ E β ((Schedule.recordEquiv n).symm (Schedule.recordEquiv n r)) * X *
      (S.recordOperator ω ℏ E β ((Schedule.recordEquiv n).symm (Schedule.recordEquiv n r)))ᴴ) = _
  rw [Equiv.symm_apply_apply, Fin.sum_univ_one, S.branch_eq_sandwich]

/-- The Kraus operator acts as the identity on the finite auxiliary factor
along every record. The branch law applies to correlated joint inputs. -/
theorem Schedule.instrument_lift_branch (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n)
    (r : Fin n → Fin 3) (A : Type*) [Fintype A] [DecidableEq A]
    (X : Matrix (Level × A) (Level × A) ℂ) :
    let W := S.recordOperator ω ℏ E β r ⊗ₖ (1 : Matrix A A ℂ)
    ((S.instrument ω ℏ E β).lift A).branch (Schedule.recordEquiv n r) X = W * X * Wᴴ := by
  let W := S.recordOperator ω ℏ E β ((Schedule.recordEquiv n).symm (Schedule.recordEquiv n r))
    ⊗ₖ (1 : Matrix A A ℂ)
  change (∑ _ : Fin 1, W * X * Wᴴ) = _
  rw [Fin.sum_univ_one]
  simp only [W, Equiv.symm_apply_apply]

/-- The reported outcome is a function of the record of the actual adaptive schedule. -/
def Schedule.reportedInstrument (ω ℏ E β : ℝ) {n q : ℕ} (S : Schedule n)
    (report : (Fin n → Fin 3) → Fin q) : FiniteInstrument Level q :=
  (S.instrument ω ℏ E β).relabel (fun a => report ((Schedule.recordEquiv n).symm a))

theorem Schedule.reportedInstrument_branch (ω ℏ E β : ℝ) {n q : ℕ} (S : Schedule n)
    (report : (Fin n → Fin 3) → Fin q) (b : Fin q) (X : Mat) :
    (S.reportedInstrument ω ℏ E β report).branch b X =
      ∑ r ∈ Finset.univ.filter (fun r => report r = b), S.branch ω ℏ E β r X := by
  rw [Schedule.reportedInstrument, FiniteInstrument.relabel_branch]
  simp only [Finset.sum_filter]
  let e := Schedule.recordEquiv n
  have h := e.sum_comp (fun a =>
    if report (e.symm a) = b then (S.instrument ω ℏ E β).branch a X else 0)
  rw [← h]
  simp only [e, Equiv.symm_apply_apply, Schedule.instrument_branch]

theorem Schedule.reportedInstrument_lift_branch (ω ℏ E β : ℝ) {n q : ℕ} (S : Schedule n)
    (report : (Fin n → Fin 3) → Fin q) (b : Fin q)
    (A : Type*) [Fintype A] [DecidableEq A] (X : Matrix (Level × A) (Level × A) ℂ) :
    ((S.reportedInstrument ω ℏ E β report).lift A).branch b X =
      ∑ r ∈ Finset.univ.filter (fun r => report r = b),
        let W := S.recordOperator ω ℏ E β r ⊗ₖ (1 : Matrix A A ℂ)
        W * X * Wᴴ := by
  rw [Schedule.reportedInstrument, FiniteInstrument.relabel_lift_branch]
  simp only [Finset.sum_filter]
  let e := Schedule.recordEquiv n
  have h := e.sum_comp (fun a =>
    if report (e.symm a) = b then ((S.instrument ω ℏ E β).lift A).branch a X else 0)
  rw [← h]
  simp only [e, Equiv.symm_apply_apply, Schedule.instrument_lift_branch]

theorem Schedule.reportedInstrument_branch_mem_fixedAlgebra (ω ℏ E β : ℝ)
    (hℏ : 0 < ℏ) {n q : ℕ} (S : Schedule n)
    (report : (Fin n → Fin 3) → Fin q) (b : Fin q) {X : Mat}
    (hX : X ∈ fixedAlgebra signatures) :
    (S.reportedInstrument ω ℏ E β report).branch b X ∈ fixedAlgebra signatures := by
  rw [Schedule.reportedInstrument_branch]
  exact (fixedAlgebra signatures).sum_mem fun r _ =>
    S.branch_mem_fixedAlgebra ω ℏ E β hℏ r hX

/-- Reporting only the first readout retains its probability after all continuations. -/
theorem Schedule.report_first_trace (ω ℏ E β s : ℝ) {n : ℕ}
    (next : Fin 3 → Schedule n) (b : Fin 3) (X : Mat) :
    (((Schedule.measure s next).reportedInstrument ω ℏ E β (fun r => r 0)).branch b X).trace =
      ((clockInstrument ω ℏ E (-β * ℏ * s)).branch b X).trace := by
  let S := Schedule.measure s next
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3)
  rw [Schedule.reportedInstrument_branch, Matrix.trace_sum, Finset.sum_filter]
  have h := e.sum_comp (fun r => if r 0 = b then (S.branch ω ℏ E β r X).trace else 0)
  rw [← h, Fintype.sum_prod_type]
  simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Schedule.first_marginal ω ℏ E β s next b X

theorem clockInstrument_initialBranch (ω ℏ E : ℝ) (a : Fin 3) :
    (clockInstrument ω ℏ E 0).branch a prepared =
      if a = (1 : Fin 2).castSucc then prepared else 0 := by
  let one := (1 : Fin 2).castSucc
  have h : evolvedProjector ω ℏ E 0 one = prepared := by
    rw [evolvedProjector, heisenberg_zero, outcomeProjector]
    simp only [one, Fin.lastCases_castSucc, event, prepared, rhoPlus_eq]
  rw [clockInstrument_branch, ← h, evolvedProjector_mul]
  by_cases ha : a = one
  · subst a
    rw [if_pos rfl]
    simpa only [if_true] using evolvedProjector_mul ω ℏ E 0 one one
  · have ha' : a ≠ (1 : Fin 2).castSucc := ha
    simp only [if_neg ha, if_neg ha', zero_mul]

theorem adaptive_halfTurn (E : ℝ) :
    let S : Schedule 2 := .measure 0 (fun a =>
      .measure (if a = (1 : Fin 2).castSucc then Real.pi else 0) (fun _ => .done))
    let r : Fin 2 → Fin 3 := Fin.cons (1 : Fin 2).castSucc (Fin.cons (0 : Fin 2).castSucc Fin.elim0)
    (S.branch 1 1 E 1 r prepared).trace.re = 1 := by
  simp only [Schedule.branch, mul_zero, clockInstrument_initialBranch]
  change (clockInstrument 1 1 E (-(1 : ℝ) * 1 * Real.pi)).weight (0 : Fin 2).castSucc prepared = 1
  rw [clockInstrument_hand_weight _ _ _ _ _ (by norm_num)]
  change p 1 (-(1 : ℝ) * 1 * Real.pi) = 1
  rw [show -(1 : ℝ) * 1 * Real.pi = -(Real.pi / 1) by ring, p_reflection]
  exact p_keep (by norm_num)

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
