import SKEFTHawking.AdaptiveRetainedClockInstrument

/-! Finite outcome-dependent stopping and duration reports for the retained modular clock. -/
noncomputable section
open Matrix
open scoped ComplexOrder Kronecker
namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork FiniteGibbsClock

/-- At a leaf, terminate without applying any further clock measurement. -/
inductive StoppingSchedule : Type
  | done
  | measure (s : ℝ) (next : Fin 3 → StoppingSchedule)

/-- A record ends at its first terminal node. -/
def StoppingSchedule.Record : StoppingSchedule → Type
  | .done => Unit
  | .measure _ next => Σ a : Fin 3, (next a).Record

@[implicit_reducible]
def StoppingSchedule.recordFintype : (S : StoppingSchedule) → Fintype S.Record
  | .done => inferInstanceAs (Fintype Unit)
  | .measure _ next =>
    letI (a : Fin 3) : Fintype (next a).Record := recordFintype (next a)
    inferInstanceAs (Fintype (Σ a : Fin 3, (next a).Record))

instance (S : StoppingSchedule) : Fintype S.Record := S.recordFintype

def StoppingSchedule.path : (S : StoppingSchedule) → S.Record → List (Fin 3)
  | .done, _ => []
  | .measure _ next, r => r.1 :: (next r.1).path r.2

theorem StoppingSchedule.eq_of_path_prefix (S : StoppingSchedule) (r t : S.Record)
    (h : (S.path r).IsPrefix (S.path t)) : r = t := by
  induction S with
  | done => exact Subsingleton.elim (α := Unit) r t
  | measure s next ih =>
    obtain ⟨a, r⟩ := r
    obtain ⟨b, t⟩ := t
    have ⟨hab, hp⟩ := List.cons_prefix_cons.mp h
    change a = b at hab
    subst b
    rw [ih a r t hp]

def StoppingSchedule.branch (ω ℏ E β : ℝ) :
    (S : StoppingSchedule) → S.Record → Mat → Mat
  | .done, _, X => X
  | .measure s next, r, X =>
    (next r.1).branch ω ℏ E β r.2 ((clockInstrument ω ℏ E (-β * ℏ * s)).branch r.1 X)

def StoppingSchedule.recordOperator (ω ℏ E β : ℝ) :
    (S : StoppingSchedule) → S.Record → Mat
  | .done, _ => 1
  | .measure s next, r =>
    (next r.1).recordOperator ω ℏ E β r.2 * evolvedProjector ω ℏ E (-β * ℏ * s) r.1

theorem StoppingSchedule.branch_eq_sandwich (ω ℏ E β : ℝ) (S : StoppingSchedule)
    (r : S.Record) (X : Mat) :
    S.branch ω ℏ E β r X = S.recordOperator ω ℏ E β r * X * (S.recordOperator ω ℏ E β r)ᴴ := by
  induction S generalizing X with
  | done => simp [StoppingSchedule.branch, StoppingSchedule.recordOperator]
  | measure s next ih =>
    rw [StoppingSchedule.branch, StoppingSchedule.recordOperator, ih, clockInstrument_branch]
    rw [Matrix.conjTranspose_mul, evolvedProjector_adjoint]
    simp only [mul_assoc]

theorem StoppingSchedule.recordOperator_normalized (ω ℏ E β : ℝ) (S : StoppingSchedule) :
    (∑ r : S.Record, (S.recordOperator ω ℏ E β r)ᴴ * S.recordOperator ω ℏ E β r) = 1 := by
  induction S with
  | done =>
    change (∑ _ : Unit, (1 : Mat)ᴴ * 1) = 1
    simp
  | measure s next ih =>
    let P := evolvedProjector ω ℏ E (-β * ℏ * s)
    change (∑ r : Σ a : Fin 3, (next a).Record,
      ((next r.1).recordOperator ω ℏ E β r.2 * P r.1)ᴴ *
        ((next r.1).recordOperator ω ℏ E β r.2 * P r.1)) = 1
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ a : Fin 3, P a := by
        apply Finset.sum_congr rfl
        intro a _
        let L := (next a).recordOperator ω ℏ E β
        calc
          _ = ∑ r, (P a)ᴴ * ((L r)ᴴ * L r) * P a := by
            apply Finset.sum_congr rfl
            intro r _
            change (L r * P a)ᴴ * (L r * P a) = _
            rw [Matrix.conjTranspose_mul]
            simp only [mul_assoc]
          _ = P a := by
            rw [← Finset.sum_mul, ← Finset.mul_sum, show (∑ r, (L r)ᴴ * L r) = 1 from ih a,
              Matrix.mul_one]
            change (P a)ᴴ * P a = P a
            rw [show (P a)ᴴ = P a from evolvedProjector_adjoint _ _ _ _ _]
            simpa only [if_true] using evolvedProjector_mul ω ℏ E (-β * ℏ * s) a a
      _ = 1 := evolvedProjector_complete ω ℏ E (-β * ℏ * s)

theorem StoppingSchedule.branch_mem_fixedAlgebra (ω ℏ E β : ℝ) (hℏ : 0 < ℏ)
    (S : StoppingSchedule) (r : S.Record) {X : Mat}
    (hX : X ∈ fixedAlgebra signatures) :
    S.branch ω ℏ E β r X ∈ fixedAlgebra signatures := by
  induction S generalizing X with
  | done => exact hX
  | measure s next ih =>
    exact ih r.1 r.2 (clockInstrument_branch_mem_fixedAlgebra ω ℏ E β s hℏ _ _ hX)

theorem StoppingSchedule.branch_posSemidef (ω ℏ E β : ℝ) (S : StoppingSchedule)
    (r : S.Record) {X : Mat} (hX : X.PosSemidef) : (S.branch ω ℏ E β r X).PosSemidef := by
  induction S generalizing X with
  | done => exact hX
  | measure s _ ih =>
    exact ih r.1 r.2 ((clockInstrument ω ℏ E (-β * ℏ * s)).branch_posSemidef _ hX)

def StoppingSchedule.recordEquiv (S : StoppingSchedule) :
    S.Record ≃ Fin (Fintype.card S.Record) := Fintype.equivFin _

/-- The terminal records of the experiment form a normalized instrument. -/
def StoppingSchedule.instrument (ω ℏ E β : ℝ) (S : StoppingSchedule) :
    FiniteInstrument Level (Fintype.card S.Record) where
  count := 1
  operators a _ := S.recordOperator ω ℏ E β (S.recordEquiv.symm a)
  normalized := by
    change (∑ a : Fin (Fintype.card S.Record), ∑ _ : Fin 1,
      (S.recordOperator ω ℏ E β (S.recordEquiv.symm a))ᴴ *
        S.recordOperator ω ℏ E β (S.recordEquiv.symm a)) = 1
    simp only [Fin.sum_univ_one]
    let g (r : S.Record) := (S.recordOperator ω ℏ E β r)ᴴ * S.recordOperator ω ℏ E β r
    exact (S.recordEquiv.symm.sum_comp g).trans (S.recordOperator_normalized ω ℏ E β)

theorem StoppingSchedule.instrument_branch (ω ℏ E β : ℝ) (S : StoppingSchedule)
    (r : S.Record) (X : Mat) :
    (S.instrument ω ℏ E β).branch (S.recordEquiv r) X = S.branch ω ℏ E β r X := by
  change (∑ _ : Fin 1, S.recordOperator ω ℏ E β (S.recordEquiv.symm (S.recordEquiv r)) * X *
    (S.recordOperator ω ℏ E β (S.recordEquiv.symm (S.recordEquiv r)))ᴴ) = _
  rw [Equiv.symm_apply_apply, Fin.sum_univ_one, S.branch_eq_sandwich]

theorem StoppingSchedule.instrument_lift_branch (ω ℏ E β : ℝ) (S : StoppingSchedule)
    (r : S.Record) (A : Type*) [Fintype A] [DecidableEq A]
    (X : Matrix (Level × A) (Level × A) ℂ) :
    let W := S.recordOperator ω ℏ E β r ⊗ₖ (1 : Matrix A A ℂ)
    ((S.instrument ω ℏ E β).lift A).branch (S.recordEquiv r) X = W * X * Wᴴ := by
  let W := S.recordOperator ω ℏ E β (S.recordEquiv.symm (S.recordEquiv r))
    ⊗ₖ (1 : Matrix A A ℂ)
  change (∑ _ : Fin 1, W * X * Wᴴ) = _
  rw [Fin.sum_univ_one]
  simp only [W, Equiv.symm_apply_apply]

theorem StoppingSchedule.sum_trace (ω ℏ E β : ℝ) (S : StoppingSchedule) (X : Mat) :
    ∑ r : S.Record, (S.branch ω ℏ E β r X).trace = X.trace := by
  calc
    _ = ∑ r : S.Record, ((S.instrument ω ℏ E β).branch (S.recordEquiv r) X).trace := by
      simp only [S.instrument_branch]
    _ = ∑ a, ((S.instrument ω ℏ E β).branch a X).trace := by
      exact S.recordEquiv.sum_comp (fun a => ((S.instrument ω ℏ E β).branch a X).trace)
    _ = X.trace := (S.instrument ω ℏ E β).sum_trace X

theorem StoppingSchedule.first_marginal (ω ℏ E β s : ℝ) (next : Fin 3 → StoppingSchedule)
    (a : Fin 3) (X : Mat) :
    ∑ r : (next a).Record, ((StoppingSchedule.measure s next).branch ω ℏ E β ⟨a,r⟩ X).trace =
      ((clockInstrument ω ℏ E (-β * ℏ * s)).branch a X).trace :=
  (next a).sum_trace ω ℏ E β ((clockInstrument ω ℏ E (-β * ℏ * s)).branch a X)

def StoppingSchedule.reportedInstrument (ω ℏ E β : ℝ) {q : ℕ} (S : StoppingSchedule)
    (report : S.Record → Fin q) : FiniteInstrument Level q :=
  (S.instrument ω ℏ E β).relabel (fun a => report (S.recordEquiv.symm a))

theorem StoppingSchedule.reportedInstrument_branch (ω ℏ E β : ℝ) {q : ℕ} (S : StoppingSchedule)
    (report : S.Record → Fin q) (b : Fin q) (X : Mat) :
    (S.reportedInstrument ω ℏ E β report).branch b X =
      ∑ r ∈ Finset.univ.filter (fun r => report r = b), S.branch ω ℏ E β r X := by
  rw [StoppingSchedule.reportedInstrument, FiniteInstrument.relabel_branch]
  simp only [Finset.sum_filter]
  have h := S.recordEquiv.sum_comp (fun a =>
    if report (S.recordEquiv.symm a) = b then (S.instrument ω ℏ E β).branch a X else 0)
  rw [← h]
  simp only [Equiv.symm_apply_apply, StoppingSchedule.instrument_branch]


theorem StoppingSchedule.reportedInstrument_lift_branch (ω ℏ E β : ℝ) {q : ℕ}
    (S : StoppingSchedule) (report : S.Record → Fin q) (b : Fin q)
    (A : Type*) [Fintype A] [DecidableEq A] (X : Matrix (Level × A) (Level × A) ℂ) :
    ((S.reportedInstrument ω ℏ E β report).lift A).branch b X =
      ∑ r ∈ Finset.univ.filter (fun r => report r = b),
        let W := S.recordOperator ω ℏ E β r ⊗ₖ (1 : Matrix A A ℂ)
        W * X * Wᴴ := by
  rw [StoppingSchedule.reportedInstrument, FiniteInstrument.relabel_lift_branch]
  simp only [Finset.sum_filter]
  have h := S.recordEquiv.sum_comp (fun a =>
    if report (S.recordEquiv.symm a) = b then ((S.instrument ω ℏ E β).lift A).branch a X else 0)
  rw [← h]
  simp only [Equiv.symm_apply_apply, StoppingSchedule.instrument_lift_branch]

def Schedule.toStopping : {n : ℕ} → Schedule n → StoppingSchedule
  | _, .done => .done
  | _, .measure s next => .measure s (fun a => (next a).toStopping)

def Schedule.toStoppingRecord : {n : ℕ} → (S : Schedule n) → (Fin n → Fin 3) → S.toStopping.Record
  | _, .done, _ => ()
  | _, .measure _ next, r => ⟨r 0, (next (r 0)).toStoppingRecord (Fin.tail r)⟩

theorem Schedule.toStopping_branch (ω ℏ E β : ℝ) {n : ℕ} (S : Schedule n)
    (r : Fin n → Fin 3) (X : Mat) :
    S.toStopping.branch ω ℏ E β (S.toStoppingRecord r) X = S.branch ω ℏ E β r X := by
  induction S generalizing X with
  | done => rfl
  | measure s next ih =>
    exact ih (r 0) (Fin.tail r) ((clockInstrument ω ℏ E (-β * ℏ * s)).branch (r 0) X)

def StoppingSchedule.height : StoppingSchedule → ℕ
  | .done => 0
  | .measure _ next => (Finset.univ.sup fun a => (next a).height) + 1

theorem StoppingSchedule.path_length_le_height (S : StoppingSchedule) (r : S.Record) :
    (S.path r).length ≤ S.height := by
  induction S with
  | done => exact Nat.le_refl 0
  | measure s next ih =>
    change ((next r.1).path r.2).length + 1 ≤ (Finset.univ.sup fun a => (next a).height) + 1
    exact Nat.succ_le_succ ((ih r.1 r.2).trans (Finset.le_sup (f := fun a => (next a).height) (Finset.mem_univ r.1)))

/-- The reported duration counts actual measurements. -/
def StoppingSchedule.duration (S : StoppingSchedule) (r : S.Record) : Fin (S.height + 1) :=
  ⟨(S.path r).length, Nat.lt_succ_of_le (S.path_length_le_height r)⟩

def StoppingSchedule.durationInstrument (ω ℏ E β : ℝ) (S : StoppingSchedule) :
    FiniteInstrument Level (S.height + 1) :=
  S.reportedInstrument ω ℏ E β S.duration

theorem StoppingSchedule.durationInstrument_branch (ω ℏ E β : ℝ) (S : StoppingSchedule)
    (b : Fin (S.height + 1)) (X : Mat) :
    (S.durationInstrument ω ℏ E β).branch b X =
      ∑ r ∈ Finset.univ.filter (fun r => (S.path r).length = b.1), S.branch ω ℏ E β r X := by
  rw [StoppingSchedule.durationInstrument, S.reportedInstrument_branch]
  simp only [Fin.ext_iff, StoppingSchedule.duration]

private def equalWeightStop : StoppingSchedule :=
  .measure (Real.pi / 2) (fun a =>
    if a = (0 : Fin 2).castSucc then .done
    else .measure (Real.pi / 2) (fun _ => .done))

private def equalWeightEarly : equalWeightStop.Record :=
  ⟨(0 : Fin 2).castSucc, by simpa [equalWeightStop, StoppingSchedule.Record] using ()⟩

private def equalWeightLate : equalWeightStop.Record :=
  ⟨(1 : Fin 2).castSucc, ⟨(1 : Fin 2).castSucc, ()⟩⟩

private theorem quarterTurn_weight (E : ℝ) (a : Fin 2) :
    (clockInstrument 1 1 E (-(1 : ℝ) * 1 * (Real.pi / 2))).weight a.castSucc prepared =
      1 / 2 := by
  open QuantumNetwork.FiniteClockHandReadout in
  rw [clockInstrument_hand_weight 1 1 E 1 (Real.pi / 2) (by norm_num) a, mass,
    show -(1 : ℝ) * 1 * (Real.pi / 2) = -(Real.pi / (2 * 1)) by ring, p_reflection,
    p_quarter (by norm_num)]
  split <;> norm_num

/-- A quarter turn gives equal weight to a one-readout leaf and a two-readout leaf. -/
theorem stoppingClock_two_positive_durations (E : ℝ) :
    ∃ (S : StoppingSchedule) (r t : S.Record),
      (S.path r).length = 1 ∧ (S.path t).length = 2 ∧
      ((S.instrument 1 1 E 1).branch (S.recordEquiv r) prepared).trace.re = 1 / 2 ∧
      ((S.instrument 1 1 E 1).branch (S.recordEquiv t) prepared).trace.re = 1 / 2 := by
  refine ⟨equalWeightStop, equalWeightEarly, equalWeightLate, rfl, rfl, ?_, ?_⟩
  · rw [StoppingSchedule.instrument_branch]
    exact quarterTurn_weight E 0
  · rw [StoppingSchedule.instrument_branch]
    let τ := -(1 : ℝ) * 1 * (Real.pi / 2)
    let a := (1 : Fin 2).castSucc
    change ((clockInstrument 1 1 E τ).branch a
      ((clockInstrument 1 1 E τ).branch a prepared)).trace.re = _
    rw [clockInstrument_repeat, if_pos rfl]
    exact quarterTurn_weight E 1

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
