import SKEFTHawking.ClassicalFlowTimeStability

/-! Classical energy stability on actual restarted time windows. Each window carries
its own support, finite-energy and continuous gradient-envelope hypotheses. -/
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SKEFTHawking.ClassicalFlowWindowStability
open NavierStokesR3 ProblemStatement Comparison
open NavierStokes.ProblemStatement (temporalDerivative spatialDerivative spatialDivergence)

/-- Translate the time argument without changing spatial coordinates or field values. -/
def timeShift {V : Type*} (a : ℝ) (f : ℝ × Space → V) : ℝ × Space → V :=
  fun z => f (z.1 + a, z.2)

theorem shift_time_mem {a b s : ℝ} (hs : s ∈ Icc 0 (b-a)) : s+a ∈ Icc a b := by
  constructor <;> linarith [hs.1, hs.2]

theorem shift_time_mem_open {a b s : ℝ} (hs : s ∈ Ioo 0 (b-a)) : s+a ∈ Ioo a b := by
  constructor <;> linarith [hs.1, hs.2]

theorem timeShift_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} {f : ℝ × Space → V} (hf : ContDiffOn ℝ ∞ f (slab a b)) :
    ContDiffOn ℝ ∞ (timeShift a f) (slab 0 (b-a)) := by
  apply hf.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
  intro z hz
  exact ⟨shift_time_mem hz.1, mem_univ _⟩

theorem timeShift_temporal (a : ℝ) (u : VelocityField) (s : ℝ) (x : Space) :
    temporalDerivative (timeShift a u) s x = temporalDerivative u (s+a) x := by
  unfold temporalDerivative timeShift
  exact congrArg (fun L : ℝ →L[ℝ] Space => L 1)
    (fderiv_comp_add_right (𝕜 := ℝ) (f := fun t => u (t,x)) (x := s) a)

theorem timeShift_spatial (a : ℝ) (u : VelocityField) (s : ℝ) (x : Space) :
    spatialDerivative (timeShift a u) s x = spatialDerivative u (s+a) x := rfl

theorem timeShift_divergence (a : ℝ) (u : VelocityField) (s : ℝ) (x : Space) :
    spatialDivergence (timeShift a u) s x = spatialDivergence u (s+a) x := rfl

theorem timeShift_residual (a ν : ℝ) (u : VelocityField) (p : PressureField) (s : ℝ) (x : Space) :
    navierStokesResidual ν (timeShift a u) (timeShift a p) s x =
      navierStokesResidual ν u p (s+a) x := by
  unfold navierStokesResidual
  rw [timeShift_temporal]
  rfl

theorem timeShift_energy {a b : ℝ} {u : VelocityField}
    (he : UniformFiniteEnergy (Icc a b) u) :
    UniformFiniteEnergy (Icc 0 (b-a)) (timeShift a u) := by
  obtain ⟨C,hC,he⟩ := he
  exact ⟨C,hC,fun s hs => he (s+a) (shift_time_mem hs)⟩

theorem timeShift_support {a b : ℝ} {u : VelocityField} {K : Set Space}
    (hs : ∀ t ∈ Icc a b, tsupport (fun x => u (t,x)) ⊆ K) :
    ∀ s ∈ Icc 0 (b-a), tsupport (fun x => timeShift a u (s,x)) ⊆ K :=
  fun s ht => hs (s+a) (shift_time_mem ht)

theorem timeShift_integral (a t : ℝ) (g : ℝ → ℝ) :
    (∫ s in 0..(t-a), g (s+a)) = ∫ s in a..t, g s := by
  rw [intervalIntegral.integral_comp_add_right]
  simp

/-- PDE hypotheses on one closed window; support and energy bounds are window-local. -/
structure Window (a b : ℝ) (u v : VelocityField) (p q : PressureField) (g : ℝ → ℝ) : Prop where
  ordered : a ≤ b
  smooth_u : ContDiffOn ℝ ∞ u (slab a b)
  smooth_v : ContDiffOn ℝ ∞ v (slab a b)
  smooth_p : ContDiffOn ℝ ∞ p (slab a b)
  smooth_q : ContDiffOn ℝ ∞ q (slab a b)
  support : ∃ K : Set Space, IsCompact K ∧ ∀ t ∈ Icc a b, tsupport (fun x => u (t,x)) ⊆ K
  energy : UniformFiniteEnergy (Icc a b) v
  div_u : ∀ t ∈ Ioo a b, ∀ x, spatialDivergence u t x = 0
  div_v : ∀ t ∈ Ioo a b, ∀ x, spatialDivergence v t x = 0
  equation : ∀ t ∈ Ioo a b, ∀ x, navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x
  envelope : ContinuousOn g (Icc a b)
  nonnegative : ∀ t ∈ Icc a b, 0 ≤ g t
  gradient : ∀ t ∈ Icc a b, ∀ x, ‖spatialDerivative u t x‖ ≤ g t

/-- Actual squared difference energy, with integrability supplied by each PDE window. -/
def errorEnergy (u v : VelocityField) (t : ℝ) : ℝ := l2Sq (fun x => (u-v) (t,x))

/-- Restart the actual PDE at a, including the zero-length window directly. -/
theorem window_energy {a b : ℝ} {u v : VelocityField} {p q : PressureField} {g : ℝ → ℝ}
    (h : Window a b u v p q g) :
    ∀ t ∈ Icc a b, errorEnergy u v t ≤ errorEnergy u v a * Real.exp (2 * ∫ s in a..t, g s) := by
  intro t ht
  by_cases hab : a = b
  · have hta : t = a := by linarith [ht.1, ht.2]
    subst t
    simp
  · have hpos : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne h.ordered hab)
    obtain ⟨K,hK,hs⟩ := h.support
    have hg : ContinuousOn (fun s => g (s+a)) (Icc 0 (b-a)) :=
      h.envelope.comp (continuous_id.add continuous_const).continuousOn (fun s hs => shift_time_mem hs)
    have he := ClassicalFlowTimeStability.classical_energy_stability_of_time_gradient hpos
      (timeShift_smooth h.smooth_u) (timeShift_smooth h.smooth_v)
      (timeShift_smooth h.smooth_p) (timeShift_smooth h.smooth_q) hK (timeShift_support hs)
      (timeShift_energy h.energy)
      (fun s hs x => (timeShift_divergence a u s x).trans (h.div_u (s+a) (shift_time_mem_open hs) x))
      (fun s hs x => (timeShift_divergence a v s x).trans (h.div_v (s+a) (shift_time_mem_open hs) x))
      (fun s hs x => by rw [timeShift_residual, timeShift_residual]; exact h.equation _ (shift_time_mem_open hs) x)
      hg (fun s hs => h.nonnegative _ (shift_time_mem hs))
      (fun s hs x => h.gradient _ (shift_time_mem hs) x)
    have hta : t-a ∈ Icc 0 (b-a) := by constructor <;> linarith [ht.1, ht.2]
    have hx := he (t-a) hta
    rw [timeShift_integral] at hx
    simpa only [errorEnergy, timeShift, Pi.sub_apply, sub_add_cancel, zero_add] using hx

/-- Two independently verified windows chain through the actual intermediate energy.
No continuity between their two envelopes is assumed. -/
theorem two_window_energy {a b c : ℝ} {u v : VelocityField} {p q : PressureField}
    {g h : ℝ → ℝ} (h1 : Window a b u v p q g) (h2 : Window b c u v p q h) :
    ∀ t ∈ Icc b c, errorEnergy u v t ≤ errorEnergy u v a *
      Real.exp (2 * ((∫ s in a..b, g s) + ∫ s in b..t, h s)) := by
  intro t ht
  have hb := window_energy h1 b ⟨h1.ordered, le_rfl⟩
  calc
    errorEnergy u v t ≤ errorEnergy u v b * Real.exp (2 * ∫ s in b..t, h s) := window_energy h2 t ht
    _ ≤ (errorEnergy u v a * Real.exp (2 * ∫ s in a..b, g s)) *
        Real.exp (2 * ∫ s in b..t, h s) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- A finite partition chains actual PDE windows with independently continuous envelopes. -/
theorem finite_partition_energy {u v : VelocityField} {p q : PressureField}
    (τ : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (n : ℕ)
    (hw : ∀ i < n, Window (τ i) (τ (i+1)) u v p q (g i)) :
    errorEnergy u v (τ n) ≤ errorEnergy u v (τ 0) *
      Real.exp (2 * ∑ i ∈ Finset.range n, ∫ s in τ i..τ (i+1), g i s) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := hw n (Nat.lt_succ_self n)
      have hp := ih (fun i hi => hw i (Nat.lt_succ_of_lt hi))
      have he := window_energy hn (τ (n+1)) ⟨hn.ordered, le_rfl⟩
      calc
        errorEnergy u v (τ (n+1)) ≤ errorEnergy u v (τ n) *
            Real.exp (2 * ∫ s in τ n..τ (n+1), g n s) := he
        _ ≤ (errorEnergy u v (τ 0) *
              Real.exp (2 * ∑ i ∈ Finset.range n, ∫ s in τ i..τ (i+1), g i s)) *
            Real.exp (2 * ∫ s in τ n..τ (n+1), g n s) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = _ := by
          rw [Finset.sum_range_succ, mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- Restriction preserves all actual PDE obligations, including local support and energy. -/
theorem Window.restrict {a b c d : ℝ} {u v : VelocityField} {p q : PressureField}
    {g : ℝ → ℝ} (h : Window a d u v p q g) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    Window b c u v p q g := by
  have hi : Icc b c ⊆ Icc a d := Icc_subset_Icc hab hcd
  have ho : Ioo b c ⊆ Ioo a d := fun t ht => ⟨hab.trans_lt ht.1, ht.2.trans_le hcd⟩
  have hs : slab b c ⊆ slab a d := fun z hz => ⟨hi hz.1, hz.2⟩
  obtain ⟨K,hK,hS⟩ := h.support
  obtain ⟨C,hC,hE⟩ := h.energy
  exact ⟨hbc,h.smooth_u.mono hs,h.smooth_v.mono hs,h.smooth_p.mono hs,h.smooth_q.mono hs,
    ⟨K,hK,fun t ht => hS t (hi ht)⟩,⟨C,hC,fun t ht => hE t (hi ht)⟩,
    fun t ht => h.div_u t (ho ht),fun t ht => h.div_v t (ho ht),
    fun t ht => h.equation t (ho ht),h.envelope.mono hi,
    fun t ht => h.nonnegative t (hi ht),fun t ht => h.gradient t (hi ht)⟩

/-- Splitting a continuous envelope produces exactly the original accumulated exponent. -/
theorem split_integral_exponent {a b c : ℝ} {g : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hg : ContinuousOn g (Icc a c)) :
    2 * ((∫ s in a..b, g s) + ∫ s in b..c, g s) = 2 * ∫ s in a..c, g s := by
  rw [intervalIntegral.integral_add_adjacent_intervals
    ((hg.mono (Icc_subset_Icc le_rfl hbc)).intervalIntegrable_of_Icc hab)
    ((hg.mono (Icc_subset_Icc hab le_rfl)).intervalIntegrable_of_Icc hbc)]

/-- Actual restart at b and recombination recover the unsplit bound, rather than assuming it. -/
theorem split_window_energy {a b c : ℝ} {u v : VelocityField} {p q : PressureField}
    {g : ℝ → ℝ} (h : Window a c u v p q g) (hab : a ≤ b) (hbc : b ≤ c) :
    errorEnergy u v c ≤ errorEnergy u v a * Real.exp (2 * ∫ s in a..c, g s) := by
  have hleft := h.restrict le_rfl hab hbc
  have hright := h.restrict hab hbc le_rfl
  have he := two_window_energy hleft hright c ⟨hbc,le_rfl⟩
  rw [split_integral_exponent hab hbc h.envelope] at he
  exact he

/-- The zero-based API is recovered with its original energy and integral. -/
theorem zero_based_energy {T : ℝ} {u v : VelocityField} {p q : PressureField}
    {g : ℝ → ℝ} (h : Window 0 T u v p q g) :
    ∀ t ∈ Icc 0 T, l2Sq (fun x => (u-v) (t,x)) ≤
      l2Sq (fun x => (u-v) (0,x)) * Real.exp (2 * ∫ s in 0..t, g s) :=
  window_energy h

end SKEFTHawking.ClassicalFlowWindowStability
