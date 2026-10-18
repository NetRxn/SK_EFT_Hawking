import SKEFTHawking.QuantumNetwork.FinitePersistentMeasuredHand

/-! # Persistent measured-hand trace distances
The signed insertion isometry applies to arbitrary complex reduced matrices.
The posterior |dp| identity has an explicit measured-sector premise.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FinitePersistentMeasuredHandErrors
open Matrix FiniteInterventionProcess FinitePersistentMeasuredHand
open scoped BigOperators ComplexOrder Kronecker
variable (F : Type*) [Fintype F] [DecidableEq F]

theorem insert_adjoint (Y : ReducedMat F) (Q : FiniteClockHandReadout.Mat) :
    (FiniteClockControlledRetainedMemory.insert F Y Q)ᴴ =
      FiniteClockControlledRetainedMemory.insert F Yᴴ Qᴴ := by
  ext x y
  simp [FiniteClockControlledRetainedMemory.insert, Matrix.conjTranspose_apply]

theorem insert_mul (Y Z : ReducedMat F) (Q R : FiniteClockHandReadout.Mat) :
    FiniteClockControlledRetainedMemory.insert F Y Q *
      FiniteClockControlledRetainedMemory.insert F Z R =
      FiniteClockControlledRetainedMemory.insert F (Y*Z) (Q*R) := by
  ext ⟨⟨b,u⟩,f⟩ ⟨⟨d,w⟩,g⟩
  simp only [FiniteClockControlledRetainedMemory.insert, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [mul_mul_mul_comm, Finset.sum_add_distrib, Finset.sum_mul, add_mul, mul_add]
  ring

theorem insert_absOp (Y : ReducedMat F) (a : A) :
    absOp (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) =
      FiniteClockControlledRetainedMemory.insert F (absOp Y) (FiniteClockHandReadout.Q a) := by
  apply posSemidef_eq_of_mul_self_eq (absOp_posSemidef _)
    (FiniteClockControlledRetainedMemory.insert_positive F (absOp_posSemidef Y)
      (FiniteClockHandReadout.Q_density a).1)
  rw [absOp_mul_self, insert_adjoint, insert_mul, insert_mul,
    FiniteClockHandReadout.Q_adjoint, FiniteClockHandReadout.Q_mul, if_pos rfl,
    absOp_mul_self]

/-- Rank-one measured-hand insertion preserves the entire signed trace norm. -/
theorem insert_traceNorm (Y : ReducedMat F) (a : A) :
    traceNorm (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) =
      traceNorm Y := by
  rw [traceNorm_eq_trace_absOp, insert_absOp,
    FiniteClockControlledRetainedMemory.insert_trace, FiniteClockHandReadout.Q_trace,
    mul_one, ← traceNorm_eq_trace_absOp]

theorem traceNorm_real_smul {D : Type*} [Fintype D] [DecidableEq D]
    (c : ℝ) (X : Matrix D D ℂ) : traceNorm ((c:ℂ) • X) = |c| * traceNorm X := by
  by_cases hc : 0 ≤ c
  · rw [traceNorm_smul_nonneg hc, abs_of_nonneg hc]
  · have hn : 0 ≤ -c := by linarith
    have he : (c:ℂ) • X = -(((-c:ℝ):ℂ) • X) := by simp
    rw [he, traceNorm_neg, traceNorm_smul_nonneg hn, abs_of_neg (lt_of_not_ge hc)]

theorem posterior_branch_difference {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ)
    (b a : A) (i : Fin 11) {Y : ReducedMat F} (hY : Y.PosSemidef) :
    traceNorm ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) -
      (step F ω ℏ s hℏ).branch S F 22 (outcomeEquiv (b,i))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a))) =
      |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| *
        (FiniteClockControlledRetainedMemory.dataBranch F b i Y).trace.re := by
  rw [branch_posterior, branch_posterior, ← sub_smul, ← Complex.ofReal_sub,
    traceNorm_real_smul, insert_traceNorm,
    traceNorm_posSemidef (FiniteClockControlledRetainedMemory.dataBranch_positive F b i hY)]
  congr 1
  unfold transition
  split <;> simp [abs_sub_comm]

theorem posterior_stepDistance_exact {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ)
    (a : A) {Y : ReducedMat F} (hY : Y.PosSemidef) :
    FiniteAdaptiveMapPerturbation.stepDistance S F 22 (step F ω ℏ t hℏ) (step F ω ℏ s hℏ)
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) =
      |FiniteClockHandReadout.p ω t-FiniteClockHandReadout.p ω s| * Y.trace.re := by
  unfold FiniteAdaptiveMapPerturbation.stepDistance
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, posterior_branch_difference F hℏ ω t s _ a _ hY,
    ← Finset.mul_sum, ← Complex.re_sum,
    FiniteClockControlledRetainedMemory.dataBranch_sum_trace, Fin.sum_univ_two]
  norm_num [Complex.mul_re]
  ring

def eta (θ φ : ℝ) : ℝ := |Real.sin ((θ-φ)/2)|
def midpointPhase (θ φ : ℝ) : ℝ := (θ+φ)/2+Real.pi/2

theorem phase_trig (θ : ℝ) : phase θ = (Real.cos θ : ℂ)-Complex.I*Real.sin θ := by
  rw [phase, show -Complex.I*(θ:ℂ) = ((-θ:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I]
  simp
  ring

theorem plus_phase_trig (θ : ℝ) :
    Complex.exp (Complex.I*θ) = (Real.cos θ : ℂ)+Complex.I*Real.sin θ := by
  rw [show Complex.I*(θ:ℂ) = (θ:ℂ)*Complex.I by ring, Complex.exp_ofReal_mul_I]
  ring

theorem extract_trig (θ : ℝ) (a : A) (Z : FullMat F) (bf dg : B × F) :
    extract F 1 1 θ a Z bf dg =
      (Z ((bf.1,0),bf.2) ((dg.1,0),dg.2) + Z ((bf.1,1),bf.2) ((dg.1,1),dg.2) +
        sign a*((Real.cos θ:ℂ)+Complex.I*Real.sin θ)*Z ((bf.1,0),bf.2) ((dg.1,1),dg.2) +
        sign a*((Real.cos θ:ℂ)-Complex.I*Real.sin θ)*Z ((bf.1,1),bf.2) ((dg.1,0),dg.2))/2 := by
  rw [extract_phase F (by norm_num : (1:ℝ) ≠ 0)]
  simp only [Complex.ofReal_one, one_mul]
  have hn : Complex.exp (-Complex.I*(θ:ℂ)) =
      (Real.cos θ:ℂ)-Complex.I*Real.sin θ := phase_trig θ
  rw [plus_phase_trig, hn]

theorem extract_frequency {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : A) (Z : FullMat F) :
    extract F ω ℏ t a Z = extract F 1 1 (ω*t) a Z := by
  ext bf dg
  have h := extract_phase F (by norm_num : (1:ℝ) ≠ 0) 1 (ω*t) a Z bf dg
  simp only [Complex.ofReal_one, Complex.ofReal_mul, one_mul] at h
  exact (extract_phase F hℏ ω t a Z bf dg).trans h.symm

/-- The unrestricted effect difference uses two PSD spectral compressions. -/
theorem compression_signed_difference (θ φ : ℝ) (Z : FullMat F) :
    extract F 1 1 θ 0 Z-extract F 1 1 φ 0 Z =
      (Real.sin ((θ-φ)/2) : ℂ) •
        (extract F 1 1 (midpointPhase θ φ) 0 Z-extract F 1 1 (midpointPhase θ φ) 1 Z) := by
  let m := (θ+φ)/2
  let d := (θ-φ)/2
  have ht : θ=m+d := by dsimp [m,d]; ring
  have hf : φ=m-d := by dsimp [m,d]; ring
  have hc : Real.cos θ = Real.cos φ-2*Real.sin m*Real.sin d := by
    rw [ht,hf,Real.cos_add,Real.cos_sub]
    ring
  have hs : Real.sin θ = Real.sin φ+2*Real.cos m*Real.sin d := by
    rw [ht,hf,Real.sin_add,Real.sin_sub]
    ring
  ext bf dg
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, extract_trig]
  change _ = (Real.sin d:ℂ)*_
  rw [show midpointPhase θ φ = m+Real.pi/2 from rfl]
  simp [sign, Real.cos_add, Real.sin_add,
    Real.cos_pi_div_two, Real.sin_pi_div_two, hc, hs]
  push_cast
  ring

def Vplus (θ φ : ℝ) (Z : FullMat F) : ReducedMat F :=
  if 0 ≤ Real.sin ((θ-φ)/2) then extract F 1 1 (midpointPhase θ φ) 0 Z
  else extract F 1 1 (midpointPhase θ φ) 1 Z

def Vminus (θ φ : ℝ) (Z : FullMat F) : ReducedMat F :=
  if 0 ≤ Real.sin ((θ-φ)/2) then extract F 1 1 (midpointPhase θ φ) 1 Z
  else extract F 1 1 (midpointPhase θ φ) 0 Z

theorem spectral_positive (θ φ : ℝ) {Z : FullMat F} (hZ : Z.PosSemidef) :
    (Vplus F θ φ Z).PosSemidef ∧ (Vminus F θ φ Z).PosSemidef := by
  unfold Vplus Vminus
  split <;> exact ⟨extract_positive F 1 1 _ _ hZ, extract_positive F 1 1 _ _ hZ⟩

theorem spectral_mass (θ φ : ℝ) (Z : FullMat F) :
    (Vplus F θ φ Z).trace+(Vminus F θ φ Z).trace = Z.trace := by
  have h := extract_sum_trace F (by norm_num : (1:ℝ) ≠ 0) 1 (midpointPhase θ φ) Z
  simp only [Fin.sum_univ_two] at h
  unfold Vplus Vminus
  split
  · exact h
  · exact (add_comm _ _).trans h

theorem spectral_difference (θ φ : ℝ) (Z : FullMat F) :
    extract F 1 1 θ 0 Z-extract F 1 1 φ 0 Z =
      (eta θ φ:ℂ) • (Vplus F θ φ Z-Vminus F θ φ Z) := by
  rw [compression_signed_difference]
  unfold Vplus Vminus eta
  split
  · rw [abs_of_nonneg ‹_›]
  · rw [abs_of_neg (lt_of_not_ge ‹_›)]
    ext x y
    simp
    ring

theorem insert_sub (Y Z : ReducedMat F) (Q : FiniteClockHandReadout.Mat) :
    FiniteClockControlledRetainedMemory.insert F (Y-Z) Q =
      FiniteClockControlledRetainedMemory.insert F Y Q-
        FiniteClockControlledRetainedMemory.insert F Z Q := by
  ext x y
  simp [FiniteClockControlledRetainedMemory.insert, sub_mul]

theorem dataBranch_sub (a : A) (i : Fin 11) (Y Z : ReducedMat F) :
    FiniteClockControlledRetainedMemory.dataBranch F a i (Y-Z) =
      FiniteClockControlledRetainedMemory.dataBranch F a i Y-
        FiniteClockControlledRetainedMemory.dataBranch F a i Z := by
  simp only [FiniteClockControlledRetainedMemory.dataBranch, krausMap,
    Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem data_jordan_contraction (a : A) {V W : ReducedMat F}
    (hV : V.PosSemidef) (hW : W.PosSemidef) :
    (∑ i : Fin 11, traceNorm (FiniteClockControlledRetainedMemory.dataBranch F a i (V-W))) ≤
      V.trace.re+W.trace.re := by
  calc
    _ = ∑ i : Fin 11, traceNorm (FiniteClockControlledRetainedMemory.dataBranch F a i V-
        FiniteClockControlledRetainedMemory.dataBranch F a i W) := by simp only [dataBranch_sub]
    _ ≤ ∑ i : Fin 11, (traceNorm (FiniteClockControlledRetainedMemory.dataBranch F a i V)+
        traceNorm (FiniteClockControlledRetainedMemory.dataBranch F a i W)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [sub_eq_add_neg]
      exact (traceNorm_add_le _ _).trans_eq (by rw [traceNorm_neg])
    _ = _ := by
      simp only [traceNorm_posSemidef (FiniteClockControlledRetainedMemory.dataBranch_positive F a _ hV),
        traceNorm_posSemidef (FiniteClockControlledRetainedMemory.dataBranch_positive F a _ hW),
        Finset.sum_add_distrib, ← Complex.re_sum,
        FiniteClockControlledRetainedMemory.dataBranch_sum_trace]

theorem other_compression_difference (θ φ : ℝ) (Z : FullMat F) :
    extract F 1 1 θ 1 Z-extract F 1 1 φ 1 Z =
      -(extract F 1 1 θ 0 Z-extract F 1 1 φ 0 Z) := by
  have hθ := extract_sum F (by norm_num : (1:ℝ) ≠ 0) 1 θ Z
  have hφ := extract_sum F (by norm_num : (1:ℝ) ≠ 0) 1 φ Z
  simp only [Fin.sum_univ_two] at hθ hφ
  have ht : extract F 1 1 θ 1 Z = FiniteClockControlledRetainedMemory.handTrace F Z-
      extract F 1 1 θ 0 Z := (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hθ)
  have hf : extract F 1 1 φ 1 Z = FiniteClockControlledRetainedMemory.handTrace F Z-
      extract F 1 1 φ 0 Z := (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hφ)
  rw [ht,hf]
  abel

theorem spectral_arm_difference (θ φ : ℝ) (a : A) (Z : FullMat F) :
    extract F 1 1 θ a Z-extract F 1 1 φ a Z =
      (eta θ φ:ℂ) • (if a=0 then Vplus F θ φ Z-Vminus F θ φ Z
        else Vminus F θ φ Z-Vplus F θ φ Z) := by
  rcases (show a=0 ∨ a=1 by fin_cases a <;> decide) with rfl | rfl
  · simpa only [if_pos rfl, ite_true] using spectral_difference F θ φ Z
  · rw [other_compression_difference, spectral_difference]
    simp only [show (1:A) ≠ 0 by decide, if_false]
    module

theorem arm_error_bound {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ) (a : A)
    {Z : FullMat F} (hZ : Z.PosSemidef) :
    (∑ i : Fin 11, traceNorm ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z-
      (step F ω ℏ s hℏ).branch S F 22 (outcomeEquiv (a,i)) Z)) ≤
      eta (ω*t) (ω*s)*Z.trace.re := by
  have hp := spectral_positive F (ω*t) (ω*s) hZ
  have hm := congrArg Complex.re (spectral_mass F (ω*t) (ω*s) Z)
  simp only [Complex.add_re] at hm
  have hi (i : Fin 11) :
      traceNorm ((step F ω ℏ t hℏ).branch S F 22 (outcomeEquiv (a,i)) Z-
        (step F ω ℏ s hℏ).branch S F 22 (outcomeEquiv (a,i)) Z) =
      eta (ω*t) (ω*s) * traceNorm (FiniteClockControlledRetainedMemory.dataBranch F a i
        (if a=0 then Vplus F (ω*t) (ω*s) Z-Vminus F (ω*t) (ω*s) Z
          else Vminus F (ω*t) (ω*s) Z-Vplus F (ω*t) (ω*s) Z)) := by
    rw [branch_action,branch_action, ← insert_sub, ← dataBranch_sub,
      extract_frequency F hℏ, extract_frequency F hℏ, spectral_arm_difference]
    simp only [FiniteClockControlledRetainedMemory.dataBranch, krausMap_smul, insert_smul,
      traceNorm_real_smul, abs_of_nonneg (abs_nonneg _), insert_traceNorm, eta]
  simp only [hi, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  split
  · exact (data_jordan_contraction F a hp.1 hp.2).trans_eq hm
  · exact (data_jordan_contraction F a hp.2 hp.1).trans_eq ((add_comm _ _).trans hm)

/-- Unrestricted sharp coefficient, scaling with PSD mass rather than normalization. -/
theorem stepDistance_bound {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ)
    {Z : FullMat F} (hZ : Z.PosSemidef) :
    FiniteAdaptiveMapPerturbation.stepDistance S F 22 (step F ω ℏ t hℏ) (step F ω ℏ s hℏ) Z ≤
      eta (ω*t) (ω*s)*Z.trace.re := by
  unfold FiniteAdaptiveMapPerturbation.stepDistance
  rw [← outcomeEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0 := arm_error_bound F hℏ ω t s 0 hZ
  have h1 := arm_error_bound F hℏ ω t s 1 hZ
  linarith

theorem localError {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ) :
    FiniteAdaptiveMapPerturbation.LocalError S F 22 (step F ω ℏ t hℏ) (step F ω ℏ s hℏ)
      (eta (ω*t) (ω*s)) := by
  refine ⟨abs_nonneg _, fun Z hZ => ?_⟩
  simpa only [hZ.2, Complex.one_re, mul_one] using stepDistance_bound F hℏ ω t s hZ.1

theorem eta_bound (θ φ : ℝ) : eta θ φ ≤ min 1 (|θ-φ|/2) := by
  refine le_min (Real.abs_sin_le_one _) ?_
  exact Real.abs_sin_le_abs.trans_eq (by rw [abs_div]; norm_num)

theorem eta_zero_compression {θ φ : ℝ} (h : eta θ φ=0) (Z : FullMat F) :
    extract F 1 1 θ 0 Z = extract F 1 1 φ 0 Z := by
  have hd := spectral_difference F θ φ Z
  rw [h, Complex.ofReal_zero, zero_smul] at hd
  exact sub_eq_zero.mp hd

inductive PhasePolicyErrors (ω : ℝ) : {n : ℕ} → Policy n → Policy n → List ℝ → Prop
  | done : PhasePolicyErrors ω .done .done []
  | node {n : ℕ} {t s : Duration} {P Q : Fin 22 → Policy n} {e : ℝ} {es : List ℝ}
      (bound : eta (ω*t) (ω*s) ≤ e) (length : es.length=n)
      (next : ∀ o, PhasePolicyErrors ω (P o) (Q o) es) :
      PhasePolicyErrors ω (.node t P) (.node s Q) (e::es)

theorem policy_pairedErrors {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n}
    {es : List ℝ} (h : PhasePolicyErrors ω P Q es) :
    FiniteAdaptiveMapPerturbation.PairedErrors S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q) es := by
  induction h with
  | done => exact .done
  | @node n t s P Q e es hb hlen hn ih =>
    apply FiniteAdaptiveMapPerturbation.PairedErrors.node
    · have hl := localError F hℏ ω t s
      exact ⟨(abs_nonneg _).trans hb, fun Z hZ => (hl.2 Z hZ).trans hb⟩
    · exact hlen
    · exact ih

theorem policy_capped {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n}
    {es : List ℝ} (h : PhasePolicyErrors ω P Q es) {X Y : FullMat F}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    FiniteAdaptiveMapPerturbation.outputDistance S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q) X Y ≤ min 1 (traceDist X Y+es.sum) :=
  FiniteAdaptiveMapPerturbation.pairedErrors_capped S F 22 (policy_pairedErrors F hℏ h) hX hY

def terminalProbability (ω ℏ : ℝ) (hℏ : ℏ ≠ 0) {n : ℕ} (P : Policy n)
    (effect : History 22 n → FullMat F) (X : FullMat F) : ℝ :=
  ∑ h, (effect h*run S F 22 (policyTree F ω ℏ hℏ P) h X).trace.re

theorem policy_event_error {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n}
    {es : List ℝ} (h : PhasePolicyErrors ω P Q es) {X Y : FullMat F}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (effect : History 22 n → FullMat F) (he : ∀ h, IsBinaryPOVM (effect h)) :
    |terminalProbability F ω ℏ hℏ P effect X-terminalProbability F ω ℏ hℏ Q effect Y| ≤
      min 1 (traceDist X Y+es.sum) := by
  have hb := FiniteAdaptiveReadoutRobustness.bounded_observable_difference
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ P) hX)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ Q) hY) effect he
  rw [FiniteAdaptiveReadoutRobustness.tree_branchDistance] at hb
  exact hb.trans (policy_capped F hℏ h hX hY)

/-- A measured posterior earns a sharper continuation bound on every recorded arm. -/
theorem continuation_bound {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t s : ℝ) {n : ℕ}
    (P Q : Fin 22 → Tree S F 22 n) (E : ℝ)
    (hn : ∀ o (Y : ReducedMat F), Y.PosSemidef →
      FiniteAdaptiveMapPerturbation.outputDistance S F 22 (P o) (Q o)
        (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q (outcomeEquiv.symm o).1))
        (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q (outcomeEquiv.symm o).1)) ≤
        E*Y.trace.re)
    {Z : FullMat F} (hZ : Z.PosSemidef) :
    FiniteAdaptiveMapPerturbation.outputDistance S F 22
      (.node (step F ω ℏ t hℏ) P) (.node (step F ω ℏ s hℏ) Q) Z Z ≤
      FiniteAdaptiveMapPerturbation.stepDistance S F 22 (step F ω ℏ t hℏ) (step F ω ℏ s hℏ) Z+
        E*Z.trace.re := by
  have hi (o : Fin 22) :
      FiniteAdaptiveMapPerturbation.outputDistance S F 22 (P o) (Q o)
        ((step F ω ℏ t hℏ).branch S F 22 o Z) ((step F ω ℏ s hℏ).branch S F 22 o Z) ≤
      traceDist ((step F ω ℏ t hℏ).branch S F 22 o Z) ((step F ω ℏ s hℏ).branch S F 22 o Z)+
        E*((step F ω ℏ s hℏ).branch S F 22 o Z).trace.re := by
    have ht := branch_positive F hℏ ω t o hZ
    have hs := branch_positive F hℏ ω s o hZ
    apply (FiniteAdaptiveMapPerturbation.outputDistance_triangle S F 22
      (P o) (P o) (Q o) _ _ _).trans
    apply add_le_add (FiniteAdaptiveMapPerturbation.outputDistance_common S F 22 (P o)
      ht.isHermitian hs.isHermitian)
    obtain ⟨⟨a,i⟩,rfl⟩ := outcomeEquiv.surjective o
    rw [branch_action]
    have hh := hn (outcomeEquiv (a,i))
      (FiniteClockControlledRetainedMemory.dataBranch F a i (extract F ω ℏ s a Z))
      (FiniteClockControlledRetainedMemory.dataBranch_positive F a i (extract_positive F ω ℏ s a hZ))
    simp only [Equiv.symm_apply_apply] at hh
    simpa only [FiniteClockControlledRetainedMemory.insert_trace,
      FiniteClockHandReadout.Q_trace, mul_one] using hh
  rw [FiniteAdaptiveMapPerturbation.outputDistance_node]
  apply (Finset.sum_le_sum (fun o _ => hi o)).trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.re_sum, branches_trace]
  unfold FiniteAdaptiveMapPerturbation.stepDistance traceDist
  rw [Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem posterior_policy_bound {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n}
    {es : List ℝ} (h : FiniteClockControlledRetainedMemory.PolicyErrors ω P Q es)
    (a : A) {Y : ReducedMat F} (hY : Y.PosSemidef) :
    FiniteAdaptiveMapPerturbation.outputDistance S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q)
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a))
      (FiniteClockControlledRetainedMemory.insert F Y (FiniteClockHandReadout.Q a)) ≤ es.sum*Y.trace.re := by
  induction h generalizing a Y with
  | done => simp [policyTree, FiniteAdaptiveMapPerturbation.outputDistance_done, traceDist_self]
  | @node n t s P Q e es hb hlen hn ih =>
    have hc := continuation_bound F hℏ ω t s
      (fun o => policyTree F ω ℏ hℏ (P o)) (fun o => policyTree F ω ℏ hℏ (Q o)) es.sum
      (fun o V hV => ih o (outcomeEquiv.symm o).1 hV)
      (FiniteClockControlledRetainedMemory.insert_positive F hY (FiniteClockHandReadout.Q_density a).1)
    rw [posterior_stepDistance_exact F hℏ ω t s a hY,
      FiniteClockControlledRetainedMemory.insert_trace, FiniteClockHandReadout.Q_trace, mul_one] at hc
    have hm : 0 ≤ Y.trace.re := by
      rw [← traceNorm_posSemidef hY]
      exact traceNorm_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hb hm
    change _ ≤ (e::es).sum*Y.trace.re
    simpa only [policyTree, List.sum_cons, add_mul] using hc.trans (add_le_add hmul le_rfl)

/-- Root uses the unrestricted coefficient; every later prefix uses its proved measured sector. -/
inductive ReachableErrors (ω : ℝ) : {n : ℕ} → Policy n → Policy n → List ℝ → Prop
  | done : ReachableErrors ω .done .done []
  | node {n : ℕ} {t s : Duration} {P Q : Fin 22 → Policy n} {e : ℝ} {es : List ℝ}
      (bound : eta (ω*t) (ω*s) ≤ e) (length : es.length=n)
      (next : ∀ o, FiniteClockControlledRetainedMemory.PolicyErrors ω (P o) (Q o) es) :
      ReachableErrors ω (.node t P) (.node s Q) (e::es)

theorem reachable_same_input {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n}
    {es : List ℝ} (h : ReachableErrors ω P Q es) {Z : FullMat F} (hZ : Z.PosSemidef) :
    FiniteAdaptiveMapPerturbation.outputDistance S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q) Z Z ≤ es.sum*Z.trace.re := by
  cases h with
  | done => simp [policyTree, FiniteAdaptiveMapPerturbation.outputDistance_done, traceDist_self]
  | @node n t s P Q e es hb hlen hn =>
    have hc := continuation_bound F hℏ ω t s
      (fun o => policyTree F ω ℏ hℏ (P o)) (fun o => policyTree F ω ℏ hℏ (Q o)) es.sum
      (fun o V hV => posterior_policy_bound F hℏ (hn o) (outcomeEquiv.symm o).1 hV) hZ
    have hm : 0 ≤ Z.trace.re := by rw [← traceNorm_posSemidef hZ]; exact traceNorm_nonneg _
    have hs := (stepDistance_bound F hℏ ω t s hZ).trans (mul_le_mul_of_nonneg_right hb hm)
    simpa only [policyTree, List.sum_cons, add_mul] using hc.trans (add_le_add hs le_rfl)

theorem reachable_capped {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n}
    {es : List ℝ} (h : ReachableErrors ω P Q es) {X Y : FullMat F}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    FiniteAdaptiveMapPerturbation.outputDistance S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q) X Y ≤ min 1 (traceDist X Y+es.sum) := by
  apply le_min
  · have hm := FiniteAdaptiveMapPerturbation.outputDistance_mass S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q) hX.1 hY.1
    simpa only [hX.2,hY.2,Complex.one_re, show ((1:ℝ)+1)/2=1 by norm_num] using hm
  · have ht := FiniteAdaptiveMapPerturbation.outputDistance_triangle S F 22
      (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ P) (policyTree F ω ℏ hℏ Q) X Y Y
    have hi := FiniteAdaptiveMapPerturbation.outputDistance_common S F 22
      (policyTree F ω ℏ hℏ P) hX.1.isHermitian hY.1.isHermitian
    have hn := reachable_same_input F hℏ h hY.1
    simp only [hY.2,Complex.one_re,mul_one] at hn
    exact ht.trans (add_le_add hi hn)

theorem reachable_event_error {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ} {P Q : Policy n}
    {es : List ℝ} (h : ReachableErrors ω P Q es) {X Y : FullMat F}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y)
    (effect : History 22 n → FullMat F) (he : ∀ h, IsBinaryPOVM (effect h)) :
    |terminalProbability F ω ℏ hℏ P effect X-terminalProbability F ω ℏ hℏ Q effect Y| ≤
      min 1 (traceDist X Y+es.sum) := by
  have hb := FiniteAdaptiveReadoutRobustness.bounded_observable_difference
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ P) hX)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ Q) hY) effect he
  rw [FiniteAdaptiveReadoutRobustness.tree_branchDistance] at hb
  exact hb.trans (reachable_capped F hℏ h hX hY)

theorem reachable_optimalReadout_stability {ω ℏ : ℝ} (hℏ : ℏ ≠ 0) {n : ℕ}
    {PA PB QA QB : Policy n} {esA esB : List ℝ}
    (hA : ReachableErrors ω PA QA esA) (hB : ReachableErrors ω PB QB esB)
    {XA XB YA YB : FullMat F}
    (hXA : IsDensityOperator XA) (hXB : IsDensityOperator XB)
    (hYA : IsDensityOperator YA) (hYB : IsDensityOperator YB) :
    |FiniteAdaptiveReadoutRobustness.instrumentError
      (fun h => run S F 22 (policyTree F ω ℏ hℏ QA) h YA)
      (fun h => run S F 22 (policyTree F ω ℏ hℏ QB) h YB)
      (FiniteAdaptiveReadoutDiscrimination.optimalReadout
        (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ PA) hXA)
        (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ PB) hXB))-
      (1-FiniteAdaptiveMapPerturbation.outputDistance S F 22
        (policyTree F ω ℏ hℏ PA) (policyTree F ω ℏ hℏ PB) XA XB)/2| ≤
      (min 1 (traceDist XA YA+esA.sum)+min 1 (traceDist XB YB+esB.sum))/2 := by
  have hh := FiniteAdaptiveReadoutRobustness.transported_optimalReadout_stability
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ PA) hXA)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ PB) hXB)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ QA) hYA)
    (FiniteAdaptiveReadoutDiscrimination.run_family (policyTree F ω ℏ hℏ QB) hYB)
  simp only [FiniteAdaptiveReadoutRobustness.tree_branchDistance] at hh
  exact hh.trans (div_le_div_of_nonneg_right
    (add_le_add (reachable_capped F hℏ hA hXA hYA) (reachable_capped F hℏ hB hXB hYB)) (by norm_num))

end SKEFTHawking.QuantumNetwork.FinitePersistentMeasuredHandErrors
