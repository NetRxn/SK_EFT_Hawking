import SKEFTHawking.FiniteNontracialObservableTransfer

noncomputable section
namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection NontracialReflectionDynamics FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

/-- The actual half-time split tree has one normalized composed Kraus step, even at depth zero. -/
def historyHalfSplitPositiveTree (p : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => .node (halfSplitStep p.value γ η t p.nonnegative p.bounded hγ hη ht) (fun _ => .done)
  | r::rs => .node (halfSplitStep p.value γ η t p.nonnegative p.bounded hγ hη ht)
      (fun _ => historyPositiveTree r rs)

/-- Separate all-complex trace for the half-time split process. -/
theorem history_half_split_positive_trace (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u : Labels rs) (X : Mat2) :
    (run (Fin 2) Unit 6 (historyHalfSplitPositiveTree p γ η t hγ hη ht rs) u
      (GibbsMultilevelReflection.joint X)).trace =
      (observable γ η (t/2) (Psi p.value (historyEffect rs u))*X).trace := by
  cases rs with
  | nil =>
    rcases u with ⟨i,⟨⟩⟩
    simp only [historyHalfSplitPositiveTree, run, halfSplitStep_branch,
      GibbsMultilevelReflection.joint_trace, branch_trace]
    rw [NontracialReflectionDynamics.trace_dual, Phi_Psi_duality,
      observable_Psi p.value γ η (t/2) hγ hη (by positivity)]
    rfl
  | cons r rs =>
    change (run (Fin 2) Unit 6 (historyPositiveTree r rs) u.2
      ((halfSplitStep p.value γ η t p.nonnegative p.bounded hγ hη ht).branch
        (Fin 2) Unit 6 u.1 (GibbsMultilevelReflection.joint X))).trace = _
    rw [halfSplitStep_branch, history_positive_trace, trace_duality,
      NontracialReflectionDynamics.trace_dual, Phi_Psi_duality,
      observable_Psi p.value γ η (t/2) hγ hη (by positivity)]
    rfl

/-- Actual half-time split probabilities are nonnegative and sum to one. -/
theorem history_half_split_normalized (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∀ u, 0 ≤ weight (Fin 2) Unit 6 (historyHalfSplitPositiveTree p γ η t hγ hη ht rs) u
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ u, weight (Fin 2) Unit 6 (historyHalfSplitPositiveTree p γ η t hγ hη ht rs) u
      (GibbsMultilevelReflection.joint rhoN))=1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

/-- Ordinary split singleton effect, identified as a joint matrix using every complex input. -/
theorem history_split_indicator_effect (p : Gap) (rs : List Gap) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (historyPositiveTree p rs)
      (PauliHistoryConsistency.indicatorScore u) =
      GibbsMultilevelReflection.joint (Psi p.value (historyEffect rs u)) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := PauliHistoryConsistency.joint_surjective X
  rw [PauliHistoryConsistency.effect_complex_trace]
  simp only [PauliHistoryConsistency.indicatorScore, apply_ite, ite_mul,
    Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [history_positive_trace]
  rw [GibbsMultilevelReflection.joint, GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker]
  simp [Matrix.trace]

/-- The actual inserted unsplit suffix uses p squared and full inserted time. -/
theorem history_unsplit_indicator_effect (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (historyInsertedPositiveTree p γ η t hγ hη ht rs)
      (PauliHistoryConsistency.indicatorScore u) =
      GibbsMultilevelReflection.joint (Psi (p.value*p.value) (observable γ η t (historyEffect rs u))) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := PauliHistoryConsistency.joint_surjective X
  rw [PauliHistoryConsistency.effect_complex_trace]
  simp only [PauliHistoryConsistency.indicatorScore, apply_ite, ite_mul,
    Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [history_inserted_positive_trace]
  rw [GibbsMultilevelReflection.joint, GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker]
  simp [Matrix.trace]

/-- Third actual singleton effect: half inserted time after the split retention p. -/
theorem history_half_split_indicator_effect (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (historyHalfSplitPositiveTree p γ η t hγ hη ht rs)
      (PauliHistoryConsistency.indicatorScore u) =
      GibbsMultilevelReflection.joint (observable γ η (t/2) (Psi p.value (historyEffect rs u))) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := PauliHistoryConsistency.joint_surjective X
  rw [PauliHistoryConsistency.effect_complex_trace]
  simp only [PauliHistoryConsistency.indicatorScore, apply_ite, ite_mul,
    Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [history_half_split_positive_trace]
  rw [GibbsMultilevelReflection.joint, GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker]
  simp [Matrix.trace]

/-- Literal depth-zero inserted labels recover the accepted actual two-event kernel. -/
theorem history_inserted_two_kernel (p : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (i j : Fin 6) :
    historyInsertedKernel p [] γ η t hγ hη ht (i,()) (j,()) =
      insertedTwoKernel p.value γ η t p.nonnegative p.bounded hγ hη ht i j := by
  rw [history_inserted_depth_zero, insertedTwoKernel_trace]

/-- The explicit bijection removes only the terminal unit in a literal depth-two half. -/
def historyTripleLabelsEquiv (r s : Gap) : Triple ≃ Labels [r,s] where
  toFun u := (u.1,u.2.1,u.2.2,())
  invFun u := (u.1,u.2.1,u.2.2.1)
  left_inv _ := rfl
  right_inv u := by rcases u with ⟨i,j,k,⟨⟩⟩; rfl

theorem history_depth_two_effect (r s : Gap) (u : Triple) :
    historyEffect [r,s] (historyTripleLabelsEquiv r s u)=tripleEffect r.value s.value u := rfl

theorem history_depth_two_midpoint (p r s : Gap) (u : Triple) :
    historyMidpoint p [r,s] (historyTripleLabelsEquiv r s u)=tripleMidpoint p.value r.value s.value u := rfl

/-- Two-gap recovery is an equality of actual full complex chronological traces. -/
theorem history_inserted_depth_two (p r s : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Triple) :
    historyInsertedKernel p [r,s] γ η t hγ hη ht
      (historyTripleLabelsEquiv r s u) (historyTripleLabelsEquiv r s v) =
    sixKernel p.value r.value s.value γ η t p.nonnegative p.bounded
      r.nonnegative r.bounded s.nonnegative s.bounded hγ hη ht u v := by
  rw [history_inserted_kernel_trace, six_kernel_trace]
  rfl

/-- Literal coefficient transport binds every original three-label consumer to the recursive quotient. -/
def historyTriplePull (r s : Gap) (F : Triple → ℂ) : Labels [r,s] → ℂ :=
  fun u => F ((historyTripleLabelsEquiv r s).symm u)

theorem history_depth_two_synthesis (p r s : Gap) (F : Triple → ℂ) :
    historySynthesis p [r,s] (historyTriplePull r s F)=tripleSynthesis p.value r.value s.value F := by
  have h := (historyTripleLabelsEquiv r s).sum_comp (fun u =>
    F ((historyTripleLabelsEquiv r s).symm u) • historyMidpoint p [r,s] u)
  simp only [Equiv.symm_apply_apply, history_depth_two_midpoint] at h
  exact h.symm

/-- The independently defined actual observable descent agrees with the genuine projection transfer. -/
theorem historyTransfer_eq_observable (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (historyTransfer p rs γ η t).toLinearMap=historyObservable p rs γ η t hγ hη ht := by
  ext z
  apply historyCoordinates_injective p rs
  change historyCoordinates p rs (historyTransfer p rs γ η t z)=
    historyCoordinates p rs (historyObservable p rs γ η t hγ hη ht z)
  rw [historyTransfer_coordinates p rs γ η t hγ hη ht,
    historyObservable_coordinates p rs γ η t hγ hη ht]

/-- The actual inserted norm equals the half-time transfer norm, retaining its own metric. -/
theorem history_inserted_norm_half_transfer (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (z : HistorySpace p rs) :
    ‖historyToInserted p rs γ η t hγ hη ht z‖=‖historyTransfer p rs γ η (t/2) z‖ := by
  have he : historyTransfer p rs γ η (t/2) z=historyObservable p rs γ η (t/2) hγ hη (by positivity) z :=
    congrArg (fun M : HistorySpace p rs →ₗ[ℂ] HistorySpace p rs => M z)
      (historyTransfer_eq_observable p rs γ η (t/2) hγ hη (by positivity))
  rw [he]
  exact history_inserted_norm_half_observable p rs γ η t hγ hη ht z

/-- The full complex original six-event pairing is recovered after the explicit label pullback. -/
theorem history_depth_two_pairing (p r s : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (F G : Triple → ℂ) :
    pairing (historyInsertedKernel p [r,s] γ η t hγ hη ht)
      (historyTriplePull r s F) (historyTriplePull r s G) =
    pairing (sixKernel p.value r.value s.value γ η t p.nonnegative p.bounded
      r.nonnegative r.bounded s.nonnegative s.bounded hγ hη ht) F G := by
  rw [history_inserted_pairing, history_depth_two_synthesis, history_depth_two_synthesis,
    six_pairing_form]

/-- The actual genuinely three-label XYY class in the recursive quotient. -/
def historyXYYVector (p r s : Gap) : HistorySpace p [r,s] :=
  mk _ (history_posSemidef p [r,s]) (historyTriplePull r s XYY)

theorem historyXYYVector_coordinates (p r s : Gap) :
    historyCoordinates p [r,s] (historyXYYVector p r s) =
      ((24/25 : ℂ)*(p.value : ℂ)*(s.value : ℂ)) • pauliX := by
  rw [historyXYYVector, historyCoordinates_mk, history_depth_two_synthesis, XYY_synthesis]

theorem historyXYYVector_norm_sq (p r s : Gap) :
    ‖historyXYYVector p r s‖^2=(24/25 : ℝ)^3*p.value^2*s.value^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (⟪historyXYYVector p r s,historyXYYVector p r s⟫_ℂ).re=_
  rw [history_coordinates_inner, historyXYYVector, historyCoordinates_mk,
    history_depth_two_synthesis, XYY_form]
  rw [show (24/25 : ℂ)=((24/25 : ℝ) : ℂ) by norm_num]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The inserted pairing has one transverse factor, while the transfer norm has its square. -/
theorem historyXYY_inserted_pairing (p r s : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    pairing (historyInsertedKernel p [r,s] γ η t hγ hη ht)
      (historyTriplePull r s XYY) (historyTriplePull r s XYY) =
      (24/25 : ℂ)^3*(p.value : ℂ)^2*(s.value : ℂ)^2*
        (Real.exp (-(γ+η)*t) : ℂ) := by
  rw [history_depth_two_pairing]
  exact XYY_inserted_pairing p.value r.value s.value γ η t p.nonnegative p.bounded
    r.nonnegative r.bounded s.nonnegative s.bounded hγ hη ht

theorem historyXYY_transferred_norm_sq (p r s : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ‖historyTransfer p [r,s] γ η t (historyXYYVector p r s)‖^2=
      (24/25 : ℝ)^3*p.value^2*s.value^2*Real.exp (-(γ+η)*t)^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (⟪historyTransfer p [r,s] γ η t (historyXYYVector p r s),
    historyTransfer p [r,s] γ η t (historyXYYVector p r s)⟫_ℂ).re=_
  rw [history_coordinates_inner, historyTransfer_coordinates p [r,s] γ η t hγ hη ht,
    historyXYYVector, historyCoordinates_mk, history_depth_two_synthesis,
    XYY_transferred_norm_sq p.value r.value s.value γ η t hγ hη ht]
  rw [show (24/25 : ℂ)=((24/25 : ℝ) : ℂ) by norm_num]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The original ±27 witnesses remain literal coefficients at depth two. -/
theorem historyXYY_three_label_values (r s : Gap) :
    historyTriplePull r s XYY (0,2,2,())=27 ∧
    historyTriplePull r s XYY (1,2,2,())= -27 ∧
    historyTriplePull r s XYY (0,3,2,())= -27 ∧
    historyTriplePull r s XYY (0,2,3,())= -27 := XYY_values

/-- Zero inner side retention does not kill the genuine three-label class. -/
theorem historyXYY_positive (p r s : Gap) (hp : 0 < p.value) (hs : 0 < s.value) :
    0 < ‖historyXYYVector p r s‖^2 := by
  rw [historyXYYVector_norm_sq]
  positivity

theorem historyXYY_zero_outer (p r s : Gap) (hs : s.value=0) : historyXYYVector p r s=0 := by
  apply historyCoordinates_injective p [r,s]
  rw [historyXYYVector_coordinates, map_zero, hs]
  simp

theorem historyXYY_zero_central (p r s : Gap) (hp : p.value=0) : historyXYYVector p r s=0 := by
  apply historyCoordinates_injective p [r,s]
  rw [historyXYYVector_coordinates, map_zero, hp]
  simp

/-- Paired labels retain the terminal unit and the literal two-time coefficients. -/
def historyPairPull (r : Gap) (F : HalfHistory → ℂ) : Labels [r] → ℂ :=
  fun u => F (u.1,u.2.1)

theorem history_depth_one_synthesis (p r : Gap) (F : HalfHistory → ℂ) :
    historySynthesis p [r] (historyPairPull r F)=synthesis p.value r.value F := by
  let e : HalfHistory ≃ Labels [r] :=
    { toFun := fun u => (u.1,u.2,())
      invFun := fun u => (u.1,u.2.1)
      left_inv := fun _ => rfl
      right_inv := by intro u; rcases u with ⟨i,j,⟨⟩⟩; rfl }
  have h := e.sum_comp (fun u => historyPairPull r F u • historyMidpoint p [r] u)
  change synthesis p.value r.value F=historySynthesis p [r] (historyPairPull r F) at h
  exact h.symm

/-- A nonzero centered XZ coefficient is null in the actual recursive history quotient. -/
theorem history_centeredXZ_guard (p r : Gap) :
    historyPairPull r centeredXZ (0,4,())=204/25 ∧
    mk _ (history_posSemidef p [r]) (historyPairPull r centeredXZ)=0 := by
  constructor
  · exact centeredXZ_nonzero_coefficient
  · rw [history_null_iff, history_depth_one_synthesis, centeredXZ_synthesis]

/-- The uncentered two-label XZ retains its nonzero synthesis for positive central retention. -/
theorem history_uncenteredXZ_guard (p r : Gap) (hp : 0 < p.value) :
    historySynthesis p [r] (historyPairPull r XZ)=(7*(p.value : ℂ)/25) • pauliX ∧
    mk _ (history_posSemidef p [r]) (historyPairPull r XZ)≠0 := by
  constructor
  · rw [history_depth_one_synthesis, XZ_synthesis]
  · intro hz
    have h := (history_null_iff p [r] (historyPairPull r XZ)).mp hz
    rw [history_depth_one_synthesis, XZ_synthesis] at h
    have he := congrArg (fun A : Mat2 => A 0 1) h
    norm_num [Matrix.smul_apply, pauliX] at he
    have hzero : p.value=0 := by linarith
    exact (ne_of_gt hp) hzero

/-- Summing both middle interventions gives the separate actual anisotropic four-event tree. -/
theorem history_middle_erased_marginal (p r s : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    ∑ m,∑ n, historyInsertedKernel p [r,s] γ η t hγ hη ht
      (historyTripleLabelsEquiv r s (u.1,m,u.2))
      (historyTripleLabelsEquiv r s (v.1,n,v.2)) =
    middleErasedKernel p.value r.value s.value γ η t p.nonnegative p.bounded
      r.nonnegative r.bounded s.nonnegative s.bounded hγ hη ht u v := by
  simp_rw [history_inserted_depth_two]
  exact six_middle_marginal p.value r.value s.value γ η t p.nonnegative p.bounded
    r.nonnegative r.bounded s.nonnegative s.bounded hγ hη ht u v

/-- The recursive erased effect retains different diagonal and transverse fractions. -/
theorem history_middle_effect_sectors (r s : Gap) :
    Psi r.value (M (Psi s.value Zc))=((r.value : ℂ)*(s.value : ℂ)/3) • Zc ∧
    Psi r.value (M (Psi s.value pauliX))=(8*(r.value : ℂ)*(s.value : ℂ)/25) • pauliX ∧
    (∀ q : ℝ, r.value*s.value≠0 →
      (fun A : Mat2 => Psi r.value (M (Psi s.value A)))≠Psi q) := by
  exact ⟨erased_centered_z r.value s.value, erased_x r.value s.value,
    fun q h => erased_not_scalar_reset r.value s.value h q⟩

/-- Both actual XX syntheses and their distinct weighted norms remain bound to recursive labels. -/
theorem history_XX_disturbance :
    historySynthesis PauliHistoryConsistency.identityGap [PauliHistoryConsistency.identityGap]
      (historyPairPull PauliHistoryConsistency.identityGap XX)=(24/25 : ℂ) • (1 : Mat2) ∧
    historySynthesis PauliHistoryConsistency.identityGap
      [PauliHistoryConsistency.identityGap,PauliHistoryConsistency.identityGap]
      (historyTriplePull PauliHistoryConsistency.identityGap PauliHistoryConsistency.identityGap ignoreMiddleXX)=
      (192/625 : ℂ) • (1 : Mat2) ∧
    ‖mk _ (history_posSemidef PauliHistoryConsistency.identityGap [PauliHistoryConsistency.identityGap])
      (historyPairPull PauliHistoryConsistency.identityGap XX)‖^2=576/625 ∧
    ‖mk _ (history_posSemidef PauliHistoryConsistency.identityGap
      [PauliHistoryConsistency.identityGap,PauliHistoryConsistency.identityGap])
      (historyTriplePull PauliHistoryConsistency.identityGap PauliHistoryConsistency.identityGap ignoreMiddleXX)‖^2=
      36864/390625 := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [history_depth_one_synthesis]; exact XX_synthesis
  · rw [history_depth_two_synthesis]; exact ignored_XX_synthesis
  · rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (⟪mk _ (history_posSemidef PauliHistoryConsistency.identityGap [PauliHistoryConsistency.identityGap]) (historyPairPull PauliHistoryConsistency.identityGap XX),
      mk _ (history_posSemidef PauliHistoryConsistency.identityGap [PauliHistoryConsistency.identityGap]) (historyPairPull PauliHistoryConsistency.identityGap XX)⟫_ℂ).re=_
    rw [history_coordinates_inner, historyCoordinates_mk, history_depth_one_synthesis]
    change (form (synthesis 1 1 XX) (synthesis 1 1 XX)).re=576/625
    rw [XX_form]
    norm_num
  · rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (⟪mk _ (history_posSemidef PauliHistoryConsistency.identityGap [PauliHistoryConsistency.identityGap,PauliHistoryConsistency.identityGap]) (historyTriplePull PauliHistoryConsistency.identityGap PauliHistoryConsistency.identityGap ignoreMiddleXX),
      mk _ (history_posSemidef PauliHistoryConsistency.identityGap [PauliHistoryConsistency.identityGap,PauliHistoryConsistency.identityGap]) (historyTriplePull PauliHistoryConsistency.identityGap PauliHistoryConsistency.identityGap ignoreMiddleXX)⟫_ℂ).re=_
    rw [history_coordinates_inner, historyCoordinates_mk, history_depth_two_synthesis]
    change (form (tripleSynthesis 1 1 1 ignoreMiddleXX)
      (tripleSynthesis 1 1 1 ignoreMiddleXX)).re=36864/390625
    rw [ignored_XX_form]
    norm_num

/-- At zero dephasing the actual quotient observable recovers the accepted reset action. -/
theorem historyTransfer_zero_dephasing_coordinates (p : Gap) (rs : List Gap) (γ t : ℝ)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t) (z : HistorySpace p rs) :
    historyCoordinates p rs (historyTransfer p rs γ 0 t z)=
      Psi (Real.exp (-γ*t)) (historyCoordinates p rs z) := by
  rw [historyTransfer_coordinates p rs γ 0 t hγ le_rfl ht]
  exact (zero_dephasing_actions γ t hγ ht (historyCoordinates p rs z)).2

/-- Numerical mode constants belong to the actual all-depth weighted quotient and its transfer. -/
theorem historyTransfer_numerical_mode_norms (p : Gap) (rs : List Gap) (γ η t : ℝ) :
    ‖historyCenteredVector p rs 0‖^2=24*p.value^2/25 ∧
    ‖historyCenteredVector p rs 1‖^2=24*p.value^2/25 ∧
    ‖historyCenteredVector p rs 2‖^2=576*p.value^2/625 ∧
    ‖historyConstantVector p rs‖^2=1 ∧
    ‖historyComplexVector p rs‖^2=48*p.value^2/25 ∧
    ‖historyTransfer p rs γ η t (historyCenteredVector p rs 0)‖^2=
      (24*p.value^2/25)*Real.exp (-(γ+η)*t)^2 ∧
    ‖historyTransfer p rs γ η t (historyCenteredVector p rs 1)‖^2=
      (24*p.value^2/25)*Real.exp (-(γ+η)*t)^2 ∧
    ‖historyTransfer p rs γ η t (historyCenteredVector p rs 2)‖^2=
      (576*p.value^2/625)*Real.exp (-γ*t)^2 ∧
    ‖historyTransfer p rs γ η t (historyComplexVector p rs)‖^2=
      (48*p.value^2/25)*Real.exp (-(γ+η)*t)^2 := by
  rcases historyProjection_mode_norms p rs with ⟨hI,hX,hY,hZ,hC⟩
  refine ⟨hX,hY,hZ,hI,hC,?_,?_,?_,historyTransfer_complex_norm_sq p rs γ η t⟩
  · have h := historyTransfer_centered_norm_sq p rs γ η t 0
    change ‖historyTransfer p rs γ η t (historyCenteredVector p rs 0)‖^2=
      (24/25 : ℝ)*p.value^2*Real.exp (-(γ+η)*t)^2 at h
    rw [h]; ring
  · have h := historyTransfer_centered_norm_sq p rs γ η t 1
    change ‖historyTransfer p rs γ η t (historyCenteredVector p rs 1)‖^2=
      (24/25 : ℝ)*p.value^2*Real.exp (-(γ+η)*t)^2 at h
    rw [h]; ring
  · have h := historyTransfer_centered_norm_sq p rs γ η t 2
    change ‖historyTransfer p rs γ η t (historyCenteredVector p rs 2)‖^2=
      (576/625 : ℝ)*p.value^2*Real.exp (-γ*t)^2 at h
    rw [h]; ring

/-- The actual state evolution cannot replace quotient observable coordinates at positive reset rate. -/
theorem historyTransfer_state_observable_guard (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 < γ) (hη : 0 ≤ η) (ht : 0 < t) :
    state γ η t (historyCoordinates p rs (historyConstantVector p rs)) ≠
      historyCoordinates p rs (historyTransfer p rs γ η t (historyConstantVector p rs)) := by
  rw [historyTransfer_constant, historyConstantVector_coordinates]
  simpa only [observable_unital γ η t hγ.le hη ht.le] using
    state_observable_difference γ η t hγ hη ht

/-- The state and observable reset maps remain different on the actual constant coordinate. -/
theorem history_reset_action_guard (p : Gap) (rs : List Gap) :
    Phi 0 (historyCoordinates p rs (historyConstantVector p rs)) ≠
      Psi 0 (historyCoordinates p rs (historyConstantVector p rs)) := by
  rw [historyConstantVector_coordinates]
  exact reset_actions_distinct

/-- The chronological X metric is strictly smaller than the rejected one-sided state metric. -/
theorem history_metric_mismatch_guard (p : Gap) (hp : p.value=1) (rs : List Gap) :
    ‖historyCenteredVector p rs 0‖^2<(pauliX*rhoN*pauliXᴴ).trace.re := by
  rw [historyCenteredVector_norm_sq, old_metric_x, hp]
  norm_num [modeNorm, Fin.ext_iff]

/-- The accepted positive side-reset witness has the same finite-time decay at recursive depth one. -/
theorem history_side_reset_decay (p : Gap) (hp : p.value=1/2) :
    ‖historyTransfer p [⟨0,le_rfl,zero_le_one⟩] 1 1 1
      (historyCenteredVector p [⟨0,le_rfl,zero_le_one⟩] 0)‖^2=
      (6/25 : ℝ)*Real.exp (-4) := by
  rw [historyTransfer_centered_norm_sq, hp]
  have he : Real.exp (-2)^2=Real.exp (-4) := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  norm_num [modeNorm, Fin.ext_iff, he]

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
