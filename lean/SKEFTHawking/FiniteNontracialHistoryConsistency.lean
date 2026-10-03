import SKEFTHawking.FiniteNontracialReflectionDynamics
import SKEFTHawking.FinitePauliHistoryConsistency

/-! Six-event chronology for the fixed faithful nontracial replacement instrument.
The operational kernel is the real weight of an actual normalized process, cast into Complex.
Negative state recursion and positive observable recursion are separate. Their trace identity
derives the complex weighted Gram identity and the literal six-to-four outer marginal.
This initial pilot does not establish the arbitrary-depth family or its quotient dynamics. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection
open FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

abbrev Triple := PauliHistoryConsistency.Triple

/-- Each half is indexed from its inner intervention toward its outer intervention. -/
def sixHistory (u v : Triple) : History 6 6 :=
  (u.2.2,u.2.1,u.1,v.1,v.2.1,v.2.2,())

/-- Negative chronology is outer, middle, inner. -/
def negativeThree (r s : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : Tree (Fin 2) Unit 6 3 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step s hs hs1) (fun _ =>
      .node (step r hr hr1) (fun _ => .done)))

/-- Positive chronology is inner, middle, outer; q is the initial reset gap. -/
def positiveThree (q r s : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Tree (Fin 2) Unit 6 3 :=
  .node (step q hq hq1) (fun _ =>
    .node (step r hr hr1) (fun _ =>
      .node (step s hs hs1) (fun _ => .done)))

/-- The accepted actual central Kraus step follows reset at p squared. -/
def sixTree (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Tree (Fin 2) Unit 6 6 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step s hs hs1) (fun _ =>
      .node (step r hr hr1) (fun _ =>
        .node (NontracialReflectionDynamics.centralStep p γ η t hp hp1 hγ hη ht) (fun _ =>
          .node (step r hr hr1) (fun _ =>
            .node (step s hs hs1) (fun _ => .done))))))

/-- Defined from actual chronological weights before any Gram factorization. -/
def sixKernel (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Triple) : ℂ :=
  (weight (Fin 2) Unit 6 (sixTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
    (sixHistory u v) (GibbsMultilevelReflection.joint rhoN) : ℂ)

/-- Backward effect recursion uses the observable dual J, not the state branch. -/
def tripleEffect (r s : ℝ) (u : Triple) : Mat2 :=
  J u.1 (Psi r (J u.2.1 (Psi s (PauliInstrumentReconstruction.effect u.2.2))))

def tripleMidpoint (p r s : ℝ) (u : Triple) : Mat2 := Psi p (tripleEffect r s u)

theorem tripleEffect_adjoint (r s : ℝ) (u : Triple) :
    (tripleEffect r s u)ᴴ = tripleEffect r s u := by
  simp only [tripleEffect, J_adjoint, Psi_adjoint, effect_adjoint]

theorem tripleMidpoint_adjoint (p r s : ℝ) (u : Triple) :
    (tripleMidpoint p r s u)ᴴ = tripleMidpoint p r s u := by
  rw [tripleMidpoint, Psi_adjoint, tripleEffect_adjoint]

/-- The negative half has a Gamma-sandwiched state, including zero side gaps. -/
theorem negative_three_run (r s : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (u : Triple) :
    run (Fin 2) Unit 6 (negativeThree r s hr hr1 hs hs1) (u.2.2,u.2.1,u.1,())
      (GibbsMultilevelReflection.joint rhoN) =
      GibbsMultilevelReflection.joint (Gamma (tripleEffect r s u)) := by
  simp only [negativeThree, run, step_branch, Phi_one, branch_rhoN,
    Phi_Gamma, branch_Gamma, tripleEffect]

/-- Positive trace recursion holds for every complex input matrix. -/
theorem positive_three_trace (q r s : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (v : Triple) (X : Mat2) :
    (run (Fin 2) Unit 6 (positiveThree q r s hq hq1 hr hr1 hs hs1)
      (v.1,v.2.1,v.2.2,()) (GibbsMultilevelReflection.joint X)).trace =
      (Psi q (tripleEffect r s v) * X).trace := by
  simp only [positiveThree, run, step_branch, GibbsMultilevelReflection.joint_trace]
  rw [branch_trace, Phi_Psi_duality, trace_duality, Phi_Psi_duality,
    trace_duality, Phi_Psi_duality]
  rfl

theorem six_actual_run (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Triple) :
    run (Fin 2) Unit 6 (sixTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      (sixHistory u v) (GibbsMultilevelReflection.joint rhoN) =
      GibbsMultilevelReflection.joint (instrument.branch v.2.2
        (Phi s (instrument.branch v.2.1 (Phi r (instrument.branch v.1
          (NontracialReflectionDynamics.state γ η t (Phi (p*p) (Gamma (tripleEffect r s u))))))))) := by
  change (step s hs hs1).branch (Fin 2) Unit 6 v.2.2
    ((step r hr hr1).branch (Fin 2) Unit 6 v.2.1
      ((NontracialReflectionDynamics.centralStep p γ η t hp hp1 hγ hη ht).branch
        (Fin 2) Unit 6 v.1 (run (Fin 2) Unit 6 (negativeThree r s hr hr1 hs hs1)
          (u.2.2,u.2.1,u.1,()) (GibbsMultilevelReflection.joint rhoN)))) = _
  rw [negative_three_run, NontracialReflectionDynamics.centralStep_branch,
    step_branch, step_branch]

theorem six_actual_trace (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Triple) :
    (run (Fin 2) Unit 6 (sixTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      (sixHistory u v) (GibbsMultilevelReflection.joint rhoN)).trace =
      (tripleEffect r s v * NontracialReflectionDynamics.state γ η t
        (Phi (p*p) (Gamma (tripleEffect r s u)))).trace := by
  rw [six_actual_run, GibbsMultilevelReflection.joint_trace, branch_trace,
    Phi_Psi_duality, trace_duality, Phi_Psi_duality, trace_duality]
  rfl

/-- The real probability is the full complex trace, with no restriction on Y labels. -/
theorem six_kernel_trace (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Triple) :
    sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v =
      (tripleEffect r s v * NontracialReflectionDynamics.state γ η t
        (Phi (p*p) (Gamma (tripleEffect r s u)))).trace := by
  unfold sixKernel weight
  rw [six_actual_trace]
  apply hermitian_product_real _ _ (tripleEffect_adjoint r s v)
  rw [Phi_Gamma, NontracialReflectionDynamics.intertwining γ η t hγ hη ht,
    Gamma_adjoint, NontracialReflectionDynamics.observable_adjoint,
    Psi_adjoint, tripleEffect_adjoint]

theorem six_actual_probabilities (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∀ h, 0 ≤ weight (Fin 2) Unit 6
      (sixTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h, weight (Fin 2) Unit 6 (sixTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      h (GibbsMultilevelReflection.joint rhoN)) = 1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

/-- Every chronological history corresponds to exactly one pair of half histories. -/
def sixHistoryEquiv : (Triple × Triple) ≃ History 6 6 where
  toFun uv := sixHistory uv.1 uv.2
  invFun h := ((h.2.2.1,h.2.1,h.1),
    (h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1))
  left_inv uv := by rcases uv with ⟨⟨i,m,o⟩,⟨j,n,q⟩⟩; rfl
  right_inv h := by rcases h with ⟨o,m,i,j,n,q,⟨⟩⟩; rfl

/-- Normalization is transported through the actual history bijection. -/
theorem six_kernel_normalized (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∑ u, ∑ v, (sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v).re) = 1 := by
  have h := sixHistoryEquiv.sum_comp (fun h => weight (Fin 2) Unit 6
    (sixTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) h
    (GibbsMultilevelReflection.joint rhoN))
  rw [Fintype.sum_prod_type] at h
  change (∑ u, ∑ v, (sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v).re) =
    ∑ h, weight (Fin 2) Unit 6 (sixTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN) at h
  exact h.trans (six_actual_probabilities p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht).2

/-- The actual weight kernel has the conjugate-first weighted form. -/
theorem six_kernel_form (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Triple) :
    sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v =
      form (tripleMidpoint p r s u)
        (NontracialReflectionDynamics.observable γ η t (tripleMidpoint p r s v)) := by
  rw [six_kernel_trace, NontracialReflectionDynamics.trace_dual, central_split,
    ← NontracialReflectionDynamics.observable_Psi p γ η t hγ hη ht]
  rw [form, tripleMidpoint_adjoint]
  simp only [tripleMidpoint, Gamma, Matrix.mul_assoc]

/-- At zero inserted time the actual chronological kernel gives the uninserted form. -/
theorem six_zero_form (p r s γ η : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (u v : Triple) :
    sixKernel p r s γ η 0 hp hp1 hr hr1 hs hs1 hγ hη (by norm_num) u v =
      form (tripleMidpoint p r s u) (tripleMidpoint p r s v) := by
  have hzero (A : Mat2) : NontracialReflectionDynamics.observable γ η 0 A = A := by
    rw [NontracialReflectionDynamics.observable_formula γ η 0 hγ hη (by norm_num)]
    simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_smul]
    module
  rw [six_kernel_form, hzero]

/-- Transport the accepted half-time identity to all matrices via its full coordinate range.
The fixed reference space uses central retention one; this puts no positivity condition on
the actual six-event central retention or either actual side gap. -/
theorem form_half_time (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (A B : Mat2) :
    form A (NontracialReflectionDynamics.observable γ η t B) =
      form (NontracialReflectionDynamics.observable γ η (t/2) A)
        (NontracialReflectionDynamics.observable γ η (t/2) B) := by
  obtain ⟨z,hz⟩ := coordinates_surjective 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) A
  obtain ⟨w,hw⟩ := coordinates_surjective 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) B
  have h := NontracialReflectionDynamics.transfer_half_inner 1 0 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) γ η t hγ hη ht z w
  simp only [NontracialReflectionDynamics.coordinates_inner,
    NontracialReflectionDynamics.transfer_coordinates 1 0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) γ η t hγ hη ht,
    NontracialReflectionDynamics.transfer_coordinates 1 0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) γ η (t/2) hγ hη (by positivity), hz, hw] at h
  exact h

/-- Half-time Gram follows from chronology and the accepted weighted semigroup. -/
theorem six_kernel_half_gram (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Triple) :
    sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v =
      (NontracialPauliReflection.feature (NontracialReflectionDynamics.observable γ η (t/2) (tripleMidpoint p r s v)) *
        (NontracialPauliReflection.feature (NontracialReflectionDynamics.observable γ η (t/2)
          (tripleMidpoint p r s u)))ᴴ).trace := by
  rw [six_kernel_form, form_half_time γ η t hγ hη ht, feature_gram]

def tripleSynthesis (p r s : ℝ) (F : Triple → ℂ) : Mat2 :=
  ∑ u, F u • tripleMidpoint p r s u

/-- All complex coefficients, with conjugation on the first coefficient function. -/
theorem six_pairing_form (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (F G : Triple → ℂ) :
    pairing (sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) F G =
      form (tripleSynthesis p r s F)
        (NontracialReflectionDynamics.observable γ η t (tripleSynthesis p r s G)) := by
  change _ = form (tripleSynthesis p r s F)
    (NontracialReflectionDynamics.observableLinear γ η t (tripleSynthesis p r s G))
  simp only [tripleSynthesis, map_sum, map_smul,
    NontracialReflectionDynamics.form_sum_left, NontracialReflectionDynamics.form_sum_right,
    form_smul]
  simp only [pairing, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    six_kernel_form p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change star (F v) * (form _ (NontracialReflectionDynamics.observable γ η t _) * G u) =
    star (F v) * G u * form _ (NontracialReflectionDynamics.observable γ η t _)
  ring

theorem six_posSemidef (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    Matrix.PosSemidef (sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup (1 : Mat2) Matrix.PosSemidef.one
  letI := Matrix.toMatrixInnerProductSpace (1 : Mat2) Matrix.PosSemidef.one
  have hk : sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht =
      Matrix.gram ℂ (fun u => NontracialPauliReflection.feature
        (NontracialReflectionDynamics.observable γ η (t/2) (tripleMidpoint p r s u))) := by
    ext u v
    rw [six_kernel_half_gram]
    change (NontracialPauliReflection.feature
      (NontracialReflectionDynamics.observable γ η (t/2) (tripleMidpoint p r s v)) *
      (NontracialPauliReflection.feature
        (NontracialReflectionDynamics.observable γ η (t/2) (tripleMidpoint p r s u)))ᴴ).trace =
      (NontracialPauliReflection.feature
        (NontracialReflectionDynamics.observable γ η (t/2) (tripleMidpoint p r s v)) * 1 *
        (NontracialPauliReflection.feature
          (NontracialReflectionDynamics.observable γ η (t/2) (tripleMidpoint p r s u)))ᴴ).trace
    simp
  rw [hk]
  exact Matrix.posSemidef_gram ℂ _

theorem tripleEffect_outer (r s : ℝ) (i m : Fin 6) :
    ∑ o, tripleEffect r s (i,m,o) = halfEffect r (i,m) := by
  change (∑ o, JLinear i (PsiLinear r (halfEffect s (m,o)))) = _
  rw [← map_sum, ← map_sum, halfEffect_outer]
  rfl

/-- Literal new outer labels are summed in the actual weight kernel. -/
theorem six_outer_marginal (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    ∑ o, ∑ q, sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht
      (u.1,u.2,o) (v.1,v.2,q) =
      NontracialReflectionDynamics.kernel p r γ η t hp hp1 hr hr1 hγ hη ht u v := by
  simp_rw [six_kernel_trace]
  simp only [← Finset.mul_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, tripleEffect_outer,
    ← NontracialReflectionDynamics.state_sum, ← Phi_sum, ← Gamma_sum]
  rw [NontracialReflectionDynamics.kernel_trace]

/-- A Y-containing actual outer marginal survives complete side reset. -/
theorem six_y_outer_weight (p s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ∑ o, ∑ q, sixKernel p 0 s γ η t hp hp1 (by norm_num) (by norm_num)
      hs hs1 hγ hη ht (2,0,o) (2,0,q) =
      1/1296 + (p:ℂ)^2 * (Real.exp (-(γ+η)*t) : ℂ)/1350 := by
  rw [six_outer_marginal p 0 s γ η t hp hp1 (by norm_num) (by norm_num)
    hs hs1 hγ hη ht (2,0) (2,0), NontracialReflectionDynamics.actual_y_weight]

/-- At complete central reset the same Y marginal is nonzero, also at zero side gap. -/
theorem six_reset_y_outer_weight (s γ η t : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    ∑ o, ∑ q, sixKernel 0 0 s γ η t (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hs hs1 hγ hη ht (2,0,o) (2,0,q) = 1/1296 := by
  rw [six_y_outer_weight]
  norm_num

theorem tripleEffect_reset_y :
    tripleEffect 0 0 (2,0,0) = (1/6 : ℂ) • halfEffect 0 (2,0) := by
  have hm : (rhoN * PauliInstrumentReconstruction.effect 0).trace = (1/6 : ℂ) := by
    norm_num [rhoN, PauliInstrumentReconstruction.effect,
      PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign,
      PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
      PauliInstrumentReconstruction.sigma, pauliX, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]
  have hreset : Psi 0 (PauliInstrumentReconstruction.effect 0) = (1/6 : ℂ) • 1 := by
    rw [Psi_zero, hm]
  have hj : J 0 ((1/6 : ℂ) • 1) = (1/6 : ℂ) • PauliInstrumentReconstruction.effect 0 := by
    change JLinear 0 ((1/6 : ℂ) • 1) = _
    rw [map_smul]
    change (1/6 : ℂ) • J 0 1 = _
    rw [J_one]
  rw [tripleEffect, hreset, hj, Psi_smul]
  change JLinear 2 ((1/6 : ℂ) • Psi 0 (PauliInstrumentReconstruction.effect 0)) = _
  rw [map_smul]
  rfl

/-- A fixed six-event Y history has a positive probability floor at p=0 and r=s=0. -/
theorem six_actual_y_weight (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    sixKernel p 0 0 γ η t hp hp1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hγ hη ht (2,0,0) (2,0,0) =
      1/46656 + (p:ℂ)^2 * (Real.exp (-(γ+η)*t) : ℂ)/48600 := by
  rw [six_kernel_form]
  simp only [tripleMidpoint, tripleEffect_reset_y, Psi_smul]
  change form ((1/6 : ℂ) • midpoint p 0 (2,0))
    (NontracialReflectionDynamics.observableLinear γ η t
      ((1/6 : ℂ) • midpoint p 0 (2,0))) = _
  rw [map_smul, form_smul]
  change star (1/6 : ℂ) * (1/6 : ℂ) * form (midpoint p 0 (2,0))
    (NontracialReflectionDynamics.observable γ η t (midpoint p 0 (2,0))) = _
  rw [← NontracialReflectionDynamics.actual_kernel_form p 0 γ η t hp hp1
      (by norm_num) (by norm_num) hγ hη ht (2,0) (2,0),
    NontracialReflectionDynamics.actual_y_weight]
  norm_num
  ring

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency

noncomputable section
namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

/-- Weighted actual observable branches of the replacement instrument. -/
def W (a : Fin 3) (A : Mat2) : Mat2 :=
  ∑ i, PauliInstrumentReconstruction.axisMode a i • J i A

/-- Erasing an outcome retains the actual six-Kraus measurement channel. -/
def M (A : Mat2) : Mat2 := ∑ i, J i A

def stateM (X : Mat2) : Mat2 := krausMap L X

theorem J_projector (i : Fin 6) (A : Mat2) :
    J i A = (3 * (d i : ℂ))⁻¹ •
      (PauliInstrumentReconstruction.projector i * R * A * R *
        PauliInstrumentReconstruction.projector i) := by
  have hd : (d i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (d_pos i)
  have hc : c i * c i = (3 * (d i : ℂ))⁻¹ := by
    have h := c_square_d i
    field_simp at ⊢
    linear_combination 3 * h
  simp only [NontracialPauliReflection.J, L, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    PauliInstrumentReconstruction.projector_adjoint, R_adjoint, c_real, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hc]
  congr 1
  noncomm_ring

theorem W_x_formula (A : Mat2) :
    W 0 A = (rhoN * A).trace • pauliX +
      ((12/25 : ℂ) * (A 0 1 + A 1 0)) • (1 : Mat2) := by
  simp only [W, J_projector, d_values]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, PauliInstrumentReconstruction.axisMode,
      PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign,
      PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma,
      rhoN, R, pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace,
      Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem W_y_formula (A : Mat2) :
    W 1 A = (rhoN * A).trace • pauliY +
      ((12/25 : ℂ) * Complex.I * (A 0 1 - A 1 0)) • (1 : Mat2) := by
  simp only [W, J_projector, d_values]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, PauliInstrumentReconstruction.axisMode,
      PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign,
      PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma,
      rhoN, R, pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace,
      Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem M_formula (A : Mat2) :
    M A = (rhoN * A).trace • (1 : Mat2) +
      (1/3 : ℂ) • (NontracialReflectionDynamics.diagonalPart A -
        (rhoN * A).trace • (1 : Mat2)) +
      (8/25 : ℂ) • (A - NontracialReflectionDynamics.diagonalPart A) := by
  simp only [M, J_projector, d_values]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, PauliInstrumentReconstruction.projector,
      PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
      finProdFinEquiv, Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma,
      rhoN, R, pauliX, pauliY, pauliZ, NontracialReflectionDynamics.diagonalPart,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem W_smul (a : Fin 3) (z : ℂ) (A : Mat2) : W a (z • A) = z • W a A := by
  unfold W
  change (∑ i, PauliInstrumentReconstruction.axisMode a i • JLinear i (z • A)) = _
  simp only [map_smul, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]
  rfl

theorem W_x_one : W 0 1 = pauliX := by
  rw [W_x_formula]
  norm_num [rhoN_trace]

theorem W_x_x : W 0 pauliX = (24/25 : ℂ) • (1 : Mat2) := by
  rw [W_x_formula]
  norm_num [rhoN, pauliX, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]

theorem W_y_y : W 1 pauliY = (24/25 : ℂ) • (1 : Mat2) := by
  rw [W_y_formula]
  norm_num [rhoN, pauliY, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]
  ring_nf
  norm_num [Complex.I_sq]

theorem W_x_z : W 0 pauliZ = (7/25 : ℂ) • pauliX := by
  rw [W_x_formula]
  norm_num [rhoN, pauliZ, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]

def Zc : Mat2 := pauliZ - (7/25 : ℂ) • (1 : Mat2)

theorem W_x_centered_z : W 0 Zc = 0 := by
  rw [W_x_formula]
  norm_num [Zc, rhoN, pauliZ, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two, Matrix.one_apply]

theorem M_one : M 1 = 1 := by
  rw [M_formula]
  norm_num [NontracialReflectionDynamics.diagonalPart, rhoN_trace]

theorem M_x : M pauliX = (8/25 : ℂ) • pauliX := by
  rw [M_formula]
  norm_num [NontracialReflectionDynamics.diagonalPart, rhoN, pauliX,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply, Matrix.one_apply]

theorem M_y : M pauliY = (8/25 : ℂ) • pauliY := by
  rw [M_formula]
  norm_num [NontracialReflectionDynamics.diagonalPart, rhoN, pauliY,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply, Matrix.one_apply]

theorem M_centered_z : M Zc = (1/3 : ℂ) • Zc := by
  rw [M_formula]
  norm_num [NontracialReflectionDynamics.diagonalPart, Zc, rhoN, pauliZ,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply, Matrix.one_apply]

theorem measurement_normalized : IsKrausChannel L := by
  change (∑ i, (L i)ᴴ * L i) = 1
  have h := instrument.normalized
  change (∑ i, ∑ _k : Fin 1, (L i)ᴴ * L i) = 1 at h
  simpa only [Fin.sum_univ_one] using h

theorem stateM_sum (X : Mat2) : stateM X = ∑ i, instrument.branch i X := by
  simp only [stateM, krausMap, instrument_branch]

theorem stateM_Gamma (A : Mat2) : stateM (Gamma A) = Gamma (M A) := by
  rw [stateM_sum]
  simp only [branch_Gamma, M, Gamma_sum]

theorem M_adjoint (A : Mat2) : (M A)ᴴ = M Aᴴ := by
  simp only [M, Matrix.conjTranspose_sum, J_adjoint]

theorem stateM_duality (A X : Mat2) :
    (A * stateM X).trace = (M A * X).trace := by
  simp only [stateM_sum, M, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    trace_duality]

/-- Full-complex sector formula, without side-retention inverses. -/
theorem erased_observable_formula (r s : ℝ) (A : Mat2) :
    Psi r (M (Psi s A)) = (rhoN*A).trace • (1 : Mat2) +
      ((r:ℂ)*(s:ℂ)/3) • (NontracialReflectionDynamics.diagonalPart A -
        (rhoN*A).trace • (1 : Mat2)) +
      (8*(r:ℂ)*(s:ℂ)/25) • (A - NontracialReflectionDynamics.diagonalPart A) := by
  rw [M_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Psi, NontracialReflectionDynamics.diagonalPart, rhoN,
      Matrix.trace, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem erased_observable_commute (r s : ℝ) (A : Mat2) :
    Psi r (M (Psi s A)) = Psi s (M (Psi r A)) := by
  rw [erased_observable_formula, erased_observable_formula]
  have h1 : (r:ℂ)*(s:ℂ)/3 = (s:ℂ)*(r:ℂ)/3 := by ring
  have h2 : 8*(r:ℂ)*(s:ℂ)/25 = 8*(s:ℂ)*(r:ℂ)/25 := by ring
  rw [h1,h2]

theorem J_sumB {α : Type*} [Fintype α] (i : Fin 6) (A : α → Mat2) :
    J i (∑ a, A a) = ∑ a, J i (A a) := map_sum (JLinear i) _ _

theorem J_smulB (i : Fin 6) (z : ℂ) (A : Mat2) :
    J i (z • A) = z • J i A := (JLinear i).map_smul _ _

theorem triple_product_synthesis (p r s : ℝ) (f g h : Fin 6 → ℂ) :
    tripleSynthesis p r s (fun u => f u.1 * g u.2.1 * h u.2.2) =
      Psi p (∑ i, f i • J i (Psi r (∑ m, g m • J m
        (Psi s (PauliInstrumentReconstruction.synthesis h))))) := by
  simp only [tripleSynthesis, tripleMidpoint, tripleEffect, Fintype.sum_prod_type,
    PauliInstrumentReconstruction.synthesis, Psi_sum, Psi_smul, J_sumB, J_smulB,
    Finset.smul_sum, smul_smul, mul_assoc]

def XYY (u : Triple) : ℂ :=
  PauliInstrumentReconstruction.axisMode 0 u.1 *
    PauliInstrumentReconstruction.axisMode 1 u.2.1 *
    PauliInstrumentReconstruction.axisMode 1 u.2.2

theorem Psi_x (p : ℝ) : Psi p pauliX = (p:ℂ) • pauliX := by
  norm_num [Psi, rhoN, pauliX, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]

theorem Psi_y (p : ℝ) : Psi p pauliY = (p:ℂ) • pauliY := by
  norm_num [Psi, rhoN, pauliY, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_two]

theorem XYY_synthesis (p r s : ℝ) :
    tripleSynthesis p r s XYY = ((24/25 : ℂ)*(p:ℂ)*(s:ℂ)) • pauliX := by
  change tripleSynthesis p r s (fun u => PauliInstrumentReconstruction.axisMode 0 u.1 *
    PauliInstrumentReconstruction.axisMode 1 u.2.1 * PauliInstrumentReconstruction.axisMode 1 u.2.2) = _
  rw [triple_product_synthesis, PauliInstrumentReconstruction.synthesis_axisMode]
  change Psi p (W 0 (Psi r (W 1 (Psi s pauliY)))) = _
  simp only [Psi_y, W_smul, W_y_y, Psi_smul, Psi_unital, W_x_one, Psi_x, smul_smul]
  congr 1
  ring

theorem form_x_x : form pauliX pauliX = 24/25 := by
  norm_num [form, pauliX, R, Matrix.conjTranspose_apply, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_two]

theorem XYY_form (p r s : ℝ) :
    form (tripleSynthesis p r s XYY) (tripleSynthesis p r s XYY) =
      (24/25 : ℂ)^3 * (p:ℂ)^2 * (s:ℂ)^2 := by
  rw [XYY_synthesis, form_smul, form_x_x]
  norm_num only [star_mul, star_div, star_ofNat, Complex.star_def, map_mul, map_div₀,
    map_ofNat, Complex.conj_ofReal]
  ring

theorem XYY_zero_outer (p r : ℝ) : tripleSynthesis p r 0 XYY = 0 := by
  rw [XYY_synthesis]
  simp

theorem XYY_values :
    XYY (0,2,2) = 27 ∧ XYY (1,2,2) = -27 ∧
    XYY (0,3,2) = -27 ∧ XYY (0,2,3) = -27 := by
  norm_num [XYY, PauliInstrumentReconstruction.axisMode, PauliInstrumentReconstruction.sign,
    PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem XYY_three_label_dependence :
    XYY (0,2,2) ≠ XYY (1,2,2) ∧ XYY (0,2,2) ≠ XYY (0,3,2) ∧
    XYY (0,2,2) ≠ XYY (0,2,3) := by
  rcases XYY_values with ⟨h0,h1,h2,h3⟩
  rw [h0,h1,h2,h3]
  norm_num

theorem XYY_positive (p r s : ℝ) (hp : 0 < p) (hs : 0 < s) :
    0 < (form (tripleSynthesis p r s XYY) (tripleSynthesis p r s XYY)).re := by
  rw [XYY_form]
  have he : ((24/25:ℂ)^3 * (p:ℂ)^2 * (s:ℂ)^2).re = (24/25:ℝ)^3 * p^2 * s^2 := by
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im]
  rw [he]
  positivity

theorem observable_x (γ η t : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    NontracialReflectionDynamics.observable γ η t pauliX =
      (Real.exp (-(γ+η)*t):ℂ) • pauliX := by
  rw [NontracialReflectionDynamics.observable_formula γ η t hγ hη ht]
  norm_num [NontracialReflectionDynamics.scalarPart, NontracialReflectionDynamics.diagonalPart,
    rhoN, pauliX, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace,
    Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply, Matrix.one_apply]

theorem XYY_inserted_pairing (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    pairing (sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) XYY XYY =
      (24/25:ℂ)^3 * (p:ℂ)^2 * (s:ℂ)^2 * (Real.exp (-(γ+η)*t):ℂ) := by
  rw [six_pairing_form, XYY_synthesis]
  change form _ (NontracialReflectionDynamics.observableLinear γ η t _) = _
  rw [map_smul]
  change form _ (_ • NontracialReflectionDynamics.observable γ η t pauliX) = _
  rw [observable_x γ η t hγ hη ht, smul_smul, form_smul, form_x_x]
  norm_num only [star_mul, star_div, star_ofNat, Complex.star_def, map_mul, map_div₀,
    map_ofNat, Complex.conj_ofReal]
  ring

theorem XYY_transferred_norm_sq (p r s γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    form (NontracialReflectionDynamics.observable γ η t (tripleSynthesis p r s XYY))
      (NontracialReflectionDynamics.observable γ η t (tripleSynthesis p r s XYY)) =
      (24/25:ℂ)^3 * (p:ℂ)^2 * (s:ℂ)^2 * (Real.exp (-(γ+η)*t):ℂ)^2 := by
  rw [XYY_synthesis]
  change form (NontracialReflectionDynamics.observableLinear γ η t _)
    (NontracialReflectionDynamics.observableLinear γ η t _) = _
  rw [map_smul]
  change form (_ • NontracialReflectionDynamics.observable γ η t pauliX)
    (_ • NontracialReflectionDynamics.observable γ η t pauliX) = _
  rw [observable_x γ η t hγ hη ht, smul_smul, form_smul, form_x_x]
  norm_num only [star_mul, star_div, star_ofNat, Complex.star_def, map_mul, map_div₀,
    map_ofNat, Complex.conj_ofReal]
  ring

theorem two_product_synthesis (p r : ℝ) (f h : Fin 6 → ℂ) :
    synthesis p r (fun u => f u.1 * h u.2) =
      Psi p (∑ i, f i • J i (Psi r (PauliInstrumentReconstruction.synthesis h))) := by
  simp only [synthesis, NontracialPauliReflection.midpoint, halfEffect, Fintype.sum_prod_type,
    PauliInstrumentReconstruction.synthesis, Psi_sum, Psi_smul, J_sumB, J_smulB,
    Finset.smul_sum, smul_smul]

def centeredZScore (i : Fin 6) : ℂ :=
  PauliInstrumentReconstruction.axisMode 2 i - 7/25

def centeredXZ (u : HalfHistory) : ℂ :=
  PauliInstrumentReconstruction.axisMode 0 u.1 * centeredZScore u.2

def XZ (u : HalfHistory) : ℂ :=
  PauliInstrumentReconstruction.axisMode 0 u.1 * PauliInstrumentReconstruction.axisMode 2 u.2

theorem centeredZScore_synthesis :
    PauliInstrumentReconstruction.synthesis centeredZScore = Zc := by
  have he : centeredZScore = PauliInstrumentReconstruction.axisMode 2 - (7/25:ℂ) • (fun _ => 1) := by
    funext i
    simp [centeredZScore]
  rw [he]
  change PauliInstrumentReconstruction.synthesisLinear
    (PauliInstrumentReconstruction.axisMode 2 - (7/25:ℂ) • (fun _ => 1)) = _
  rw [map_sub, map_smul]
  change PauliInstrumentReconstruction.synthesis (PauliInstrumentReconstruction.axisMode 2) -
    (7/25:ℂ) • PauliInstrumentReconstruction.synthesis (fun _ => 1) = _
  rw [PauliInstrumentReconstruction.synthesis_axisMode,
    PauliInstrumentReconstruction.synthesis_constant]
  rfl

theorem Psi_centered_z (r : ℝ) : Psi r Zc = (r:ℂ) • Zc := by
  norm_num [Psi, Zc, rhoN, pauliZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

theorem centeredXZ_synthesis (p r : ℝ) : synthesis p r centeredXZ = 0 := by
  change synthesis p r (fun u => PauliInstrumentReconstruction.axisMode 0 u.1 *
    centeredZScore u.2) = _
  rw [two_product_synthesis, centeredZScore_synthesis]
  change Psi p (W 0 (Psi r Zc)) = _
  rw [Psi_centered_z, W_smul, W_x_centered_z]
  simp [Psi]

theorem centeredXZ_nonzero_coefficient : centeredXZ (0,4) = 204/25 := by
  norm_num [centeredXZ, centeredZScore, PauliInstrumentReconstruction.axisMode,
    PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
    finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]

theorem centeredXZ_actual_null_pairing (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    pairing (kernel p r hp hp1 hr hr1) centeredXZ centeredXZ = 0 := by
  rw [pairing_synthesis, centeredXZ_synthesis]
  simp [form]

theorem W_x_Psi_z (r : ℝ) : W 0 (Psi r pauliZ) = (7/25:ℂ) • pauliX := by
  rw [W_x_formula, Psi_mean]
  norm_num [Psi, rhoN, pauliZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.trace, Fin.sum_univ_two]

theorem XZ_synthesis (p r : ℝ) : synthesis p r XZ = (7*(p:ℂ)/25) • pauliX := by
  change synthesis p r (fun u => PauliInstrumentReconstruction.axisMode 0 u.1 *
    PauliInstrumentReconstruction.axisMode 2 u.2) = _
  rw [two_product_synthesis, PauliInstrumentReconstruction.synthesis_axisMode]
  change Psi p (W 0 (Psi r pauliZ)) = _
  rw [W_x_Psi_z, Psi_smul, Psi_x, smul_smul]
  congr 1
  ring

theorem XZ_form (p r : ℝ) :
    form (synthesis p r XZ) (synthesis p r XZ) = (1176/15625:ℂ)*(p:ℂ)^2 := by
  rw [XZ_synthesis, form_smul, form_x_x]
  norm_num only [star_mul, star_div, star_ofNat, Complex.star_def, map_mul, map_div₀,
    map_ofNat, Complex.conj_ofReal]
  ring

theorem XZ_actual_nonnull (p r : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < (pairing (kernel p r (le_of_lt hp) hp1 hr hr1) XZ XZ).re := by
  rw [pairing_synthesis, XZ_form]
  have he : ((1176/15625:ℂ)*(p:ℂ)^2).re = (1176/15625:ℝ)*p^2 := by
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im]
  rw [he]
  positivity

/-- The chronological negative side uses Phi_r after the six-L channel after Phi_s. -/
def erasedSideKraus (r s : ℝ) :=
  composeKraus (channel r) (composeKraus L (channel s))

theorem erasedSide_normalized (r s : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : IsKrausChannel (erasedSideKraus r s) :=
  isKrausChannel_composeKraus (channel_normalized hr hr1)
    (isKrausChannel_composeKraus measurement_normalized (channel_normalized hs hs1))

theorem erasedSide_action (r s : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (X : Mat2) :
    krausMap (erasedSideKraus r s) X = Phi r (stateM (Phi s X)) := by
  rw [erasedSideKraus, krausMap_composeKraus, krausMap_composeKraus,
    channel_state hr hr1, channel_state hs hs1]
  rfl

/-- Equality of actions follows from the proved complex sector formula, not Kraus records. -/
theorem erased_state_commute (r s : ℝ) (X : Mat2) :
    Phi r (stateM (Phi s X)) = Phi s (stateM (Phi r X)) := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [Matrix.trace_mul_comm _ A, Matrix.trace_mul_comm _ A,
    Phi_Psi_duality, stateM_duality, Phi_Psi_duality,
    Phi_Psi_duality, stateM_duality, Phi_Psi_duality,
    erased_observable_commute]

def erasedStep (r s : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : Step (Fin 2) Unit 6 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (erasedSideKraus r s k)
  normalized := GibbsMultilevelReflection.joint_normalized _ (erasedSide_normalized r s hr hr1 hs hs1)
  instrument := instrument

theorem erasedStep_branch (r s : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (i : Fin 6) (X : Mat2) :
    (erasedStep r s hr hr1 hs hs1).branch (Fin 2) Unit 6 i
      (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint (instrument.branch i (Phi r (stateM (Phi s X)))) := by
  change (instrument.lift Unit).branch i
    (krausMap (fun k => GibbsMultilevelReflection.joint (erasedSideKraus r s k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus, erasedSide_action r s hr hr1 hs hs1]
  exact GibbsMultilevelReflection.joint_kraus _ _

def erasedHalf (r s : ℝ) (u : HalfHistory) : Mat2 :=
  J u.1 (Psi r (M (Psi s (PauliInstrumentReconstruction.effect u.2))))

theorem erasedHalf_adjoint (r s : ℝ) (u : HalfHistory) :
    (erasedHalf r s u)ᴴ = erasedHalf r s u := by
  simp only [erasedHalf, J_adjoint, Psi_adjoint, M_adjoint, effect_adjoint]

/-- Four observed outcomes; the two erased interventions survive inside side evolutions.
Negative and positive chronological side channels have opposite orders. -/
def middleErasedTree (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Tree (Fin 2) Unit 6 4 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (erasedStep r s hr hr1 hs hs1) (fun _ =>
      .node (NontracialReflectionDynamics.centralStep p γ η t hp hp1 hγ hη ht) (fun _ =>
        .node (erasedStep s r hs hs1 hr hr1) (fun _ => .done))))

/-- Operational middle-erased kernel, defined before the trace factorization. -/
def middleErasedKernel (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) : ℂ :=
  (weight (Fin 2) Unit 6 (middleErasedTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
    (u.2,u.1,v.1,v.2,()) (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem middle_erased_actual_run (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    run (Fin 2) Unit 6 (middleErasedTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      (u.2,u.1,v.1,v.2,()) (GibbsMultilevelReflection.joint rhoN) =
      GibbsMultilevelReflection.joint (instrument.branch v.2
        (Phi s (stateM (Phi r (instrument.branch v.1
          (NontracialReflectionDynamics.state γ η t
            (Phi (p*p) (Gamma (erasedHalf r s u))))))))) := by
  simp only [middleErasedTree, run, step_branch, erasedStep_branch,
    NontracialReflectionDynamics.centralStep_branch, Phi_one, branch_rhoN,
    Phi_Gamma, stateM_Gamma, branch_Gamma, erasedHalf]

theorem middle_erased_actual_trace (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    (run (Fin 2) Unit 6 (middleErasedTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      (u.2,u.1,v.1,v.2,()) (GibbsMultilevelReflection.joint rhoN)).trace =
      (erasedHalf r s v * NontracialReflectionDynamics.state γ η t
        (Phi (p*p) (Gamma (erasedHalf r s u)))).trace := by
  rw [middle_erased_actual_run, GibbsMultilevelReflection.joint_trace, branch_trace,
    Phi_Psi_duality, stateM_duality, Phi_Psi_duality, trace_duality]
  rfl

theorem middle_erased_kernel_trace (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    middleErasedKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v =
      (erasedHalf r s v * NontracialReflectionDynamics.state γ η t
        (Phi (p*p) (Gamma (erasedHalf r s u)))).trace := by
  unfold middleErasedKernel weight
  rw [middle_erased_actual_trace]
  apply hermitian_product_real _ _ (erasedHalf_adjoint r s v)
  rw [Phi_Gamma, NontracialReflectionDynamics.intertwining γ η t hγ hη ht,
    Gamma_adjoint, NontracialReflectionDynamics.observable_adjoint,
    Psi_adjoint, erasedHalf_adjoint]

theorem middle_erased_normalized (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∀ h, 0 ≤ weight (Fin 2) Unit 6
      (middleErasedTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h, weight (Fin 2) Unit 6
      (middleErasedTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN)) = 1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

theorem tripleEffect_middle (r s : ℝ) (u : HalfHistory) :
    ∑ m, tripleEffect r s (u.1,m,u.2) = erasedHalf r s u := by
  change (∑ m, JLinear u.1 (PsiLinear r
    (J m (Psi s (PauliInstrumentReconstruction.effect u.2))))) = _
  rw [← map_sum, ← map_sum]
  rfl

/-- Exact paired marginal of the actual six-event process into the actual erased tree. -/
theorem six_middle_marginal (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    ∑ m, ∑ n, sixKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht
      (u.1,m,u.2) (v.1,n,v.2) =
      middleErasedKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v := by
  simp_rw [six_kernel_trace]
  simp only [← Finset.mul_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, tripleEffect_middle,
    ← NontracialReflectionDynamics.state_sum, ← Phi_sum, ← Gamma_sum]
  rw [middle_erased_kernel_trace]

def XX (u : HalfHistory) : ℂ :=
  PauliInstrumentReconstruction.axisMode 0 u.1 * PauliInstrumentReconstruction.axisMode 0 u.2

def ignoreMiddleXX (u : Triple) : ℂ :=
  PauliInstrumentReconstruction.axisMode 0 u.1 * 1 *
    PauliInstrumentReconstruction.axisMode 0 u.2.2

theorem XX_synthesis : synthesis 1 1 XX = (24/25:ℂ) • (1:Mat2) := by
  change synthesis 1 1 (fun u => PauliInstrumentReconstruction.axisMode 0 u.1 *
    PauliInstrumentReconstruction.axisMode 0 u.2) = _
  rw [two_product_synthesis, PauliInstrumentReconstruction.synthesis_axisMode]
  change Psi 1 (W 0 (Psi 1 pauliX)) = _
  simp only [Psi_one, W_x_x]

theorem ignored_XX_synthesis :
    tripleSynthesis 1 1 1 ignoreMiddleXX = (192/625:ℂ) • (1:Mat2) := by
  change tripleSynthesis 1 1 1 (fun u => PauliInstrumentReconstruction.axisMode 0 u.1 * 1 *
    PauliInstrumentReconstruction.axisMode 0 u.2.2) = _
  rw [triple_product_synthesis 1 1 1 (PauliInstrumentReconstruction.axisMode 0)
    (fun _ => 1) (PauliInstrumentReconstruction.axisMode 0), PauliInstrumentReconstruction.synthesis_axisMode]
  simp only [one_smul]
  change Psi 1 (W 0 (Psi 1 (M (Psi 1 pauliX)))) = _
  simp only [Psi_one, M_x, W_smul, W_x_x, smul_smul]
  norm_num

theorem form_one_one : form (1:Mat2) 1 = 1 := by
  simp only [form, Matrix.conjTranspose_one, one_mul, mul_one, R_square, rhoN_trace]

theorem XX_form :
    form (synthesis 1 1 XX) (synthesis 1 1 XX) = 576/625 := by
  rw [XX_synthesis, form_smul, form_one_one]
  norm_num

theorem ignored_XX_form :
    form (tripleSynthesis 1 1 1 ignoreMiddleXX)
      (tripleSynthesis 1 1 1 ignoreMiddleXX) = 36864/390625 := by
  rw [ignored_XX_synthesis, form_smul, form_one_one]
  norm_num

theorem observable_zeroB (γ η : ℝ) (hγ : 0 ≤ γ) (hη : 0 ≤ η) (A : Mat2) :
    NontracialReflectionDynamics.observable γ η 0 A = A := by
  rw [NontracialReflectionDynamics.observable_formula γ η 0 hγ hη (by norm_num)]
  simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_smul]
  module

/-- Exact disturbance in the actual operational pairings, at identity gaps. -/
theorem XX_actual_disturbance :
    pairing (kernel 1 1 (by norm_num) le_rfl (by norm_num) le_rfl) XX XX = 576/625 ∧
    pairing (sixKernel 1 1 1 0 0 0 (by norm_num) le_rfl (by norm_num) le_rfl
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num))
      ignoreMiddleXX ignoreMiddleXX = 36864/390625 ∧
    (576/625:ℂ) ≠ 36864/390625 := by
  constructor
  · rw [pairing_synthesis, XX_form]
  constructor
  · rw [six_pairing_form, observable_zeroB 0 0 (by norm_num) (by norm_num), ignored_XX_form]
  · norm_num

theorem erased_x (r s : ℝ) :
    Psi r (M (Psi s pauliX)) = (8*(r:ℂ)*(s:ℂ)/25) • pauliX := by
  rw [Psi_x, M_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Psi, rhoN, pauliX, NontracialReflectionDynamics.diagonalPart,
      Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem erased_centered_z (r s : ℝ) :
    Psi r (M (Psi s Zc)) = ((r:ℂ)*(s:ℂ)/3) • Zc := by
  rw [erased_observable_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rhoN, pauliZ, Zc, NontracialReflectionDynamics.diagonalPart,
      Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.one_apply]

/-- With nonzero adjacent retentions no scalar reset reproduces both sectors. -/
theorem erased_not_scalar_reset (r s : ℝ) (hrs : r*s ≠ 0) (q : ℝ) :
    (fun A : Mat2 => Psi r (M (Psi s A))) ≠ Psi q := by
  intro h
  have hx := congrArg (fun f : Mat2 → Mat2 => f pauliX 0 1) h
  have hz := congrArg (fun f : Mat2 → Mat2 => f Zc 0 0) h
  rw [erased_x, Psi_x] at hx
  rw [erased_centered_z, Psi_centered_z] at hz
  norm_num [pauliX, Zc, pauliZ] at hx hz
  have hc : (r:ℂ)*(s:ℂ) = 0 := by linear_combination 75 * (hz - hx)
  apply hrs
  exact_mod_cast hc

/-- Positive inserted suffix: unchanged actual centralStep, followed by both side gaps. -/
def insertedPositiveThree (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Tree (Fin 2) Unit 6 3 :=
  .node (NontracialReflectionDynamics.centralStep p γ η t hp hp1 hγ hη ht) (fun _ =>
    .node (step r hr hr1) (fun _ => .node (step s hs hs1) (fun _ => .done)))

theorem inserted_positive_trace (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (v : Triple) (X : Mat2) :
    (run (Fin 2) Unit 6 (insertedPositiveThree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      (v.1,v.2.1,v.2.2,()) (GibbsMultilevelReflection.joint X)).trace =
      (Psi (p*p) (NontracialReflectionDynamics.observable γ η t (tripleEffect r s v)) * X).trace := by
  simp only [insertedPositiveThree, run, step_branch,
    NontracialReflectionDynamics.centralStep_branch, GibbsMultilevelReflection.joint_trace]
  rw [branch_trace, Phi_Psi_duality, trace_duality, Phi_Psi_duality, trace_duality,
    NontracialReflectionDynamics.trace_dual, Phi_Psi_duality]
  rfl

/-- Split effect derived through the generic full-complex backward-effect trace bridge. -/
theorem split_three_indicator_effect (p r s : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) (u : Triple) :
    FiniteAdaptiveProcessRobustness.effect (positiveThree p r s hp hp1 hr hr1 hs hs1)
      (PauliHistoryConsistency.indicatorScore (u.1,u.2.1,u.2.2,())) =
      GibbsMultilevelReflection.joint (Psi p (tripleEffect r s u)) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := PauliHistoryConsistency.joint_surjective X
  rw [PauliHistoryConsistency.effect_complex_trace]
  simp only [PauliHistoryConsistency.indicatorScore, apply_ite, ite_mul,
    Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [positive_three_trace]
  rw [GibbsMultilevelReflection.joint, GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker]
  simp [Matrix.trace]

/-- The actual unsplit effect uses p squared and the full inserted time. -/
theorem unsplit_three_indicator_effect (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u : Triple) :
    FiniteAdaptiveProcessRobustness.effect
      (insertedPositiveThree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      (PauliHistoryConsistency.indicatorScore (u.1,u.2.1,u.2.2,())) =
      GibbsMultilevelReflection.joint
        (Psi (p*p) (NontracialReflectionDynamics.observable γ η t (tripleEffect r s u))) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := PauliHistoryConsistency.joint_surjective X
  rw [PauliHistoryConsistency.effect_complex_trace]
  simp only [PauliHistoryConsistency.indicatorScore, apply_ite, ite_mul,
    Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [inserted_positive_trace]
  rw [GibbsMultilevelReflection.joint, GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker]
  simp [Matrix.trace]

theorem XYY_zero_time_pairing (p r s γ η : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) :
    pairing (sixKernel p r s γ η 0 hp hp1 hr hr1 hs hs1 hγ hη (by norm_num)) XYY XYY =
      (24/25:ℂ)^3*(p:ℂ)^2*(s:ℂ)^2 := by
  rw [six_pairing_form, observable_zeroB γ η hγ hη, XYY_form]

theorem XYY_reset_inner_positive (p s : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    0 < (pairing (sixKernel p 0 s 0 0 0 (le_of_lt hp) hp1 (by norm_num)
      (by norm_num) (le_of_lt hs) hs1 (by norm_num) (by norm_num) (by norm_num)) XYY XYY).re := by
  rw [six_pairing_form, observable_zeroB 0 0 (by norm_num) (by norm_num)]
  exact XYY_positive p 0 s hp hs

theorem XYY_zero_central (r s : ℝ) : tripleSynthesis 0 r s XYY = 0 := by
  rw [XYY_synthesis]
  simp

def erasedHistoryEquiv : (HalfHistory × HalfHistory) ≃ History 6 4 where
  toFun uv := (uv.1.2,uv.1.1,uv.2.1,uv.2.2,())
  invFun h := ((h.2.1,h.1),(h.2.2.1,h.2.2.2.1))
  left_inv uv := by rcases uv with ⟨⟨i,o⟩,⟨j,q⟩⟩; rfl
  right_inv h := by rcases h with ⟨o,i,j,q,⟨⟩⟩; rfl

theorem middle_erased_kernel_normalized (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∑ u, ∑ v, (middleErasedKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v).re) = 1 := by
  have h := erasedHistoryEquiv.sum_comp (fun h => weight (Fin 2) Unit 6
    (middleErasedTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) h
    (GibbsMultilevelReflection.joint rhoN))
  rw [Fintype.sum_prod_type] at h
  change (∑ u, ∑ v, (middleErasedKernel p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht u v).re) =
    ∑ h, weight (Fin 2) Unit 6 (middleErasedTree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN) at h
  exact h.trans (middle_erased_normalized p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht).2

/-- Actual composed half-time evolution, with reset p rather than p squared. -/
def halfSplitKraus (p γ η t : ℝ) :=
  composeKraus (NontracialReflectionDynamics.timeKraus γ η (t/2)) (channel p)

def halfSplitStep (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Step (Fin 2) Unit 6 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (halfSplitKraus p γ η t k)
  normalized := GibbsMultilevelReflection.joint_normalized _
    (isKrausChannel_composeKraus (NontracialReflectionDynamics.normalized γ η (t/2)
      hγ hη (by positivity)) (channel_normalized hp hp1))
  instrument := instrument

theorem halfSplitStep_branch (p γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (i : Fin 6) (X : Mat2) :
    (halfSplitStep p γ η t hp hp1 hγ hη ht).branch (Fin 2) Unit 6 i
      (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint (instrument.branch i
        (NontracialReflectionDynamics.state γ η (t/2) (Phi p X))) := by
  change (instrument.lift Unit).branch i
    (krausMap (fun k => GibbsMultilevelReflection.joint (halfSplitKraus p γ η t k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus, halfSplitKraus, krausMap_composeKraus,
    channel_state hp hp1]
  exact GibbsMultilevelReflection.joint_kraus _ _

def halfSplitPositiveThree (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) : Tree (Fin 2) Unit 6 3 :=
  .node (halfSplitStep p γ η t hp hp1 hγ hη ht) (fun _ =>
    .node (step r hr hr1) (fun _ => .node (step s hs hs1) (fun _ => .done)))

theorem half_split_positive_trace (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (v : Triple) (X : Mat2) :
    (run (Fin 2) Unit 6 (halfSplitPositiveThree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      (v.1,v.2.1,v.2.2,()) (GibbsMultilevelReflection.joint X)).trace =
      (NontracialReflectionDynamics.observable γ η (t/2) (Psi p (tripleEffect r s v)) * X).trace := by
  simp only [halfSplitPositiveThree, run, step_branch, halfSplitStep_branch,
    GibbsMultilevelReflection.joint_trace]
  rw [branch_trace, Phi_Psi_duality, trace_duality, Phi_Psi_duality, trace_duality,
    NontracialReflectionDynamics.trace_dual, Phi_Psi_duality,
    NontracialReflectionDynamics.observable_Psi p γ η (t/2) hγ hη (by positivity)]
  rfl

/-- Third effect: actual half-time inserted split; distinct from the other two effects. -/
theorem half_split_three_indicator_effect (p r s γ η t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u : Triple) :
    FiniteAdaptiveProcessRobustness.effect
      (halfSplitPositiveThree p r s γ η t hp hp1 hr hr1 hs hs1 hγ hη ht)
      (PauliHistoryConsistency.indicatorScore (u.1,u.2.1,u.2.2,())) =
      GibbsMultilevelReflection.joint
        (NontracialReflectionDynamics.observable γ η (t/2) (Psi p (tripleEffect r s u))) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := PauliHistoryConsistency.joint_surjective X
  rw [PauliHistoryConsistency.effect_complex_trace]
  simp only [PauliHistoryConsistency.indicatorScore, apply_ite, ite_mul,
    Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [half_split_positive_trace]
  rw [GibbsMultilevelReflection.joint, GibbsMultilevelReflection.joint,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker]
  simp [Matrix.trace]

theorem W_z_formula (A : Mat2) :
    W 2 A = ((A 0 0 - A 1 1)/2) • (1:Mat2) +
      ((A 0 0 + A 1 1)/2) • pauliZ := by
  have hscore : PauliInstrumentReconstruction.axisMode 2 =
      (![0,0,0,0,3,-3] : Fin 6 → ℂ) := by
    funext o
    fin_cases o <;> norm_num [PauliInstrumentReconstruction.axisMode,
      PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]
  simp only [W, hscore, J_projector, d_values]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, PauliInstrumentReconstruction.axisMode,
      PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign,
      PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma,
      R, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> ring

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

abbrev Gap := PauliHistoryConsistency.Gap
abbrev Labels := PauliHistoryConsistency.Labels

/-- Actual positive chronology, from the inner intervention toward the outside. -/
def historyPositiveTree (q : Gap) : (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => .node (step q.value q.nonnegative q.bounded) (fun _ => .done)
  | r::rs => .node (step q.value q.nonnegative q.bounded) (fun _ => historyPositiveTree r rs)

/-- Actual reversed negative chronology starts with the identity reset. -/
def historyNegativeTree : (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => historyPositiveTree PauliHistoryConsistency.identityGap []
  | r::rs => PauliHistoryConsistency.snocTree (historyNegativeTree rs)
      (step r.value r.nonnegative r.bounded)

def historyReflectedTree (p : Gap) (rs : List Gap) :
    Tree (Fin 2) Unit 6 ((rs.length+1)+(rs.length+1)) :=
  PauliHistoryConsistency.appendTree (historyNegativeTree rs)
    (historyPositiveTree (PauliHistoryConsistency.squaredGap p) rs)

/-- The operational kernel is defined before its trace or Gram factorization. -/
def historyKernel (p : Gap) (rs : List Gap) (u v : Labels rs) : ℂ :=
  (weight (Fin 2) Unit 6 (historyReflectedTree p rs)
    (PauliHistoryConsistency.reflectedHistory rs u v)
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

def historyInsertedPositiveTree (p : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => .node (NontracialReflectionDynamics.centralStep p.value γ η t
      p.nonnegative p.bounded hγ hη ht) (fun _ => .done)
  | r::rs => .node (NontracialReflectionDynamics.centralStep p.value γ η t
      p.nonnegative p.bounded hγ hη ht) (fun _ => historyPositiveTree r rs)

def historyInsertedTree (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    Tree (Fin 2) Unit 6 ((rs.length+1)+(rs.length+1)) :=
  PauliHistoryConsistency.appendTree (historyNegativeTree rs)
    (historyInsertedPositiveTree p γ η t hγ hη ht rs)

/-- Actual inserted weights; no Gram-defined operational kernel. -/
def historyInsertedKernel (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Labels rs) : ℂ :=
  (weight (Fin 2) Unit 6 (historyInsertedTree p rs γ η t hγ hη ht)
    (PauliHistoryConsistency.reflectedHistory rs u v)
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

/-- The observable recursion uses the actual dual branches J. -/
def historyEffect : (rs : List Gap) → Labels rs → Mat2
  | [],u => PauliInstrumentReconstruction.effect u.1
  | r::rs,u => J u.1 (Psi r.value (historyEffect rs u.2))

def historyMidpoint (p : Gap) (rs : List Gap) (u : Labels rs) : Mat2 :=
  Psi p.value (historyEffect rs u)

theorem historyEffect_adjoint (rs : List Gap) (u : Labels rs) :
    (historyEffect rs u)ᴴ = historyEffect rs u := by
  induction rs with
  | nil => exact effect_adjoint u.1
  | cons r rs ih => simp only [historyEffect,J_adjoint,Psi_adjoint,ih]

theorem historyMidpoint_adjoint (p : Gap) (rs : List Gap) (u : Labels rs) :
    (historyMidpoint p rs u)ᴴ = historyMidpoint p rs u := by
  rw [historyMidpoint,Psi_adjoint,historyEffect_adjoint]

/-- This induction is a state identity and retains Gamma at every depth. -/
theorem history_negative_run (rs : List Gap) (u : Labels rs) :
    run (Fin 2) Unit 6 (historyNegativeTree rs)
      (PauliHistoryConsistency.negativeHistory rs u) (GibbsMultilevelReflection.joint rhoN) =
      GibbsMultilevelReflection.joint (Gamma (historyEffect rs u)) := by
  induction rs with
  | nil =>
    rcases u with ⟨o,⟨⟩⟩
    simp only [historyNegativeTree,historyPositiveTree,PauliHistoryConsistency.negativeHistory,
      PauliHistoryConsistency.identityGap,run,step_branch,Phi_one,branch_rhoN,historyEffect]
  | cons r rs ih =>
    rw [historyNegativeTree,PauliHistoryConsistency.negativeHistory,
      PauliHistoryConsistency.run_snoc,ih]
    simp only [step_branch,Phi_Gamma,branch_Gamma,historyEffect]

/-- Separate backward trace induction, quantified over every complex matrix. -/
theorem history_positive_trace (q : Gap) (rs : List Gap) (u : Labels rs) (X : Mat2) :
    (run (Fin 2) Unit 6 (historyPositiveTree q rs) u
      (GibbsMultilevelReflection.joint X)).trace = (Psi q.value (historyEffect rs u)*X).trace := by
  induction rs generalizing q X with
  | nil =>
    rcases u with ⟨o,⟨⟩⟩
    simp only [historyPositiveTree,run,step_branch,GibbsMultilevelReflection.joint_trace,
      branch_trace,Phi_Psi_duality,historyEffect]
  | cons r rs ih =>
    change (run (Fin 2) Unit 6 (historyPositiveTree r rs) u.2
      ((step q.value q.nonnegative q.bounded).branch (Fin 2) Unit 6 u.1
        (GibbsMultilevelReflection.joint X))).trace = _
    rw [step_branch,ih,trace_duality,Phi_Psi_duality]
    rfl

theorem history_inserted_positive_trace (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u : Labels rs) (X : Mat2) :
    (run (Fin 2) Unit 6 (historyInsertedPositiveTree p γ η t hγ hη ht rs) u
      (GibbsMultilevelReflection.joint X)).trace =
      (Psi (p.value*p.value) (NontracialReflectionDynamics.observable γ η t
        (historyEffect rs u))*X).trace := by
  cases rs with
  | nil =>
    rcases u with ⟨o,⟨⟩⟩
    simp only [historyInsertedPositiveTree,run,NontracialReflectionDynamics.centralStep_branch,
      GibbsMultilevelReflection.joint_trace,branch_trace]
    rw [NontracialReflectionDynamics.trace_dual,Phi_Psi_duality]
    rfl
  | cons r rs =>
    change (run (Fin 2) Unit 6 (historyPositiveTree r rs) u.2
      ((NontracialReflectionDynamics.centralStep p.value γ η t p.nonnegative p.bounded
        hγ hη ht).branch (Fin 2) Unit 6 u.1 (GibbsMultilevelReflection.joint X))).trace = _
    rw [NontracialReflectionDynamics.centralStep_branch,history_positive_trace,
      trace_duality,NontracialReflectionDynamics.trace_dual,Phi_Psi_duality]
    rfl

theorem history_actual_trace (p : Gap) (rs : List Gap) (u v : Labels rs) :
    (run (Fin 2) Unit 6 (historyReflectedTree p rs)
      (PauliHistoryConsistency.reflectedHistory rs u v) (GibbsMultilevelReflection.joint rhoN)).trace =
      (historyEffect rs v * Phi (p.value*p.value) (Gamma (historyEffect rs u))).trace := by
  rw [historyReflectedTree,PauliHistoryConsistency.reflectedHistory,
    PauliHistoryConsistency.run_append,history_negative_run,history_positive_trace,← Phi_Psi_duality]
  rfl

theorem history_inserted_actual_trace (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Labels rs) :
    (run (Fin 2) Unit 6 (historyInsertedTree p rs γ η t hγ hη ht)
      (PauliHistoryConsistency.reflectedHistory rs u v) (GibbsMultilevelReflection.joint rhoN)).trace =
      (historyEffect rs v * NontracialReflectionDynamics.state γ η t
        (Phi (p.value*p.value) (Gamma (historyEffect rs u)))).trace := by
  rw [historyInsertedTree,PauliHistoryConsistency.reflectedHistory,
    PauliHistoryConsistency.run_append,history_negative_run,history_inserted_positive_trace,
    ← Phi_Psi_duality,← NontracialReflectionDynamics.trace_dual]

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

theorem history_kernel_trace (p : Gap) (rs : List Gap) (u v : Labels rs) :
    historyKernel p rs u v =
      (historyEffect rs v * Phi (p.value*p.value) (Gamma (historyEffect rs u))).trace := by
  unfold historyKernel weight
  rw [history_actual_trace]
  apply hermitian_product_real _ _ (historyEffect_adjoint rs v)
  rw [Phi_Gamma,Gamma_adjoint,Psi_adjoint,historyEffect_adjoint]

theorem history_inserted_kernel_trace (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Labels rs) :
    historyInsertedKernel p rs γ η t hγ hη ht u v =
      (historyEffect rs v * NontracialReflectionDynamics.state γ η t
        (Phi (p.value*p.value) (Gamma (historyEffect rs u)))).trace := by
  unfold historyInsertedKernel weight
  rw [history_inserted_actual_trace]
  apply hermitian_product_real _ _ (historyEffect_adjoint rs v)
  rw [Phi_Gamma,NontracialReflectionDynamics.intertwining γ η t hγ hη ht,
    Gamma_adjoint,NontracialReflectionDynamics.observable_adjoint,Psi_adjoint,historyEffect_adjoint]

theorem history_kernel_form (p : Gap) (rs : List Gap) (u v : Labels rs) :
    historyKernel p rs u v = form (historyMidpoint p rs u) (historyMidpoint p rs v) := by
  rw [history_kernel_trace,central_split,form,historyMidpoint_adjoint]
  simp only [historyMidpoint,Gamma,Matrix.mul_assoc]

theorem history_inserted_kernel_form (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Labels rs) :
    historyInsertedKernel p rs γ η t hγ hη ht u v =
      form (historyMidpoint p rs u)
        (NontracialReflectionDynamics.observable γ η t (historyMidpoint p rs v)) := by
  rw [history_inserted_kernel_trace,NontracialReflectionDynamics.trace_dual,central_split,
    ← NontracialReflectionDynamics.observable_Psi p.value γ η t hγ hη ht]
  rw [form,historyMidpoint_adjoint]
  simp only [historyMidpoint,Gamma,Matrix.mul_assoc]

theorem history_kernel_gram (p : Gap) (rs : List Gap) (u v : Labels rs) :
    historyKernel p rs u v =
      (NontracialPauliReflection.feature (historyMidpoint p rs v)*(NontracialPauliReflection.feature (historyMidpoint p rs u))ᴴ).trace := by
  rw [history_kernel_form,feature_gram]

theorem history_inserted_half_gram (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Labels rs) :
    historyInsertedKernel p rs γ η t hγ hη ht u v =
      (NontracialPauliReflection.feature (NontracialReflectionDynamics.observable γ η (t/2) (historyMidpoint p rs v)) *
        (NontracialPauliReflection.feature (NontracialReflectionDynamics.observable γ η (t/2)
          (historyMidpoint p rs u)))ᴴ).trace := by
  rw [history_inserted_kernel_form,form_half_time γ η t hγ hη ht,feature_gram]

def historyRawSynthesis (rs : List Gap) (F : Labels rs → ℂ) : Mat2 :=
  ∑ u, F u • historyEffect rs u

def historySynthesis (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) : Mat2 :=
  ∑ u, F u • historyMidpoint p rs u

def historySynthesisLinear (p : Gap) (rs : List Gap) : (Labels rs → ℂ) →ₗ[ℂ] Mat2 where
  toFun := historySynthesis p rs
  map_add' F G := by simp [historySynthesis,add_smul,Finset.sum_add_distrib]
  map_smul' c F := by simp [historySynthesis,Finset.smul_sum,smul_smul]

theorem history_synthesis_raw (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    historySynthesis p rs F = Psi p.value (historyRawSynthesis rs F) := by
  simp only [historySynthesis,historyRawSynthesis,historyMidpoint,Psi_sum,Psi_smul]

theorem history_pairing (p : Gap) (rs : List Gap) (F G : Labels rs → ℂ) :
    pairing (historyKernel p rs) F G = form (historySynthesis p rs F) (historySynthesis p rs G) := by
  simp only [historySynthesis,NontracialReflectionDynamics.form_sum_left,
    NontracialReflectionDynamics.form_sum_right,form_smul]
  simp only [pairing,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,history_kernel_form]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem history_inserted_pairing (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (F G : Labels rs → ℂ) :
    pairing (historyInsertedKernel p rs γ η t hγ hη ht) F G =
      form (historySynthesis p rs F)
        (NontracialReflectionDynamics.observable γ η t (historySynthesis p rs G)) := by
  change _ = form (historySynthesis p rs F)
    (NontracialReflectionDynamics.observableLinear γ η t (historySynthesis p rs G))
  simp only [historySynthesis,map_sum,map_smul,NontracialReflectionDynamics.form_sum_left,
    NontracialReflectionDynamics.form_sum_right,form_smul]
  simp only [pairing,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,
    history_inserted_kernel_form p rs γ η t hγ hη ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change star (F v) * (form _ (NontracialReflectionDynamics.observable γ η t _) * G u) =
    star (F v) * G u * form _ (NontracialReflectionDynamics.observable γ η t _)
  ring

theorem history_posSemidef (p : Gap) (rs : List Gap) : Matrix.PosSemidef (historyKernel p rs) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup (1 : Mat2) Matrix.PosSemidef.one
  letI := Matrix.toMatrixInnerProductSpace (1 : Mat2) Matrix.PosSemidef.one
  have hk : historyKernel p rs = Matrix.gram ℂ (fun u => NontracialPauliReflection.feature (historyMidpoint p rs u)) := by
    ext u v
    change historyKernel p rs u v =
      (NontracialPauliReflection.feature (historyMidpoint p rs v) * 1 *
        (NontracialPauliReflection.feature (historyMidpoint p rs u))ᴴ).trace
    rw [mul_one]
    exact history_kernel_gram p rs u v
  rw [hk]
  exact Matrix.posSemidef_gram ℂ _

theorem history_inserted_posSemidef (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    Matrix.PosSemidef (historyInsertedKernel p rs γ η t hγ hη ht) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup (1 : Mat2) Matrix.PosSemidef.one
  letI := Matrix.toMatrixInnerProductSpace (1 : Mat2) Matrix.PosSemidef.one
  have hk : historyInsertedKernel p rs γ η t hγ hη ht =
      Matrix.gram ℂ (fun u => feature
        (NontracialReflectionDynamics.observable γ η (t/2) (historyMidpoint p rs u))) := by
    ext u v
    change historyInsertedKernel p rs γ η t hγ hη ht u v =
      (NontracialPauliReflection.feature (NontracialReflectionDynamics.observable γ η (t/2)
        (historyMidpoint p rs v)) * 1 *
        (NontracialPauliReflection.feature (NontracialReflectionDynamics.observable γ η (t/2)
          (historyMidpoint p rs u)))ᴴ).trace
    rw [mul_one]
    exact history_inserted_half_gram p rs γ η t hγ hη ht u v
  rw [hk]
  exact Matrix.posSemidef_gram ℂ _

theorem history_actual_probabilities (p : Gap) (rs : List Gap) :
    (∀ h, 0 ≤ weight (Fin 2) Unit 6 (historyReflectedTree p rs) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
      (∑ h, weight (Fin 2) Unit 6 (historyReflectedTree p rs) h
        (GibbsMultilevelReflection.joint rhoN)) = 1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

theorem history_inserted_actual_probabilities (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∀ h, 0 ≤ weight (Fin 2) Unit 6 (historyInsertedTree p rs γ η t hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
      (∑ h, weight (Fin 2) Unit 6 (historyInsertedTree p rs γ η t hγ hη ht) h
        (GibbsMultilevelReflection.joint rhoN)) = 1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

abbrev HistorySpace (p : Gap) (rs : List Gap) := Space (historyKernel p rs) (history_posSemidef p rs)

theorem history_null_iff (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    mk (historyKernel p rs) (history_posSemidef p rs) F = 0 ↔ historySynthesis p rs F = 0 := by
  rw [mk_eq_zero_iff,history_pairing,form_self_zero_iff]
def historyCoordinates (p : Gap) (rs : List Gap) : HistorySpace p rs →ₗ[ℂ] Mat2 :=
  ((nullSpace (historyKernel p rs) (history_posSemidef p rs)).liftQ
    (historySynthesisLinear p rs) (by
      intro F hF
      change historySynthesis p rs F=0
      apply (history_null_iff p rs F).mp
      rw [mk_eq_zero_iff]
      exact (mem_nullSpace_iff _ _ F).mp hF)).comp
    (quotientEquiv (historyKernel p rs) (history_posSemidef p rs)).symm.toLinearMap

theorem historyCoordinates_mk (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    historyCoordinates p rs (mk _ _ F)=historySynthesis p rs F := by
  rw [← quotientEquiv_mk (history_posSemidef p rs) F]
  simp only [historyCoordinates,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]
  rfl

theorem historyCoordinates_injective (p : Gap) (rs : List Gap) :
    Function.Injective (historyCoordinates p rs) := by
  intro z w h
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  obtain ⟨G,rfl⟩ := mk_surjective _ _ w
  rw [historyCoordinates_mk,historyCoordinates_mk] at h
  apply (mk_eq_mk_iff _ _ F G).mpr
  rw [history_pairing]
  have hz : historySynthesis p rs (F-G)=0 :=
    (historySynthesisLinear p rs).map_sub F G |>.trans (sub_eq_zero.mpr h)
  simp [hz,form]

/-- Sum all outcomes outward of a fixed inner event. -/
theorem historyEffect_inner_sum (rs : List Gap) (i : Fin 6) :
    (∑ h : History 6 rs.length, historyEffect rs (i,h))=PauliInstrumentReconstruction.effect i := by
  induction rs generalizing i with
  | nil => simp [historyEffect,History]
  | cons r rs ih =>
    change (∑ h : Fin 6 × History 6 rs.length, J i (Psi r.value (historyEffect rs h)))=_
    rw [Fintype.sum_prod_type]
    change (∑ o, ∑ h, JLinear i (PsiLinear r.value (historyEffect rs (o,h))))=_
    simp only [← map_sum,ih,effect_sum]
    change J i (Psi r.value 1)=PauliInstrumentReconstruction.effect i
    rw [Psi_unital,J_one]

theorem historySynthesis_inner (p : Gap) (rs : List Gap) (F : Fin 6 → ℂ) :
    historySynthesis p rs (fun u => F u.1)=Psi p.value (PauliInstrumentReconstruction.synthesis F) := by
  change (∑ u : Fin 6 × History 6 rs.length, F u.1 • Psi p.value (historyEffect rs u))=_
  rw [Fintype.sum_prod_type]
  simp only [← Finset.smul_sum,← Psi_sum,historyEffect_inner_sum,← Psi_smul]
  rfl

theorem historySynthesis_constant (p : Gap) (rs : List Gap) :
    historySynthesis p rs (fun _ => 1)=1 := by
  have h := historySynthesis_inner p rs (fun _ => (1:ℂ))
  rw [PauliInstrumentReconstruction.synthesis_constant,Psi_unital] at h
  exact h


/-- The inverse uses only positive central retention, never a side retention. -/
def historyCoefficients (p : Gap) (X : Mat2) (rs : List Gap) (u : Labels rs) : ℂ :=
  PauliInstrumentReconstruction.coefficients (inversePsi p.value X) u.1

theorem historySynthesis_coefficients (p : Gap) (hp : 0<p.value) (rs : List Gap) (X : Mat2) :
    historySynthesis p rs (historyCoefficients p X rs)=X := by
  change historySynthesis p rs (fun u => PauliInstrumentReconstruction.coefficients (inversePsi p.value X) u.1)=X
  rw [historySynthesis_inner,PauliInstrumentReconstruction.synthesis_coefficients,Psi_inverse hp]

def historyCoordinateEquiv (p : Gap) (hp : 0<p.value) (rs : List Gap) : HistorySpace p rs ≃ₗ[ℂ] Mat2 :=
  LinearEquiv.ofBijective (historyCoordinates p rs) ⟨historyCoordinates_injective p rs,by
    intro X
    exact ⟨mk _ _ (historyCoefficients p X rs),by rw [historyCoordinates_mk,historySynthesis_coefficients p hp]⟩⟩

theorem history_finrank (p : Gap) (hp : 0<p.value) (rs : List Gap) :
    Module.finrank ℂ (HistorySpace p rs)=4 := by
  rw [(historyCoordinateEquiv p hp rs).finrank_eq]
  simpa using Module.finrank_matrix ℂ ℂ (Fin 2) (Fin 2)

/-- The actual central-reset synthesis is a scalar identity, even with zero side gaps. -/
def historyMean (rs : List Gap) (F : Labels rs → ℂ) : ℂ :=
  (rhoN * historyRawSynthesis rs F).trace

theorem historySynthesis_reset (p : Gap) (hp : p.value=0) (rs : List Gap) (F : Labels rs → ℂ) :
    historySynthesis p rs F=historyMean rs F • (1:Mat2) := by
  rw [history_synthesis_raw,hp,Psi_zero]
  rfl

theorem historyMean_constant (rs : List Gap) : historyMean rs (fun _ => 1)=1 := by
  have h := historySynthesis_constant (⟨0,le_rfl,by norm_num⟩ : Gap) rs
  rw [historySynthesis_reset _ rfl] at h
  have he := congrArg (fun X : Mat2 => X 0 0) h
  simpa using he

theorem history_reset_null (p : Gap) (hp : p.value=0) (rs : List Gap) (F : Labels rs → ℂ) :
    mk (historyKernel p rs) (history_posSemidef p rs) F=0 ↔ historyMean rs F=0 := by
  rw [history_null_iff,historySynthesis_reset p hp]
  constructor
  · intro h; have he := congrArg (fun X : Mat2 => X 0 0) h; simpa using he
  · intro h; simp [h]

def historyResetCoordinates (p : Gap) (rs : List Gap) : HistorySpace p rs →ₗ[ℂ] ℂ where
  toFun z := historyCoordinates p rs z 0 0
  map_add' z w := by simp
  map_smul' c z := by simp

theorem historyResetCoordinates_mk (p : Gap) (hp : p.value=0) (rs : List Gap) (F : Labels rs → ℂ) :
    historyResetCoordinates p rs (mk _ _ F)=historyMean rs F := by
  change historyCoordinates p rs (mk _ _ F) 0 0=_
  rw [historyCoordinates_mk,historySynthesis_reset p hp]
  simp

def historyResetEquiv (p : Gap) (hp : p.value=0) (rs : List Gap) : HistorySpace p rs ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (historyResetCoordinates p rs) ⟨by
    intro z w h
    apply historyCoordinates_injective p rs
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [historyResetCoordinates_mk p hp,historyResetCoordinates_mk p hp] at h
    rw [historyCoordinates_mk,historyCoordinates_mk,historySynthesis_reset p hp,historySynthesis_reset p hp,h],by
    intro c
    refine ⟨c • mk _ _ (fun _ => 1),?_⟩
    rw [map_smul,historyResetCoordinates_mk p hp,historyMean_constant]
    simp⟩

theorem history_reset_finrank (p : Gap) (hp : p.value=0) (rs : List Gap) :
    Module.finrank ℂ (HistorySpace p rs)=1 := by
  rw [(historyResetEquiv p hp rs).finrank_eq]
  exact Module.finrank_self ℂ

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

abbrev outerEquiv := PauliHistoryConsistency.outerEquiv
abbrev outerPull := PauliHistoryConsistency.outerPull


theorem historyEffect_outer (q : Gap) (rs : List Gap) (h : Labels rs) :
    (∑ o, historyEffect (rs++[q]) ((outerEquiv q rs).symm (h,o)))=historyEffect rs h := by
  induction rs with
  | nil => exact halfEffect_outer q.value h.1
  | cons r rs ih =>
    change (∑ o, JLinear h.1 (PsiLinear r.value
      (historyEffect (rs++[q]) ((outerEquiv q rs).symm (h.2,o)))) )=_
    rw [← map_sum,← map_sum,ih]
    rfl

theorem historyMidpoint_outer (p q : Gap) (rs : List Gap) (h : Labels rs) :
    (∑ o, historyMidpoint p (rs++[q]) ((outerEquiv q rs).symm (h,o)))=historyMidpoint p rs h := by
  simp only [historyMidpoint,← Psi_sum,historyEffect_outer]

/-- The actual larger tree has the old kernel as its paired outer marginal. -/
theorem history_kernel_outer (p q : Gap) (rs : List Gap) (u v : Labels rs) :
    (∑ o, ∑ t, historyKernel p (rs++[q]) ((outerEquiv q rs).symm (u,o))
      ((outerEquiv q rs).symm (v,t)))=historyKernel p rs u v := by
  simp_rw [history_kernel_form]
  simp only [← NontracialReflectionDynamics.form_sum_right,historyMidpoint_outer]
  rw [← NontracialReflectionDynamics.form_sum_left,historyMidpoint_outer]

theorem historySynthesis_outerPull (p q : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    historySynthesis p (rs++[q]) (outerPull q rs F)=historySynthesis p rs F := by
  unfold historySynthesis outerPull PauliHistoryConsistency.outerPull
  rw [← (outerEquiv q rs).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply,← Finset.smul_sum,historyMidpoint_outer]

theorem history_pairing_outerPull (p q : Gap) (rs : List Gap) (F G : Labels rs → ℂ) :
    pairing (historyKernel p (rs++[q])) (outerPull q rs F) (outerPull q rs G)=
      pairing (historyKernel p rs) F G := by
  rw [history_pairing,history_pairing,historySynthesis_outerPull,historySynthesis_outerPull]

def outerPullLinear (q : Gap) (rs : List Gap) : (Labels rs → ℂ) →ₗ[ℂ] (Labels (rs++[q]) → ℂ) where
  toFun := outerPull q rs
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Descend the literal coefficient pullback through the actual null quotients. -/
def outerMapLinear (p q : Gap) (rs : List Gap) : HistorySpace p rs →ₗ[ℂ] HistorySpace p (rs++[q]) :=
  ((nullSpace (historyKernel p rs) (history_posSemidef p rs)).liftQ
    ((mkLinear (historyKernel p (rs++[q])) (history_posSemidef p (rs++[q]))).comp (outerPullLinear q rs))
    (by
      intro F hF
      change mk _ _ (outerPull q rs F)=0
      rw [history_null_iff,historySynthesis_outerPull]
      apply (history_null_iff p rs F).mp
      rw [mk_eq_zero_iff]
      exact (mem_nullSpace_iff _ _ F).mp hF)).comp
    (quotientEquiv (historyKernel p rs) (history_posSemidef p rs)).symm.toLinearMap

theorem outerMapLinear_mk (p q : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    outerMapLinear p q rs (mk _ _ F)=mk _ _ (outerPull q rs F) := by
  rw [← quotientEquiv_mk (history_posSemidef p rs) F]
  simp only [outerMapLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]
  rfl

def outerMap (p q : Gap) (rs : List Gap) : HistorySpace p rs →ₗᵢ[ℂ] HistorySpace p (rs++[q]) :=
  (outerMapLinear p q rs).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [outerMapLinear_mk,outerMapLinear_mk,inner_mk,inner_mk,history_pairing_outerPull])

theorem outerMap_mk (p q : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    outerMap p q rs (mk _ _ F)=mk _ _ (outerPull q rs F) := outerMapLinear_mk p q rs F

theorem outerMap_coordinates (p q : Gap) (rs : List Gap) (z : HistorySpace p rs) :
    historyCoordinates p (rs++[q]) (outerMap p q rs z)=historyCoordinates p rs z := by
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  rw [outerMap_mk,historyCoordinates_mk,historyCoordinates_mk,historySynthesis_outerPull]

theorem history_inserted_kernel_outer (p q : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Labels rs) :
    (∑ o, ∑ j, historyInsertedKernel p (rs++[q]) γ η t hγ hη ht
      ((outerEquiv q rs).symm (u,o)) ((outerEquiv q rs).symm (v,j))) =
      historyInsertedKernel p rs γ η t hγ hη ht u v := by
  simp_rw [history_inserted_kernel_form]
  change (∑ o, ∑ j, form _
    (NontracialReflectionDynamics.observableLinear γ η t
      (historyMidpoint p (rs++[q]) ((outerEquiv q rs).symm (v,j))))) = _
  simp only [← NontracialReflectionDynamics.form_sum_right,← map_sum,historyMidpoint_outer]
  rw [← NontracialReflectionDynamics.form_sum_left,historyMidpoint_outer]
  rfl

theorem history_inserted_pairing_outerPull (p q : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (F G : Labels rs → ℂ) :
    pairing (historyInsertedKernel p (rs++[q]) γ η t hγ hη ht)
      (outerPull q rs F) (outerPull q rs G) =
      pairing (historyInsertedKernel p rs γ η t hγ hη ht) F G := by
  rw [history_inserted_pairing,history_inserted_pairing,
    historySynthesis_outerPull,historySynthesis_outerPull]

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

/-- Literal end insertion, an instrument-independent index bijection. -/
def historySnocEquiv : (n : ℕ) → (History 6 n × Fin 6) ≃ History 6 (n+1)
  | 0 => {
    toFun := fun h => (h.2,())
    invFun := fun h => ((),h.1)
    left_inv := by rintro ⟨⟨⟩,o⟩; rfl
    right_inv := by rintro ⟨o,⟨⟩⟩; rfl }
  | n+1 => {
    toFun := fun h => (h.1.1,historySnocEquiv n (h.1.2,h.2))
    invFun := fun h => ((h.1,((historySnocEquiv n).symm h.2).1),
      ((historySnocEquiv n).symm h.2).2)
    left_inv := by intro h; simp
    right_inv := by intro h; simp }

theorem historySnocEquiv_apply (n : ℕ) (h : History 6 n) (o : Fin 6) :
    historySnocEquiv n (h,o) = PauliHistoryConsistency.snocHistory h o := by
  induction n with
  | zero => rfl
  | succ n ih => change (h.1,historySnocEquiv n (h.2,o)) = _
                 rw [ih]; rfl

def historyAppendEquiv : (n m : ℕ) → (History 6 n × History 6 m) ≃ History 6 (m+n)
  | 0,m => {
    toFun := fun h => h.2
    invFun := fun h => ((),h)
    left_inv := by rintro ⟨⟨⟩,h⟩; rfl
    right_inv := by intro h; rfl }
  | n+1,m => {
    toFun := fun h => (h.1.1,historyAppendEquiv n m (h.1.2,h.2))
    invFun := fun h => ((h.1,((historyAppendEquiv n m).symm h.2).1),
      ((historyAppendEquiv n m).symm h.2).2)
    left_inv := by intro h; simp
    right_inv := by intro h; simp }

theorem historyAppendEquiv_apply (n m : ℕ) (h : History 6 n) (k : History 6 m) :
    historyAppendEquiv n m (h,k) = PauliHistoryConsistency.appendHistory h k := by
  induction n with
  | zero => rfl
  | succ n ih => change (h.1,historyAppendEquiv n m (h.2,k)) = _
                 rw [ih]; rfl

def historyNegativeEquiv : (rs : List Gap) → Labels rs ≃ Labels rs
  | [] => Equiv.refl _
  | _::rs => ((Equiv.prodCongr (Equiv.refl (Fin 6)) (historyNegativeEquiv rs)).trans
      (Equiv.prodComm _ _)).trans (historySnocEquiv (rs.length+1))

theorem historyNegativeEquiv_apply (rs : List Gap) (u : Labels rs) :
    historyNegativeEquiv rs u = PauliHistoryConsistency.negativeHistory rs u := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change historySnocEquiv (rs.length+1) (historyNegativeEquiv rs u.2,u.1) = _
    rw [historySnocEquiv_apply,ih]
    rfl

def historyPairEquiv (rs : List Gap) :
    (Labels rs × Labels rs) ≃ History 6 ((rs.length+1)+(rs.length+1)) :=
  (Equiv.prodCongr (historyNegativeEquiv rs) (Equiv.refl _)).trans
    (historyAppendEquiv (rs.length+1) (rs.length+1))

theorem historyPairEquiv_apply (rs : List Gap) (u v : Labels rs) :
    historyPairEquiv rs (u,v) = PauliHistoryConsistency.reflectedHistory rs u v := by
  change historyAppendEquiv _ _ (historyNegativeEquiv rs u,v) = _
  rw [historyAppendEquiv_apply,historyNegativeEquiv_apply]
  rfl

theorem history_kernel_normalized (p : Gap) (rs : List Gap) :
    (∑ u, ∑ v, (historyKernel p rs u v).re) = 1 := by
  have h := (historyPairEquiv rs).sum_comp (fun h => weight (Fin 2) Unit 6
    (historyReflectedTree p rs) h (GibbsMultilevelReflection.joint rhoN))
  rw [Fintype.sum_prod_type] at h
  simp only [historyPairEquiv_apply] at h
  change (∑ u, ∑ v, (historyKernel p rs u v).re) =
    ∑ h, weight (Fin 2) Unit 6 (historyReflectedTree p rs) h
      (GibbsMultilevelReflection.joint rhoN) at h
  exact h.trans (history_actual_probabilities p rs).2

theorem history_inserted_kernel_normalized (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) :
    (∑ u, ∑ v, (historyInsertedKernel p rs γ η t hγ hη ht u v).re) = 1 := by
  have h := (historyPairEquiv rs).sum_comp (fun h => weight (Fin 2) Unit 6
    (historyInsertedTree p rs γ η t hγ hη ht) h (GibbsMultilevelReflection.joint rhoN))
  rw [Fintype.sum_prod_type] at h
  simp only [historyPairEquiv_apply] at h
  change (∑ u, ∑ v, (historyInsertedKernel p rs γ η t hγ hη ht u v).re) =
    ∑ h, weight (Fin 2) Unit 6 (historyInsertedTree p rs γ η t hγ hη ht) h
      (GibbsMultilevelReflection.joint rhoN) at h
  exact h.trans (history_inserted_actual_probabilities p rs γ η t hγ hη ht).2

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

theorem history_coordinates_inner (p : Gap) (rs : List Gap) (z w : HistorySpace p rs) :
    ⟪z,w⟫_ℂ = form (historyCoordinates p rs z) (historyCoordinates p rs w) := by
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  obtain ⟨G,rfl⟩ := mk_surjective _ _ w
  rw [inner_mk,history_pairing,historyCoordinates_mk,historyCoordinates_mk]

def historyEmbeddingLinear (p : Gap) (rs : List Gap) : HistorySpace p rs →ₗ[ℂ] Mat2 :=
  featureLinear.comp (historyCoordinates p rs)

theorem historyEmbeddingLinear_mk (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    historyEmbeddingLinear p rs (mk _ _ F) =
      NontracialPauliReflection.feature (historySynthesis p rs F) := by
  change NontracialPauliReflection.feature (historyCoordinates p rs (mk _ _ F)) = _
  rw [historyCoordinates_mk]

section HilbertSchmidtEmbedding
local instance : NormedAddCommGroup Mat2 := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance : InnerProductSpace ℂ Mat2 := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- Features are isometric in the Hilbert-Schmidt matrix metric. -/
def historyEmbedding (p : Gap) (rs : List Gap) : HistorySpace p rs →ₗᵢ[ℂ] Mat2 :=
  (historyEmbeddingLinear p rs).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [historyEmbeddingLinear_mk,historyEmbeddingLinear_mk,inner_mk,history_pairing]
    change (NontracialPauliReflection.feature (historySynthesis p rs G) * 1 *
      (NontracialPauliReflection.feature (historySynthesis p rs F))ᴴ).trace = _
    simpa using feature_gram (historySynthesis p rs F) (historySynthesis p rs G))

theorem historyEmbedding_mk (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    historyEmbedding p rs (mk _ _ F) =
      NontracialPauliReflection.feature (historySynthesis p rs F) :=
  historyEmbeddingLinear_mk p rs F

theorem historyEmbedding_outer (p q : Gap) (rs : List Gap) (z : HistorySpace p rs) :
    historyEmbedding p (rs++[q]) (outerMap p q rs z) = historyEmbedding p rs z := by
  change NontracialPauliReflection.feature (historyCoordinates p (rs++[q]) (outerMap p q rs z)) = _
  rw [outerMap_coordinates]
  rfl
end HilbertSchmidtEmbedding

theorem history_coordinates_surjective (p : Gap) (hp : 0 < p.value) (rs : List Gap) :
    Function.Surjective (historyCoordinates p rs) := by
  intro A
  exact ⟨mk _ _ (historyCoefficients p A rs),by
    rw [historyCoordinates_mk,historySynthesis_coefficients p hp]⟩

theorem history_feature_range_positive (p : Gap) (hp : 0 < p.value) (rs : List Gap) :
    Function.Surjective (historyEmbeddingLinear p rs) := by
  intro A
  obtain ⟨B,hB⟩ := feature_surjective A
  obtain ⟨z,hz⟩ := history_coordinates_surjective p hp rs B
  refine ⟨z,?_⟩
  change NontracialPauliReflection.feature (historyCoordinates p rs z) = A
  rw [hz,hB]

theorem history_coordinates_reset (p : Gap) (hp : p.value = 0) (rs : List Gap) (z : HistorySpace p rs) :
    historyCoordinates p rs z = historyResetCoordinates p rs z • (1 : Mat2) := by
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  rw [historyCoordinates_mk,historyResetCoordinates_mk p hp,historySynthesis_reset p hp]

theorem history_feature_range_reset (p : Gap) (hp : p.value = 0) (rs : List Gap) (A : Mat2) :
    A ∈ (historyEmbeddingLinear p rs).range ↔ ∃ c : ℂ, A = c • R := by
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨historyResetCoordinates p rs z,?_⟩
    change NontracialPauliReflection.feature (historyCoordinates p rs z) = _
    rw [history_coordinates_reset p hp]
    change featureLinear (_ • (1 : Mat2)) = _
    rw [map_smul]
    change _ • (Q * 1 * Q) = _
    rw [mul_one,Q_square]
  · rintro ⟨c,rfl⟩
    refine ⟨c • mk _ _ (fun _ => 1),?_⟩
    rw [map_smul,historyEmbeddingLinear_mk,historySynthesis_constant]
    simp only [NontracialPauliReflection.feature,mul_one,Q_square]

/-- Depth zero recovers the accepted actual two-event trace kernel. -/
theorem history_depth_zero (p : Gap) (i j : Fin 6) :
    historyKernel p [] (i,()) (j,()) = twoKernel p.value p.nonnegative p.bounded i j := by
  rw [history_kernel_trace,twoKernel_trace]
  rfl

/-- Explicit one-gap labels, including zero central and side retentions. -/
def historyPairLabels (r : Gap) (u : HalfHistory) : Labels [r] := (u.1,u.2,())

theorem history_depth_one (p r : Gap) (u v : HalfHistory) :
    historyKernel p [r] (historyPairLabels r u) (historyPairLabels r v) =
      kernel p.value r.value p.nonnegative p.bounded r.nonnegative r.bounded u v := by
  rw [history_kernel_trace,kernel_trace]
  rfl

theorem history_inserted_depth_one (p r : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : HalfHistory) :
    historyInsertedKernel p [r] γ η t hγ hη ht (historyPairLabels r u) (historyPairLabels r v) =
      NontracialReflectionDynamics.kernel p.value r.value γ η t p.nonnegative p.bounded
        r.nonnegative r.bounded hγ hη ht u v := by
  rw [history_inserted_kernel_trace,NontracialReflectionDynamics.kernel_trace]
  rfl

/-- The actual inserted process at depth zero retains its full complex central state action. -/
theorem history_inserted_depth_zero (p : Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (i j : Fin 6) :
    historyInsertedKernel p [] γ η t hγ hη ht (i,()) (j,()) =
      (PauliInstrumentReconstruction.effect j * NontracialReflectionDynamics.state γ η t
        (Phi (p.value*p.value) (Gamma (PauliInstrumentReconstruction.effect i)))).trace := by
  rw [history_inserted_kernel_trace]
  rfl

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
open Matrix FiniteInterventionProcess NontracialPauliReflection FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

theorem history_kernel_nonnegative (p : Gap) (rs : List Gap) (u v : Labels rs) :
    0 ≤ (historyKernel p rs u v).re :=
  (history_actual_probabilities p rs).1 (PauliHistoryConsistency.reflectedHistory rs u v)

theorem history_inserted_kernel_nonnegative (p : Gap) (rs : List Gap) (γ η t : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (ht : 0 ≤ t) (u v : Labels rs) :
    0 ≤ (historyInsertedKernel p rs γ η t hγ hη ht u v).re :=
  (history_inserted_actual_probabilities p rs γ η t hγ hη ht).1
    (PauliHistoryConsistency.reflectedHistory rs u v)

theorem history_inserted_zero (p : Gap) (rs : List Gap) (γ η : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 ≤ η) (u v : Labels rs) :
    historyInsertedKernel p rs γ η 0 hγ hη (by norm_num) u v = historyKernel p rs u v := by
  rw [history_inserted_kernel_form,observable_zeroB γ η hγ hη,history_kernel_form]

theorem history_feature_null_iff (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    mk (historyKernel p rs) (history_posSemidef p rs) F = 0 ↔
      NontracialPauliReflection.feature (historySynthesis p rs F) = 0 := by
  rw [history_null_iff]
  constructor
  · rintro h; simp [h,NontracialPauliReflection.feature]
  · intro h
    apply feature_injective
    simpa [NontracialPauliReflection.feature] using h

end SKEFTHawking.QuantumNetwork.NontracialHistoryConsistency
