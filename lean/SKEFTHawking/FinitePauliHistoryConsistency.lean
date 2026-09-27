import SKEFTHawking.FinitePauliReflectedCylinder
import SKEFTHawking.QuantumNetwork.FiniteAdaptiveProcessRobustness

/-! Actual finite symmetric stationary Pauli histories, full complex reconstruction, and
compatible mirrored outer extensions. The kernel is defined from chronological process weights;
ordered noncommuting branch effects supply its Gram representation. Literal outer-coordinate
pullback descends to surjective quotient isometries, with identity and transported composition.
Positive central retention realizes all qubit matrices; complete central reset has scalar rank one.
An erased interior outcome retains its measurement channel, witnessed by the six-event XX defect.
The real-indicator bridge distinguishes the split half-step from the actual unsplit suffix.
No arbitrary schedule-deletion consistency, adaptive/nonstationary reflection theorem, continuum
field reconstruction, physical clock identification, or publication readiness is asserted. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder
open scoped BigOperators ComplexOrder Kronecker

/-- Coordinates run from the midpoint outward: inner, middle, outer. -/
abbrev Triple := Fin 6 × Fin 6 × Fin 6

def sixTree (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) : Tree (Fin 2) Unit 6 6 :=
  .node (PauliReflectedCylinder.step 1 (by norm_num) le_rfl) (fun _ =>
    .node (PauliReflectedCylinder.step s hs hs1) (fun _ =>
      .node (PauliReflectedCylinder.step r hr hr1) (fun _ =>
        .node (PauliReflectedCylinder.step (p*p) (mul_nonneg hp hp) (by nlinarith)) (fun _ =>
          .node (PauliReflectedCylinder.step r hr hr1) (fun _ =>
            .node (PauliReflectedCylinder.step s hs hs1) (fun _ => .done))))))

def sixHistory (u v : Triple) : History 6 6 :=
  (u.2.2,u.2.1,u.1,v.1,v.2.1,v.2.2,())

/-- Defined from actual process weights before the operator factorization. -/
def sixKernel (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (u v : Triple) : ℂ :=
  (weight (Fin 2) Unit 6 (sixTree p r s hp hp1 hr hr1 hs hs1) (sixHistory u v)
    (GibbsMultilevelReflection.joint rho) : ℂ)

def tripleEffect (r s : ℝ) (u : Triple) : Mat :=
  instrument.branch u.1 (D r (instrument.branch u.2.1 (D s (effect u.2.2))))

def tripleMidpoint (p r s : ℝ) (u : Triple) : Mat := D p (tripleEffect r s u)

theorem tripleEffect_adjoint (r s : ℝ) (u : Triple) : (tripleEffect r s u)ᴴ=tripleEffect r s u := by
  simp only [tripleEffect,branch_adjoint,D_adjoint,effect_adjoint]

theorem tripleMidpoint_adjoint (p r s : ℝ) (u : Triple) :
    (tripleMidpoint p r s u)ᴴ=tripleMidpoint p r s u := by
  rw [tripleMidpoint,D_adjoint,tripleEffect_adjoint]

theorem six_actual_run (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (u v : Triple) :
    run (Fin 2) Unit 6 (sixTree p r s hp hp1 hr hr1 hs hs1) (sixHistory u v)
      (GibbsMultilevelReflection.joint rho)=
    GibbsMultilevelReflection.joint ((1/2:ℂ) • instrument.branch v.2.2
      (D s (instrument.branch v.2.1 (D r (instrument.branch v.1
        (D (p*p) (tripleEffect r s u))))))) := by
  simp only [sixTree,sixHistory,run,PauliReflectedCylinder.step_branch,D_one,branch_rho,
    D_smul,FiniteInstrument.branch_smul,tripleEffect]

theorem six_actual_trace (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (u v : Triple) :
    (run (Fin 2) Unit 6 (sixTree p r s hp hp1 hr hr1 hs hs1) (sixHistory u v)
      (GibbsMultilevelReflection.joint rho)).trace=
    (1/2:ℂ)*(tripleEffect r s v*D (p*p) (tripleEffect r s u)).trace := by
  rw [six_actual_run,GibbsMultilevelReflection.joint_trace,Matrix.trace_smul,branch_trace,
    D_trace_dual,branch_trace_dual,D_trace_dual,branch_trace_dual]
  rfl

theorem six_kernel_trace (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (u v : Triple) :
    sixKernel p r s hp hp1 hr hr1 hs hs1 u v=
    (1/2:ℂ)*(tripleEffect r s v*D (p*p) (tripleEffect r s u)).trace := by
  unfold sixKernel weight
  rw [six_actual_trace]
  have h := hermitian_product_real (tripleEffect r s v) (D (p*p) (tripleEffect r s u))
    (tripleEffect_adjoint r s v) (by rw [D_adjoint,tripleEffect_adjoint])
  simp only [Complex.mul_re]
  norm_num
  rw [h]

/-- Full complex Gram identity derived from the six actual interventions. -/
theorem six_kernel_gram (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (u v : Triple) :
    sixKernel p r s hp hp1 hr hr1 hs hs1 u v=
      (tripleMidpoint p r s v*rho*(tripleMidpoint p r s u)ᴴ).trace := by
  rw [six_kernel_trace,central_split,tripleMidpoint_adjoint]
  simp only [tripleMidpoint,rho,mul_smul_comm,mul_one,smul_mul_assoc,Matrix.trace_smul,smul_eq_mul]

theorem tripleEffect_outer (r s : ℝ) (i m : Fin 6) :
    ∑ o, tripleEffect r s (i,m,o)=halfEffect r (i,m) := by
  change (∑ o, branchLinear i (DLinear r (halfEffect s (m,o))))=_
  rw [← map_sum,← map_sum,halfEffect_outer]
  rfl

theorem tripleMidpoint_outer (p r s : ℝ) (i m : Fin 6) :
    ∑ o, tripleMidpoint p r s (i,m,o)=PauliReflectedCylinder.midpoint p r (i,m) := by
  simp only [tripleMidpoint,← D_sum,tripleEffect_outer,PauliReflectedCylinder.midpoint]

/-- Both newly appended outer outcomes are summed in the actual kernel. -/
theorem six_outer_marginal (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (u v : HalfHistory) :
    ∑ o, ∑ q, sixKernel p r s hp hp1 hr hr1 hs hs1 (u.1,u.2,o) (v.1,v.2,q)=
      PauliReflectedCylinder.kernel p r hp hp1 hr hr1 u v := by
  simp_rw [six_kernel_trace]
  simp only [← Finset.mul_sum,← Matrix.trace_sum,← Matrix.sum_mul,tripleEffect_outer,← D_sum]
  rw [PauliReflectedCylinder.kernel_trace]

/-- Complex coefficients synthesize the actual midpoint operators. -/
def tripleSynthesis (p r s : ℝ) (F : Triple → ℂ) : Mat :=
  ∑ u, F u • tripleMidpoint p r s u

theorem six_pairing (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (F G : Triple → ℂ) :
    pairing (sixKernel p r s hp hp1 hr hr1 hs hs1) F G=
      (tripleSynthesis p r s G*rho*(tripleSynthesis p r s F)ᴴ).trace := by
  letI := Matrix.toMatrixSeminormedAddCommGroup rho rho_density.1
  letI := Matrix.toMatrixInnerProductSpace rho rho_density.1
  have hk : sixKernel p r s hp hp1 hr hr1 hs hs1=Matrix.gram ℂ (tripleMidpoint p r s) := by
    ext u v
    exact six_kernel_gram p r s hp hp1 hr hr1 hs hs1 u v
  rw [hk]
  exact Matrix.star_dotProduct_gram_mulVec (tripleMidpoint p r s) F G

theorem six_posSemidef (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) : Matrix.PosSemidef (sixKernel p r s hp hp1 hr hr1 hs hs1) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup rho rho_density.1
  letI := Matrix.toMatrixInnerProductSpace rho rho_density.1
  have hk : sixKernel p r s hp hp1 hr hr1 hs hs1=Matrix.gram ℂ (tripleMidpoint p r s) := by
    ext u v
    exact six_kernel_gram p r s hp hp1 hr hr1 hs hs1 u v
  rw [hk]
  exact Matrix.posSemidef_gram ℂ (tripleMidpoint p r s)

/-- Depth zero has one inner outcome; this is an actual finite-index identification. -/
def singletonEquiv : (Fin 1 → Fin 6) ≃ Fin 6 where
  toFun u := u 0
  invFun i := fun _ => i
  left_inv u := by funext j; exact congrArg u (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- Depth one paths run inner-to-outer, matching the accepted ordered pair. -/
def pairIndexEquiv : (Fin 2 → Fin 6) ≃ HalfHistory where
  toFun u := (u 0,u 1)
  invFun u := ![u.1,u.2]
  left_inv u := by funext j; fin_cases j <;> rfl
  right_inv u := by rcases u with ⟨i,o⟩; rfl

def pairHistory (u v : Fin 2 → Fin 6) : History 6 4 := (u 1,u 0,v 0,v 1,())

def baseKernel (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (u v : Fin 1 → Fin 6) : ℂ :=
  (weight (Fin 2) Unit 6 (twoTree p hp hp1) (u 0,v 0,())
    (GibbsMultilevelReflection.joint rho) : ℂ)

def pairKernel (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (u v : Fin 2 → Fin 6) : ℂ :=
  (weight (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) (pairHistory u v)
    (GibbsMultilevelReflection.joint rho) : ℂ)

theorem base_recovery (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (u v : Fin 1 → Fin 6) :
    baseKernel p hp hp1 u v=twoKernel p hp hp1 (singletonEquiv u) (singletonEquiv v) := rfl

theorem base_trace (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (u v : Fin 1 → Fin 6) :
    baseKernel p hp hp1 u v=(1/2:ℂ)*(effect (v 0)*D (p*p) (effect (u 0))).trace :=
  twoKernel_trace p hp hp1 (u 0) (v 0)

theorem base_identity_recovery (u v : Fin 1 → Fin 6) :
    baseKernel 1 (by norm_num) le_rfl u v=PauliInstrumentReconstruction.kernel (u 0) (v 0) :=
  twoKernel_one (u 0) (v 0)

theorem pair_history_recovery (u v : Fin 2 → Fin 6) :
    pairHistory u v=((pairIndexEquiv u).2,(pairIndexEquiv u).1,
      (pairIndexEquiv v).1,(pairIndexEquiv v).2,()) := rfl

theorem pair_recovery (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (u v : Fin 2 → Fin 6) : pairKernel p r hp hp1 hr hr1 u v=
      PauliReflectedCylinder.kernel p r hp hp1 hr hr1 (pairIndexEquiv u) (pairIndexEquiv v) := rfl

/-- The finite-function convention agrees with the literal six-event ordering. -/
def tripleIndexEquiv : (Fin 3 → Fin 6) ≃ Triple where
  toFun u := (u 0,u 1,u 2)
  invFun u := ![u.1,u.2.1,u.2.2]
  left_inv u := by funext j; fin_cases j <;> rfl
  right_inv u := by rcases u with ⟨i,m,o⟩; rfl

theorem six_history_recovery (u v : Fin 3 → Fin 6) :
    sixHistory (tripleIndexEquiv u) (tripleIndexEquiv v)=(u 2,u 1,u 0,v 0,v 1,v 2,()) := rfl

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder
open scoped BigOperators ComplexOrder Kronecker

/-- Forgetting a Pauli outcome still applies a nonselective measurement channel. -/
theorem nonselective (X : Mat) : (∑ o, instrument.branch o X)=D (1/3) X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [instrument_branch,projector,sign,outcomeEquiv,finProdFinEquiv,
      Fin.divNat,Fin.modNat,sigma,pauliX,pauliY,pauliZ,D,rho,
      Matrix.mul_apply,Matrix.trace,Fin.sum_univ_succ,Matrix.one_apply] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

/-- Signed Pauli measurement on any complex matrix is the Jordan multiplication map. -/
theorem weighted_branch_jordan (a : Fin 3) (X : Mat) :
    (∑ o, axisMode a o • instrument.branch o X)=(1/2:ℂ) • (sigma a*X+X*sigma a) := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [axisMode,instrument_branch,projector,sign,outcomeEquiv,finProdFinEquiv,
      Fin.divNat,Fin.modNat,sigma,pauliX,pauliY,pauliZ,
      Matrix.mul_apply,Matrix.vecMul, dotProduct,Fin.sum_univ_succ,Matrix.one_apply] <;>
    ring

/-- The middle intervention is erased as an outcome, not removed as a channel. -/
theorem tripleEffect_middle (r s : ℝ) (i o : Fin 6) :
    ∑ m, tripleEffect r s (i,m,o)=halfEffect (r*s/3) (i,o) := by
  change (∑ m, branchLinear i (DLinear r (instrument.branch m (D s (effect o)))))=_
  rw [← map_sum,← map_sum,nonselective]
  change instrument.branch i (D r (D (1/3) (D s (effect o))))=_
  rw [D_comp,D_comp]
  have he : r*(1/3)*s=r*s/3 := by ring
  rw [he]
  rfl

theorem erased_retention_nonnegative {r s : ℝ} (hr : 0≤r) (hs : 0 ≤ s) : 0≤r*s/3 := by positivity

theorem erased_retention_le_one {r s : ℝ} (hr : 0≤r) (hr1 : r≤1) (_hs : 0 ≤ s) (hs1 : s≤1) :
    r*s/3≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hs1)]

/-- Actual paired middle-label marginal of the six-event tree. -/
theorem six_middle_marginal (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (u v : HalfHistory) :
    ∑ m, ∑ n, sixKernel p r s hp hp1 hr hr1 hs hs1 (u.1,m,u.2) (v.1,n,v.2)=
      PauliReflectedCylinder.kernel p (r*s/3) hp hp1
        (erased_retention_nonnegative hr hs) (erased_retention_le_one hr hr1 hs hs1) u v := by
  simp_rw [six_kernel_trace]
  simp only [← Finset.mul_sum,← Matrix.trace_sum,← Matrix.sum_mul,tripleEffect_middle,← D_sum]
  rw [PauliReflectedCylinder.kernel_trace]

/-- A coefficient on the retained inner/outer labels ignores the middle outcome. -/
def ignoreMiddle (F : HalfHistory → ℂ) (u : Triple) : ℂ := F (u.1,u.2.2)

theorem synthesis_ignoreMiddle (p r s : ℝ) (F : HalfHistory → ℂ) :
    tripleSynthesis p r s (ignoreMiddle F)=synthesis p (r*s/3) F := by
  unfold tripleSynthesis ignoreMiddle PauliReflectedCylinder.synthesis tripleMidpoint PauliReflectedCylinder.midpoint
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum,← D_sum,tripleEffect_middle]

/-- The retained XX observable sees the disturbance of the erased middle event. -/
theorem ignored_XX_synthesis (p r s : ℝ) :
    tripleSynthesis p r s (ignoreMiddle (twoTimeMode 0 0))=((r*s/3:ℝ):ℂ) • (1:Mat) := by
  rw [synthesis_ignoreMiddle,synthesis_XX]

def threeTimeMode (a b c : Fin 3) (u : Triple) : ℂ :=
  axisMode a u.1*axisMode b u.2.1*axisMode c u.2.2

theorem branch_weighted (i : Fin 6) (r : ℝ) (w : Fin 6 → ℂ) (X : Fin 6 → Mat) :
    (∑ o, w o • instrument.branch i (D r (X o)))=
      instrument.branch i (D r (∑ o, w o • X o)) := by
  change (∑ o, w o • ((branchLinear i).comp (DLinear r)) (X o))=
    ((branchLinear i).comp (DLinear r)) (∑ o, w o • X o)
  rw [map_sum]
  simp only [map_smul]

/-- The complete ordered three-label synthesis, without commuting branch maps. -/
theorem synthesis_threeTime (p r s : ℝ) (a b c : Fin 3) :
    tripleSynthesis p r s (threeTimeMode a b c)=
      D p (∑ i, axisMode a i • instrument.branch i
        (D r (∑ m, axisMode b m • instrument.branch m (D s (sigma c))))) := by
  unfold tripleSynthesis threeTimeMode tripleMidpoint tripleEffect
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type,mul_smul,← D_smul,← D_sum,← Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp_rw [branch_weighted]
  change instrument.branch i (D r (∑ m, axisMode b m • instrument.branch m
    (D s (PauliInstrumentReconstruction.synthesis (axisMode c)))))=_
  rw [PauliInstrumentReconstruction.synthesis_axisMode]

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder
open scoped BigOperators ComplexOrder Kronecker

theorem weighted_branch_YY : (∑ o, axisMode 1 o • instrument.branch o (sigma 1))=(1:Mat) := by
  rw [weighted_branch_jordan]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma,pauliY,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,Complex.I_sq]

theorem weighted_branch_X_one : (∑ o, axisMode 0 o • instrument.branch o (1:Mat))=sigma 0 := by
  simp only [branch_one]
  exact PauliInstrumentReconstruction.synthesis_axisMode 0

/-- The middle Y sandwich turns its Y input into a scalar, so r cancels. -/
theorem synthesis_XYY (p r s : ℝ) :
    tripleSynthesis p r s (threeTimeMode 0 1 1)=((p*s:ℝ):ℂ) • sigma 0 := by
  rw [synthesis_threeTime,D_sigma]
  simp only [FiniteInstrument.branch_smul,smul_comm _ (s:ℂ),← Finset.smul_sum,
    weighted_branch_YY,D_smul,D_unital,weighted_branch_X_one,D_sigma]
  simp only [smul_smul,Complex.ofReal_mul]
  congr 1
  ring

/-- Every coordinate is genuinely used, including the imaginary Pauli Y direction. -/
theorem XYY_values : threeTimeMode 0 1 1 (0,2,2)=27 ∧
    threeTimeMode 0 1 1 (1,2,2)= -27 ∧
    threeTimeMode 0 1 1 (0,3,2)= -27 ∧
    threeTimeMode 0 1 1 (0,2,3)= -27 := by
  norm_num [threeTimeMode,axisMode,sign,outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat]

theorem XYY_pairing (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) :
    pairing (sixKernel p r s hp hp1 hr hr1 hs hs1) (threeTimeMode 0 1 1) (threeTimeMode 0 1 1)=
      ((p^2*s^2:ℝ):ℂ) := by
  rw [six_pairing,synthesis_XYY]
  norm_num [sigma,pauliX,rho,Matrix.conjTranspose_smul,Matrix.conjTranspose,
    Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.trace,Fin.sum_univ_two,Matrix.one_apply]
  ring

theorem ignored_XX_pairing (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) :
    pairing (sixKernel p r s hp hp1 hr hr1 hs hs1)
      (ignoreMiddle (twoTimeMode 0 0)) (ignoreMiddle (twoTimeMode 0 0))=((r*s/3:ℝ):ℂ)^2 := by
  rw [six_pairing,ignored_XX_synthesis]
  simp [rho,Matrix.conjTranspose_smul,Matrix.trace_smul,smul_smul]
  ring

/-- Even identity gaps retain the measurement disturbance: erasure differs from deletion. -/
theorem repeated_time_XX_guard :
    pairing (sixKernel 1 1 1 (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl)
      (ignoreMiddle (twoTimeMode 0 0)) (ignoreMiddle (twoTimeMode 0 0))=1/9 ∧
    pairing (PauliReflectedCylinder.kernel 1 1 (by norm_num) le_rfl (by norm_num) le_rfl)
      (twoTimeMode 0 0) (twoTimeMode 0 0)=1 := by
  constructor
  · rw [ignored_XX_pairing]; norm_num
  · rw [twoTime_XX_pairing]; norm_num

/-- The norm belongs to the null quotient of the actual six-event kernel. -/
theorem XYY_norm_sq (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) :
    ‖mk (sixKernel p r s hp hp1 hr hr1 hs hs1) (six_posSemidef p r s hp hp1 hr hr1 hs hs1)
      (threeTimeMode 0 1 1)‖^2=p^2*s^2 := by
  rw [norm_mk_sq,XYY_pairing]
  norm_cast

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open FinitePositiveKernel PauliReflectedCylinder

theorem XYY_coordinate_dependence :
    threeTimeMode 0 1 1 (0,2,2)≠threeTimeMode 0 1 1 (1,2,2) ∧
    threeTimeMode 0 1 1 (0,2,2)≠threeTimeMode 0 1 1 (0,3,2) ∧
    threeTimeMode 0 1 1 (0,2,2)≠threeTimeMode 0 1 1 (0,2,3) := by
  rw [XYY_values.1,XYY_values.2.1,XYY_values.2.2.1,XYY_values.2.2.2]
  norm_num

theorem XYY_norm_positive (p r s : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (hs : 0 ≤ s) (hs1 : s≤1) (hp0 : 0<p) (hs0 : 0<s) :
    0<‖mk (sixKernel p r s hp hp1 hr hr1 hs hs1) (six_posSemidef p r s hp hp1 hr hr1 hs hs1)
      (threeTimeMode 0 1 1)‖^2 := by
  rw [XYY_norm_sq]
  exact mul_pos (sq_pos_of_pos hp0) (sq_pos_of_pos hs0)

/-- Marginalizing actual middle outcomes cannot be replaced by deleting their interventions. -/
theorem repeated_time_deletion_fails :
    pairing (sixKernel 1 1 1 (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl)
      (ignoreMiddle (twoTimeMode 0 0)) (ignoreMiddle (twoTimeMode 0 0))≠
    pairing (PauliReflectedCylinder.kernel 1 1 (by norm_num) le_rfl (by norm_num) le_rfl)
      (twoTimeMode 0 0) (twoTimeMode 0 0) := by
  rw [repeated_time_XX_guard.1,repeated_time_XX_guard.2]
  norm_num

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

/-- A stationary depolarizing retention, with its channel bounds. -/
structure Gap where
  value : ℝ
  nonnegative : 0≤value
  bounded : value≤1

def identityGap : Gap := ⟨1,by norm_num,le_rfl⟩
def squaredGap (p : Gap) : Gap := ⟨p.value*p.value,mul_nonneg p.nonnegative p.nonnegative,by
  nlinarith [p.nonnegative,p.bounded]⟩

/-- Concatenation retains both actual process segments and their outcome histories.
The depth is written m+n so recursion on the first tree is definitional. -/
def appendTree {n m : ℕ} : Tree (Fin 2) Unit 6 n → Tree (Fin 2) Unit 6 m →
    Tree (Fin 2) Unit 6 (m+n)
  | .done,U => U
  | .node D next,U => .node D (fun o => appendTree (next o) U)

def appendHistory {n m : ℕ} : History 6 n → History 6 m → History 6 (m+n) :=
  match n with
  | 0 => fun _ v => v
  | _+1 => fun u v => (u.1,appendHistory u.2 v)

theorem run_append {n m : ℕ} (T : Tree (Fin 2) Unit 6 n) (U : Tree (Fin 2) Unit 6 m)
    (h : History 6 n) (k : History 6 m) (X : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ) :
    run (Fin 2) Unit 6 (appendTree T U) (appendHistory h k) X=
      run (Fin 2) Unit 6 U k (run (Fin 2) Unit 6 T h X) := by
  induction T generalizing X with
  | done => rfl
  | node D next ih => exact ih h.1 h.2 (D.branch (Fin 2) Unit 6 h.1 X)

def snocTree {n : ℕ} : Tree (Fin 2) Unit 6 n → Step (Fin 2) Unit 6 → Tree (Fin 2) Unit 6 (n+1)
  | .done,D => .node D (fun _ => .done)
  | .node D next,E => .node D (fun o => snocTree (next o) E)

def snocHistory {n : ℕ} : History 6 n → Fin 6 → History 6 (n+1) :=
  match n with
  | 0 => fun _ o => (o,())
  | _+1 => fun h o => (h.1,snocHistory h.2 o)

theorem run_snoc {n : ℕ} (T : Tree (Fin 2) Unit 6 n) (D : Step (Fin 2) Unit 6)
    (h : History 6 n) (o : Fin 6) (X : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ) :
    run (Fin 2) Unit 6 (snocTree T D) (snocHistory h o) X=
      D.branch (Fin 2) Unit 6 o (run (Fin 2) Unit 6 T h X) := by
  induction T generalizing X with
  | done => rfl
  | node E next ih => exact ih h.1 h.2 (E.branch (Fin 2) Unit 6 h.1 X)

abbrev Labels (rs : List Gap) := History 6 (rs.length+1)

/-- The positive half runs inner-to-outer; its first evolution is explicit. -/
def positiveTree (p : Gap) : (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => .node (PauliReflectedCylinder.step p.value p.nonnegative p.bounded) (fun _ => .done)
  | r::rs => .node (PauliReflectedCylinder.step p.value p.nonnegative p.bounded)
      (fun _ => positiveTree r rs)

/-- The negative half runs outer-to-inner, starting with the identity evolution. -/
def negativeTree : (rs : List Gap) → Tree (Fin 2) Unit 6 (rs.length+1)
  | [] => positiveTree identityGap []
  | r::rs => snocTree (negativeTree rs) (PauliReflectedCylinder.step r.value r.nonnegative r.bounded)

def negativeHistory : (rs : List Gap) → Labels rs → Labels rs
  | [],h => h
  | _::rs,h => snocHistory (negativeHistory rs h.2) h.1

def reflectedTree (p : Gap) (rs : List Gap) :
    Tree (Fin 2) Unit 6 ((rs.length+1)+(rs.length+1)) :=
  appendTree (negativeTree rs) (positiveTree (squaredGap p) rs)

def reflectedHistory (rs : List Gap) (u v : Labels rs) :
    History 6 ((rs.length+1)+(rs.length+1)) := appendHistory (negativeHistory rs u) v

/-- The finite-depth kernel is the actual chronological weight. -/
def historyKernel (p : Gap) (rs : List Gap) (u v : Labels rs) : ℂ :=
  (weight (Fin 2) Unit 6 (reflectedTree p rs) (reflectedHistory rs u v)
    (GibbsMultilevelReflection.joint rho) : ℂ)

def historyEffect : (rs : List Gap) → Labels rs → Mat
  | [],u => effect u.1
  | r::rs,u => instrument.branch u.1 (D r.value (historyEffect rs u.2))

def historyMidpoint (p : Gap) (rs : List Gap) (u : Labels rs) : Mat := D p.value (historyEffect rs u)

theorem historyEffect_adjoint (rs : List Gap) (u : Labels rs) :
    (historyEffect rs u)ᴴ=historyEffect rs u := by
  induction rs with
  | nil => exact effect_adjoint u.1
  | cons r rs ih => simp only [historyEffect,branch_adjoint,D_adjoint,ih]

theorem negative_run (rs : List Gap) (u : Labels rs) :
    run (Fin 2) Unit 6 (negativeTree rs) (negativeHistory rs u) (GibbsMultilevelReflection.joint rho)=
      GibbsMultilevelReflection.joint ((1/2:ℂ) • historyEffect rs u) := by
  induction rs with
  | nil =>
    rcases u with ⟨o,⟨⟩⟩
    simp only [negativeTree,negativeHistory,positiveTree,run,PauliReflectedCylinder.step_branch,
      identityGap,D_one,branch_rho,historyEffect]
  | cons r rs ih =>
    rw [negativeTree,negativeHistory,run_snoc,ih]
    simp only [PauliReflectedCylinder.step_branch,D_smul,FiniteInstrument.branch_smul,historyEffect]

/-- Backward trace duality keeps the noncommuting branch order. -/
theorem positive_trace (p : Gap) (rs : List Gap) (u : Labels rs) (X : Mat) :
    (run (Fin 2) Unit 6 (positiveTree p rs) u (GibbsMultilevelReflection.joint X)).trace=
      (D p.value (historyEffect rs u)*X).trace := by
  induction rs generalizing p X with
  | nil =>
    rcases u with ⟨o,⟨⟩⟩
    simp only [positiveTree,run,PauliReflectedCylinder.step_branch,GibbsMultilevelReflection.joint_trace,
      branch_trace,D_trace_dual,historyEffect]
  | cons r rs ih =>
    change (run (Fin 2) Unit 6 (positiveTree r rs) u.2
      ((PauliReflectedCylinder.step p.value p.nonnegative p.bounded).branch (Fin 2) Unit 6 u.1
        (GibbsMultilevelReflection.joint X))).trace=_
    rw [PauliReflectedCylinder.step_branch,ih,branch_trace_dual,D_trace_dual]
    rfl

theorem history_actual_trace (p : Gap) (rs : List Gap) (u v : Labels rs) :
    (run (Fin 2) Unit 6 (reflectedTree p rs) (reflectedHistory rs u v)
      (GibbsMultilevelReflection.joint rho)).trace=
      (1/2:ℂ)*(historyEffect rs v*D (p.value*p.value) (historyEffect rs u)).trace := by
  rw [reflectedTree,reflectedHistory,run_append,negative_run,positive_trace]
  rw [Matrix.mul_smul,Matrix.trace_smul,← D_trace_dual]
  rfl

theorem history_kernel_trace (p : Gap) (rs : List Gap) (u v : Labels rs) :
    historyKernel p rs u v=(1/2:ℂ)*(historyEffect rs v*D (p.value*p.value) (historyEffect rs u)).trace := by
  unfold historyKernel weight
  rw [history_actual_trace]
  have h := hermitian_product_real (historyEffect rs v) (D (p.value*p.value) (historyEffect rs u))
    (historyEffect_adjoint rs v) (by rw [D_adjoint,historyEffect_adjoint])
  simp only [Complex.mul_re]
  norm_num
  rw [h]

theorem history_kernel_gram (p : Gap) (rs : List Gap) (u v : Labels rs) :
    historyKernel p rs u v=(historyMidpoint p rs v*rho*(historyMidpoint p rs u)ᴴ).trace := by
  rw [history_kernel_trace,central_split]
  simp only [historyMidpoint,D_adjoint,historyEffect_adjoint,rho,mul_smul_comm,mul_one,
    smul_mul_assoc,Matrix.trace_smul,smul_eq_mul]

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder GibbsObservable
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

def historySynthesis (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) : Mat :=
  ∑ u, F u • historyMidpoint p rs u

def historySynthesisLinear (p : Gap) (rs : List Gap) : (Labels rs → ℂ) →ₗ[ℂ] Mat where
  toFun := historySynthesis p rs
  map_add' F G := by simp [historySynthesis,add_smul,Finset.sum_add_distrib]
  map_smul' c F := by simp [historySynthesis,Finset.smul_sum,smul_smul]

theorem history_pairing (p : Gap) (rs : List Gap) (F G : Labels rs → ℂ) :
    pairing (historyKernel p rs) F G=(historySynthesis p rs G*rho*(historySynthesis p rs F)ᴴ).trace := by
  letI := Matrix.toMatrixSeminormedAddCommGroup rho rho_density.1
  letI := Matrix.toMatrixInnerProductSpace rho rho_density.1
  have hk : historyKernel p rs=Matrix.gram ℂ (historyMidpoint p rs) := by
    ext u v; exact history_kernel_gram p rs u v
  rw [hk]
  exact Matrix.star_dotProduct_gram_mulVec (historyMidpoint p rs) F G

theorem history_posSemidef (p : Gap) (rs : List Gap) : Matrix.PosSemidef (historyKernel p rs) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup rho rho_density.1
  letI := Matrix.toMatrixInnerProductSpace rho rho_density.1
  have hk : historyKernel p rs=Matrix.gram ℂ (historyMidpoint p rs) := by
    ext u v; exact history_kernel_gram p rs u v
  rw [hk]
  exact Matrix.posSemidef_gram ℂ (historyMidpoint p rs)

abbrev HistorySpace (p : Gap) (rs : List Gap) := Space (historyKernel p rs) (history_posSemidef p rs)

theorem history_null_iff (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    mk (historyKernel p rs) (history_posSemidef p rs) F=0 ↔ historySynthesis p rs F=0 := by
  rw [mk_eq_zero_iff,history_pairing]
  constructor
  · exact GibbsObservable.trace_weighted_eq_zero rho_posDef _
  · intro h; simp [h]

def historyCoordinates (p : Gap) (rs : List Gap) : HistorySpace p rs →ₗ[ℂ] Mat :=
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
  simp [hz]

/-- Sum all outcomes outward of a fixed inner event. -/
theorem historyEffect_inner_sum (rs : List Gap) (i : Fin 6) :
    (∑ h : History 6 rs.length, historyEffect rs (i,h))=effect i := by
  induction rs generalizing i with
  | nil => simp [historyEffect,History]
  | cons r rs ih =>
    change (∑ h : Fin 6 × History 6 rs.length, instrument.branch i (D r.value (historyEffect rs h)))=_
    rw [Fintype.sum_prod_type]
    change (∑ o, ∑ h, branchLinear i (DLinear r.value (historyEffect rs (o,h))))=_
    simp only [← map_sum,ih,effect_sum]
    change instrument.branch i (D r.value 1)=effect i
    rw [D_unital,branch_one]

theorem historySynthesis_inner (p : Gap) (rs : List Gap) (F : Fin 6 → ℂ) :
    historySynthesis p rs (fun u => F u.1)=D p.value (PauliInstrumentReconstruction.synthesis F) := by
  change (∑ u : Fin 6 × History 6 rs.length, F u.1 • D p.value (historyEffect rs u))=_
  rw [Fintype.sum_prod_type]
  simp only [← Finset.smul_sum,← D_sum,historyEffect_inner_sum,← D_smul]
  rfl

theorem historySynthesis_constant (p : Gap) (rs : List Gap) :
    historySynthesis p rs (fun _ => 1)=1 := by
  have h := historySynthesis_inner p rs (fun _ => (1:ℂ))
  rw [PauliInstrumentReconstruction.synthesis_constant,D_unital] at h
  exact h


/-- The inverse uses only positive central retention, never a side retention. -/
def historyCoefficients (p : Gap) (X : Mat) (rs : List Gap) (u : Labels rs) : ℂ :=
  PauliInstrumentReconstruction.coefficients (inverseD p.value X) u.1

theorem historySynthesis_coefficients (p : Gap) (hp : 0<p.value) (rs : List Gap) (X : Mat) :
    historySynthesis p rs (historyCoefficients p X rs)=X := by
  change historySynthesis p rs (fun u => PauliInstrumentReconstruction.coefficients (inverseD p.value X) u.1)=X
  rw [historySynthesis_inner,PauliInstrumentReconstruction.synthesis_coefficients,D_inverse hp]

def historyCoordinateEquiv (p : Gap) (hp : 0<p.value) (rs : List Gap) : HistorySpace p rs ≃ₗ[ℂ] Mat :=
  LinearEquiv.ofBijective (historyCoordinates p rs) ⟨historyCoordinates_injective p rs,by
    intro X
    exact ⟨mk _ _ (historyCoefficients p X rs),by rw [historyCoordinates_mk,historySynthesis_coefficients p hp]⟩⟩

theorem history_finrank (p : Gap) (hp : 0<p.value) (rs : List Gap) :
    Module.finrank ℂ (HistorySpace p rs)=4 := by
  rw [(historyCoordinateEquiv p hp rs).finrank_eq]
  simpa using Module.finrank_matrix ℂ ℂ (Fin 2) (Fin 2)

/-- The actual central-reset synthesis is a scalar identity, even with zero side gaps. -/
def historyMean (rs : List Gap) (F : Labels rs → ℂ) : ℂ :=
  ∑ u, F u*((historyEffect rs u).trace/2)

theorem historySynthesis_reset (p : Gap) (hp : p.value=0) (rs : List Gap) (F : Labels rs → ℂ) :
    historySynthesis p rs F=historyMean rs F • (1:Mat) := by
  simp only [historySynthesis,historyMidpoint,hp,D_zero,rho,smul_smul,← Finset.sum_smul,historyMean]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  ring

theorem historyMean_constant (rs : List Gap) : historyMean rs (fun _ => 1)=1 := by
  have h := historySynthesis_constant (⟨0,le_rfl,by norm_num⟩ : Gap) rs
  rw [historySynthesis_reset _ rfl] at h
  have he := congrArg (fun X : Mat => X 0 0) h
  simpa using he

theorem history_reset_null (p : Gap) (hp : p.value=0) (rs : List Gap) (F : Labels rs → ℂ) :
    mk (historyKernel p rs) (history_posSemidef p rs) F=0 ↔ historyMean rs F=0 := by
  rw [history_null_iff,historySynthesis_reset p hp]
  constructor
  · intro h; have he := congrArg (fun X : Mat => X 0 0) h; simpa using he
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

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder GibbsObservable
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

/-- Literal outer-coordinate splitting; all earlier labels keep their order. -/
def outerEquiv (q : Gap) : (rs : List Gap) → Labels (rs++[q]) ≃ Labels rs × Fin 6
  | [] => {
      toFun := fun h => ((h.1,()),h.2.1)
      invFun := fun h => (h.1.1,h.2,())
      left_inv := by rintro ⟨i,o,⟨⟩⟩; rfl
      right_inv := by rintro ⟨⟨i,⟨⟩⟩,o⟩; rfl }
  | _::rs => {
      toFun := fun h => ((h.1,(outerEquiv q rs h.2).1),(outerEquiv q rs h.2).2)
      invFun := fun h => (h.1.1,(outerEquiv q rs).symm (h.1.2,h.2))
      left_inv := by intro h; simp
      right_inv := by intro h; simp }

def outerPull (q : Gap) (rs : List Gap) (F : Labels rs → ℂ) : Labels (rs++[q]) → ℂ :=
  fun h => F (outerEquiv q rs h).1

theorem historyEffect_outer (q : Gap) (rs : List Gap) (h : Labels rs) :
    (∑ o, historyEffect (rs++[q]) ((outerEquiv q rs).symm (h,o)))=historyEffect rs h := by
  induction rs with
  | nil => exact halfEffect_outer q.value h.1
  | cons r rs ih =>
    change (∑ o, branchLinear h.1 (DLinear r.value
      (historyEffect (rs++[q]) ((outerEquiv q rs).symm (h.2,o)))) )=_
    rw [← map_sum,← map_sum,ih]
    rfl

theorem historyMidpoint_outer (p q : Gap) (rs : List Gap) (h : Labels rs) :
    (∑ o, historyMidpoint p (rs++[q]) ((outerEquiv q rs).symm (h,o)))=historyMidpoint p rs h := by
  simp only [historyMidpoint,← D_sum,historyEffect_outer]

/-- The actual larger tree has the old kernel as its paired outer marginal. -/
theorem history_kernel_outer (p q : Gap) (rs : List Gap) (u v : Labels rs) :
    (∑ o, ∑ t, historyKernel p (rs++[q]) ((outerEquiv q rs).symm (u,o))
      ((outerEquiv q rs).symm (v,t)))=historyKernel p rs u v := by
  simp_rw [history_kernel_trace]
  simp only [← Finset.mul_sum,← Matrix.trace_sum,← Matrix.sum_mul,historyEffect_outer,← D_sum]

/-- Pullback means literally ignoring the appended coordinate, with no inverse reconstruction. -/
theorem historySynthesis_outerPull (p q : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    historySynthesis p (rs++[q]) (outerPull q rs F)=historySynthesis p rs F := by
  unfold historySynthesis outerPull
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

theorem outerMap_surjective_positive (p q : Gap) (hp : 0<p.value) (rs : List Gap) :
    Function.Surjective (outerMap p q rs) := by
  intro z
  refine ⟨(historyCoordinateEquiv p hp rs).symm (historyCoordinates p (rs++[q]) z),?_⟩
  apply historyCoordinates_injective p (rs++[q])
  rw [outerMap_coordinates]
  exact (historyCoordinateEquiv p hp rs).apply_symm_apply _

theorem outerMap_surjective_reset (p q : Gap) (hp : p.value=0) (rs : List Gap) :
    Function.Surjective (outerMap p q rs) := by
  intro z
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  refine ⟨historyMean (rs++[q]) F • mk _ _ (fun _ => 1),?_⟩
  apply historyCoordinates_injective p (rs++[q])
  rw [outerMap_coordinates,map_smul,historyCoordinates_mk,historyCoordinates_mk,
    historySynthesis_constant,historySynthesis_reset p hp]

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder GibbsObservable
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

/-- Appended gaps are ordered by their actual successive outer extensions. -/
def extendSchedule (rs : List Gap) : List Gap → List Gap
  | [] => rs
  | q::qs => extendSchedule (rs++[q]) qs

theorem extendSchedule_eq_append (rs qs : List Gap) : extendSchedule rs qs=rs++qs := by
  induction qs generalizing rs with
  | nil => simp [extendSchedule]
  | cons q qs ih => simpa [extendSchedule,List.append_assoc] using ih (rs++[q])

def extendPull (rs : List Gap) : (qs : List Gap) → (Labels rs → ℂ) → Labels (extendSchedule rs qs) → ℂ
  | [],F => F
  | q::qs,F => extendPull (rs++[q]) qs (outerPull q rs F)

def extensionMap (p : Gap) (rs : List Gap) : (qs : List Gap) →
    HistorySpace p rs →ₗᵢ[ℂ] HistorySpace p (extendSchedule rs qs)
  | [] => LinearIsometry.id (R := ℂ) (E := HistorySpace p rs)
  | q::qs => (extensionMap p (rs++[q]) qs).comp (outerMap p q rs)

theorem extensionMap_mk (p : Gap) (rs qs : List Gap) (F : Labels rs → ℂ) :
    extensionMap p rs qs (mk _ _ F)=mk _ _ (extendPull rs qs F) := by
  induction qs generalizing rs with
  | nil => rfl
  | cons q qs ih =>
    change extensionMap p (rs++[q]) qs (outerMap p q rs (mk _ _ F))=_
    rw [outerMap_mk,ih]
    rfl

theorem extensionMap_coordinates (p : Gap) (rs qs : List Gap) (z : HistorySpace p rs) :
    historyCoordinates p (extendSchedule rs qs) (extensionMap p rs qs z)=historyCoordinates p rs z := by
  induction qs generalizing rs with
  | nil => rfl
  | cons q qs ih =>
    change historyCoordinates p (extendSchedule (rs++[q]) qs)
      (extensionMap p (rs++[q]) qs (outerMap p q rs z))=_
    rw [ih,outerMap_coordinates]

theorem extensionMap_identity (p : Gap) (rs : List Gap) :
    extensionMap p rs []=LinearIsometry.id (R := ℂ) (E := HistorySpace p rs) := rfl

theorem extendSchedule_composition (rs as bs : List Gap) :
    extendSchedule rs (as++bs)=extendSchedule (extendSchedule rs as) bs := by
  simp only [extendSchedule_eq_append,List.append_assoc]

/-- The necessary dependent transport only changes equal schedule indices. -/
def scheduleTransport (p : Gap) {rs ss : List Gap} (h : rs=ss) : HistorySpace p rs →ₗᵢ[ℂ] HistorySpace p ss := by
  subst ss
  exact LinearIsometry.id (R := ℂ) (E := HistorySpace p rs)

theorem scheduleTransport_coordinates (p : Gap) {rs ss : List Gap} (h : rs=ss) (z : HistorySpace p rs) :
    historyCoordinates p ss (scheduleTransport p h z)=historyCoordinates p rs z := by
  subst ss
  rfl

/-- Ordered composition, with the target schedule transport displayed. -/
theorem extensionMap_composition (p : Gap) (rs as bs : List Gap) (z : HistorySpace p rs) :
    scheduleTransport p (extendSchedule_composition rs as bs) (extensionMap p rs (as++bs) z)=
      extensionMap p (extendSchedule rs as) bs (extensionMap p rs as z) := by
  apply historyCoordinates_injective p (extendSchedule (extendSchedule rs as) bs)
  rw [scheduleTransport_coordinates,extensionMap_coordinates,extensionMap_coordinates,extensionMap_coordinates]

theorem outerMap_surjective (p q : Gap) (rs : List Gap) : Function.Surjective (outerMap p q rs) := by
  rcases lt_or_eq_of_le p.nonnegative with hp|hp
  · exact outerMap_surjective_positive p q hp rs
  · exact outerMap_surjective_reset p q hp.symm rs

theorem extensionMap_surjective (p : Gap) (rs qs : List Gap) : Function.Surjective (extensionMap p rs qs) := by
  induction qs generalizing rs with
  | nil => exact Function.surjective_id
  | cons q qs ih => exact (ih (rs++[q])).comp (outerMap_surjective p q rs)

/-- The chronological list is the reversed negative half followed by the positive half. -/
def historyList : {n : ℕ} → History 6 n → List (Fin 6)
  | 0,_ => []
  | _+1,h => h.1::historyList h.2

theorem historyList_append {n m : ℕ} (u : History 6 n) (v : History 6 m) :
    historyList (appendHistory u v)=historyList u++historyList v := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons u.1) (ih u.2)

theorem historyList_snoc {n : ℕ} (u : History 6 n) (o : Fin 6) :
    historyList (snocHistory u o)=historyList u++[o] := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons u.1) (ih u.2)

theorem negativeHistory_list (rs : List Gap) (u : Labels rs) :
    historyList (negativeHistory rs u)=(historyList u).reverse := by
  induction rs with
  | nil => rcases u with ⟨i,⟨⟩⟩; rfl
  | cons r rs ih =>
    rw [negativeHistory,historyList_snoc,ih]
    exact List.reverse_cons.symm

theorem reflectedHistory_list (rs : List Gap) (u v : Labels rs) :
    historyList (reflectedHistory rs u v)=(historyList u).reverse++historyList v := by
  rw [reflectedHistory,historyList_append,negativeHistory_list]

theorem reflectedTree_zero (p : Gap) : reflectedTree p []=twoTree p.value p.nonnegative p.bounded := rfl

theorem reflectedTree_one (p r : Gap) :
    reflectedTree p [r]=fourTree p.value r.value p.nonnegative p.bounded r.nonnegative r.bounded := rfl

theorem reflectedTree_two (p r s : Gap) :
    reflectedTree p [r,s]=sixTree p.value r.value s.value p.nonnegative p.bounded
      r.nonnegative r.bounded s.nonnegative s.bounded := rfl

theorem history_kernel_zero (p : Gap) (u v : Labels []) :
    historyKernel p [] u v=twoKernel p.value p.nonnegative p.bounded u.1 v.1 := by
  rw [history_kernel_trace,twoKernel_trace]
  rfl

theorem history_kernel_one (p r : Gap) (u v : Labels [r]) :
    historyKernel p [r] u v=PauliReflectedCylinder.kernel p.value r.value
      p.nonnegative p.bounded r.nonnegative r.bounded (u.1,u.2.1) (v.1,v.2.1) := by
  rw [history_kernel_trace,PauliReflectedCylinder.kernel_trace]
  rfl

theorem history_kernel_two (p r s : Gap) (u v : Labels [r,s]) :
    historyKernel p [r,s] u v=sixKernel p.value r.value s.value p.nonnegative p.bounded
      r.nonnegative r.bounded s.nonnegative s.bounded (u.1,u.2.1,u.2.2.1) (v.1,v.2.1,v.2.2.1) := by
  rw [history_kernel_trace,six_kernel_trace]
  rfl

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder GibbsObservable
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

def historyEmbeddingLinear (p : Gap) (rs : List Gap) : HistorySpace p rs →ₗ[ℂ] ObservableSpace :=
  (GibbsObservable.observableLinear rho_density.1).comp (historyCoordinates p rs)

theorem historyEmbeddingLinear_mk (p : Gap) (rs : List Gap) (F : Labels rs → ℂ) :
    historyEmbeddingLinear p rs (mk _ _ F)=GibbsObservable.observable rho_density.1 (historySynthesis p rs F) := by
  change GibbsObservable.observable rho_density.1 (historyCoordinates p rs (mk _ _ F))=_
  rw [historyCoordinates_mk]

def historyEmbedding (p : Gap) (rs : List Gap) : HistorySpace p rs →ₗᵢ[ℂ] ObservableSpace :=
  (historyEmbeddingLinear p rs).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [historyEmbeddingLinear_mk,historyEmbeddingLinear_mk,GibbsObservable.inner_observable,
      inner_mk,history_pairing])

def historyObservableEquiv (p : Gap) (hp : 0<p.value) (rs : List Gap) :
    HistorySpace p rs ≃ₗᵢ[ℂ] ObservableSpace :=
  LinearIsometryEquiv.ofSurjective (historyEmbedding p rs) (by
    intro z
    obtain ⟨X,rfl⟩ := GibbsObservable.observable_surjective rho_density.1 z
    refine ⟨mk _ _ (historyCoefficients p X rs),?_⟩
    change historyEmbeddingLinear p rs (mk _ _ (historyCoefficients p X rs))=_
    rw [historyEmbeddingLinear_mk,historySynthesis_coefficients p hp])

theorem outerMap_observable (p q : Gap) (rs : List Gap) (z : HistorySpace p rs) :
    historyEmbedding p (rs++[q]) (outerMap p q rs z)=historyEmbedding p rs z := by
  change GibbsObservable.observable rho_density.1 (historyCoordinates p (rs++[q]) (outerMap p q rs z))=_
  rw [outerMap_coordinates]
  rfl

/-- Real-score backward effects admit a full complex trace identity on arbitrary matrix inputs.
This follows directly from nodeEffect_trace; it does not identify a real part with a complex pairing. -/
theorem effect_complex_trace {n : ℕ} (T : Tree (Fin 2) Unit 6 n) (f : History 6 n → ℝ)
    (X : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ) :
    (FiniteAdaptiveProcessRobustness.effect T f*X).trace=
      ∑ h, (f h:ℂ)*(run (Fin 2) Unit 6 T h X).trace := by
  induction T generalizing X with
  | done => simp [FiniteAdaptiveProcessRobustness.effect,History,run,Matrix.trace_smul]
  | node E next ih =>
    rw [FiniteAdaptiveProcessRobustness.effect,FiniteAdaptiveProcessRobustness.nodeEffect_trace]
    simp_rw [ih]
    change (∑ a,∑ h, (f (a,h):ℂ)*(run (Fin 2) Unit 6 (next a) h (E.branch (Fin 2) Unit 6 a X)).trace)=
      ∑ h : Fin 6 × History 6 _, (f h:ℂ)*(run (Fin 2) Unit 6 (.node E next) h X).trace
    rw [Fintype.sum_prod_type]
    rfl

/-- The singleton real indicator uses the existing backward-effect API. -/
def indicatorScore {n : ℕ} (u : History 6 n) : History 6 n → ℝ :=
  by classical exact fun h => if h=u then 1 else 0

theorem joint_surjective : Function.Surjective (GibbsMultilevelReflection.joint (d := 2)) := by
  intro X
  refine ⟨fun i j => X (i,()) (j,()),?_⟩
  ext ⟨i,⟨⟩⟩ ⟨j,⟨⟩⟩
  simp [GibbsMultilevelReflection.joint]

/-- First retention is supplied explicitly: a split positive half uses p, not p squared. -/
theorem positive_indicator_effect (p : Gap) (rs : List Gap) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (positiveTree p rs) (indicatorScore u)=
      GibbsMultilevelReflection.joint (D p.value (historyEffect rs u)) := by
  classical
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  obtain ⟨Y,rfl⟩ := joint_surjective X
  rw [effect_complex_trace]
  simp only [indicatorScore]
  simp only [apply_ite,ite_mul,Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [positive_trace]
  rw [GibbsMultilevelReflection.joint,GibbsMultilevelReflection.joint,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.trace_kronecker]
  simp [Matrix.trace]

theorem split_indicator_effect (p : Gap) (rs : List Gap) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (positiveTree p rs) (indicatorScore u)=
      GibbsMultilevelReflection.joint (historyMidpoint p rs u) := positive_indicator_effect p rs u

/-- The actual unsplit suffix has the distinct central full-step effect. -/
theorem unsplit_indicator_effect (p : Gap) (rs : List Gap) (u : Labels rs) :
    FiniteAdaptiveProcessRobustness.effect (positiveTree (squaredGap p) rs) (indicatorScore u)=
      GibbsMultilevelReflection.joint (D (p.value*p.value) (historyEffect rs u)) :=
  positive_indicator_effect (squaredGap p) rs u

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency

namespace SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction PauliReflectedCylinder GibbsObservable
open scoped BigOperators ComplexOrder Kronecker InnerProductSpace

/-- Multiple outer extensions still use the literal coefficient pullback. -/
theorem historySynthesis_extendPull (p : Gap) (rs qs : List Gap) (F : Labels rs → ℂ) :
    historySynthesis p (extendSchedule rs qs) (extendPull rs qs F)=historySynthesis p rs F := by
  have h := extensionMap_coordinates p rs qs (mk _ _ F)
  rw [extensionMap_mk,historyCoordinates_mk,historyCoordinates_mk] at h
  exact h

theorem history_pairing_extendPull (p : Gap) (rs qs : List Gap) (F G : Labels rs → ℂ) :
    pairing (historyKernel p (extendSchedule rs qs)) (extendPull rs qs F) (extendPull rs qs G)=
      pairing (historyKernel p rs) F G := by
  rw [history_pairing,history_pairing,historySynthesis_extendPull,historySynthesis_extendPull]

theorem extendPull_identity (rs : List Gap) (F : Labels rs → ℂ) : extendPull rs [] F=F := rfl

/-- Identity gaps model repeated intervention times without deleting the measurements. -/
theorem general_repeated_time_XX_guard :
    pairing (historyKernel identityGap [identityGap,identityGap])
      (fun h => twoTimeMode 0 0 (h.1,h.2.2.1))
      (fun h => twoTimeMode 0 0 (h.1,h.2.2.1))=1/9 := by
  let e : Labels [identityGap,identityGap] ≃ Triple := {
    toFun := fun h => (h.1,h.2.1,h.2.2.1)
    invFun := fun h => (h.1,h.2.1,h.2.2,())
    left_inv := by rintro ⟨a,b,c,⟨⟩⟩; rfl
    right_inv := by rintro ⟨a,b,c⟩; rfl }
  have hk : historyKernel identityGap [identityGap,identityGap]=
      fun u v => sixKernel 1 1 1 (by norm_num) le_rfl (by norm_num) le_rfl
        (by norm_num) le_rfl (e u) (e v) := by
    funext u v
    exact history_kernel_two identityGap identityGap identityGap u v
  rw [hk]
  unfold pairing dotProduct Matrix.mulVec
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  simp only [dotProduct]
  simp_rw [← e.symm.sum_comp]
  change pairing (sixKernel 1 1 1 (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num) le_rfl)
    (ignoreMiddle (twoTimeMode 0 0)) (ignoreMiddle (twoTimeMode 0 0))=1/9
  exact repeated_time_XX_guard.1

end SKEFTHawking.QuantumNetwork.PauliHistoryConsistency
