import SKEFTHawking.FinitePauliInstrumentReconstruction
import SKEFTHawking.FiniteGibbsReset

/-! Four actual stationary Pauli interventions with symmetric depolarizing gaps.
The kernel is defined from the depth-four process before its midpoint factorization. -/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.PauliReflectedCylinder
open Matrix FiniteInterventionProcess FinitePositiveKernel
open PauliInstrumentReconstruction GibbsObservable
open scoped BigOperators ComplexOrder Kronecker

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev HalfHistory := Fin 6 × Fin 6

def uniformWeights : Fin 2 → ℝ := fun _ => 1/2

theorem uniform_nonnegative (i : Fin 2) : 0≤uniformWeights i := by norm_num [uniformWeights]
theorem uniform_normalized : ∑ i, uniformWeights i=1 := by norm_num [uniformWeights,Fin.sum_univ_two]
theorem uniform_density : DiagonalLindblad.density uniformWeights=rho := by
  ext i j
  by_cases h : i=j <;> simp [DiagonalLindblad.density,rho,uniformWeights,h]

/-- Explicit common state and observable action of the actual uniform reset channel. -/
def D (q : ℝ) (X : Mat) : Mat := (q:ℂ) • X+(1-(q:ℂ)) • (X.trace • rho)

def channel (q : ℝ) := GibbsReset.timeKraus uniformWeights q

theorem channel_normalized {q : ℝ} (hq : 0≤q) (hq1 : q≤1) : IsKrausChannel (channel q) :=
  GibbsReset.time_normalized uniformWeights uniform_nonnegative uniform_normalized q hq hq1

theorem channel_state {q : ℝ} (hq : 0≤q) (hq1 : q≤1) (X : Mat) : krausMap (channel q) X=D q X := by
  rw [channel,GibbsReset.time_state uniformWeights uniform_nonnegative q hq hq1,uniform_density]
  rfl

theorem channel_observable {q : ℝ} (hq : 0≤q) (hq1 : q≤1) (X : Mat) :
    Channel.heisenberg (channel q) X=D q X := by
  rw [channel,GibbsReset.time_observable uniformWeights uniform_nonnegative q hq hq1,uniform_density]
  simp only [D,rho,smul_mul_assoc,one_mul,Matrix.trace_smul,smul_smul]
  congr 1
  congr 1
  ring

theorem D_trace (q : ℝ) (X : Mat) : (D q X).trace=X.trace := by
  simp only [D,Matrix.trace_add,Matrix.trace_smul,rho_density.2,smul_eq_mul,mul_one]
  ring

theorem D_smul (q : ℝ) (c : ℂ) (X : Mat) : D q (c • X)=c • D q X := by
  simp only [D,Matrix.trace_smul,smul_add,smul_smul,smul_eq_mul]
  module

theorem D_add (q : ℝ) (X Y : Mat) : D q (X+Y)=D q X+D q Y := by
  simp only [D,Matrix.trace_add,smul_add,add_smul]
  module

theorem D_one (X : Mat) : D 1 X=X := by simp [D]
theorem D_zero (X : Mat) : D 0 X=X.trace • rho := by simp [D]
theorem D_zero_matrix (q : ℝ) : D q 0=0 := by simp [D]

theorem D_stationary (q : ℝ) : D q rho=rho := by
  simp only [D,rho_density.2,one_smul]
  module

theorem D_unital (q : ℝ) : D q 1=1 := by
  simp [D,rho,Matrix.trace,smul_smul]
  module

theorem rho_adjoint : rhoᴴ=rho := by simp [rho]

theorem D_adjoint (q : ℝ) (X : Mat) : (D q X)ᴴ=D q Xᴴ := by
  simp [D,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,rho_adjoint,Matrix.trace_conjTranspose]

theorem D_comp (p q : ℝ) (X : Mat) : D p (D q X)=D (p*q) X := by
  rw [D,D_trace]
  simp only [D,smul_add,smul_smul,Complex.ofReal_mul]
  module

theorem D_trace_dual (q : ℝ) (X Y : Mat) : (Y*D q X).trace=(D q Y*X).trace := by
  simp only [D,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,Matrix.trace_add,
    Matrix.trace_smul,rho,one_mul,mul_one,smul_smul,smul_eq_mul]
  ring

theorem branch_adjoint (o : Fin 6) (X : Mat) : (instrument.branch o X)ᴴ=instrument.branch o Xᴴ := by
  simp only [instrument_branch,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,projector_adjoint]
  norm_num
  simp only [mul_assoc]

theorem branch_rho (o : Fin 6) : instrument.branch o rho=(1/2:ℂ) • effect o := by
  simp [instrument_branch,rho,effect,projector_square,smul_smul]
  module

theorem branch_trace (o : Fin 6) (X : Mat) : (instrument.branch o X).trace=(effect o*X).trace := by
  rw [instrument_branch,Matrix.trace_smul,Matrix.trace_mul_cycle,projector_square]
  simp [effect,Matrix.trace_smul]

theorem branch_trace_dual (o : Fin 6) (X Y : Mat) :
    (Y*instrument.branch o X).trace=(instrument.branch o Y*X).trace := by
  simp only [instrument_branch,mul_smul_comm,smul_mul_assoc,Matrix.trace_smul]
  congr 1
  calc
    (Y*(projector o*X*projector o)).trace=((Y*projector o)*X*projector o).trace := by simp only [mul_assoc]
    _ = (projector o*(Y*projector o)*X).trace := Matrix.trace_mul_cycle _ _ _
    _ = (projector o*Y*projector o*X).trace := by simp only [mul_assoc]

/-- Evolution precedes this same actual six-outcome Pauli instrument. -/
def step (q : ℝ) (hq : 0≤q) (hq1 : q≤1) : Step (Fin 2) Unit 6 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (channel q k)
  normalized := GibbsMultilevelReflection.joint_normalized _ (channel_normalized hq hq1)
  instrument := instrument

theorem step_branch (q : ℝ) (hq : 0≤q) (hq1 : q≤1) (o : Fin 6) (X : Mat) :
    (step q hq hq1).branch (Fin 2) Unit 6 o (GibbsMultilevelReflection.joint X)=
      GibbsMultilevelReflection.joint (instrument.branch o (D q X)) := by
  change (instrument.lift Unit).branch o
    (krausMap (fun k => GibbsMultilevelReflection.joint (channel q k)) (GibbsMultilevelReflection.joint X))=_
  rw [GibbsMultilevelReflection.joint_kraus,channel_state hq hq1]
  exact GibbsMultilevelReflection.joint_kraus _ _

/-- Half histories are (inner,outer), while events occur outer,inner,inner,outer. -/
def fourTree (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1) : Tree (Fin 2) Unit 6 4 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step r hr hr1) (fun _ =>
      .node (step (p*p) (mul_nonneg hp hp) (by nlinarith)) (fun _ =>
        .node (step r hr hr1) (fun _ => .done))))

/-- Actual chronological weight; no Gram expression is used in this definition. -/
def kernel (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1) (u v : HalfHistory) : ℂ :=
  (weight (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
    (GibbsMultilevelReflection.joint rho) : ℂ)

/-- Ordered Lüders half-history effect, followed by half of the central evolution. -/
def halfEffect (r : ℝ) (u : HalfHistory) : Mat := instrument.branch u.1 (D r (effect u.2))
def midpoint (p r : ℝ) (u : HalfHistory) : Mat := D p (halfEffect r u)


theorem effect_adjoint (o : Fin 6) : (effect o)ᴴ=effect o := by
  simp [effect,Matrix.conjTranspose_smul,projector_adjoint]

theorem halfEffect_adjoint (r : ℝ) (u : HalfHistory) : (halfEffect r u)ᴴ=halfEffect r u := by
  rw [halfEffect,branch_adjoint,D_adjoint,effect_adjoint]

theorem midpoint_adjoint (p r : ℝ) (u : HalfHistory) : (midpoint p r u)ᴴ=midpoint p r u := by
  rw [midpoint,D_adjoint,halfEffect_adjoint]

/-- Actual unnormalized branch state after the four chronological events. -/
theorem actual_run (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (u v : HalfHistory) :
    run (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rho)=
    GibbsMultilevelReflection.joint ((1/2:ℂ) • instrument.branch v.2
      (D r (instrument.branch v.1 (D (p*p) (halfEffect r u))))) := by
  change (step r hr hr1).branch (Fin 2) Unit 6 v.2
    ((step (p*p) (mul_nonneg hp hp) (by nlinarith)).branch (Fin 2) Unit 6 v.1
      ((step r hr hr1).branch (Fin 2) Unit 6 u.1
        ((step 1 (by norm_num) le_rfl).branch (Fin 2) Unit 6 u.2 (GibbsMultilevelReflection.joint rho))))=_
  simp only [step_branch,D_one,branch_rho,D_smul,FiniteInstrument.branch_smul,halfEffect]

theorem actual_trace (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (u v : HalfHistory) :
    (run (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rho)).trace=
      (1/2:ℂ)*(halfEffect r v*D (p*p) (halfEffect r u)).trace := by
  rw [actual_run,GibbsMultilevelReflection.joint_trace,Matrix.trace_smul,branch_trace,
    D_trace_dual,branch_trace_dual]
  rfl

theorem hermitian_product_real (X Y : Mat) (hX : Xᴴ=X) (hY : Yᴴ=Y) :
    (((X*Y).trace.re : ℝ):ℂ)=(X*Y).trace := by
  have hc : star (X*Y).trace=(X*Y).trace := by
    rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,hX,hY,Matrix.trace_mul_comm]
  have hi := Complex.conj_eq_iff_im.mp hc
  apply Complex.ext
  · rfl
  · simpa using hi.symm

/-- The actual real weight equals the full complex trace, including Y histories. -/
theorem kernel_trace (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (u v : HalfHistory) :
    kernel p r hp hp1 hr hr1 u v=(1/2:ℂ)*(halfEffect r v*D (p*p) (halfEffect r u)).trace := by
  unfold kernel weight
  rw [actual_trace]
  have h := hermitian_product_real (halfEffect r v) (D (p*p) (halfEffect r u))
    (halfEffect_adjoint r v) (by rw [D_adjoint,halfEffect_adjoint])
  simp only [Complex.mul_re]
  norm_num
  rw [h]

/-- Trace duality moves one copy of the central channel to each half-history. -/
theorem central_split (p : ℝ) (X Y : Mat) :
    (Y*D (p*p) X).trace=(D p Y*D p X).trace := by
  rw [← D_comp,D_trace_dual]

/-- Derived from actual weights, not imposed as the definition of the kernel. -/
theorem kernel_gram (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
    (u v : HalfHistory) :
    kernel p r hp hp1 hr hr1 u v=(midpoint p r v*rho*(midpoint p r u)ᴴ).trace := by
  rw [kernel_trace,central_split,midpoint_adjoint]
  simp only [midpoint,rho,mul_smul_comm,mul_one,smul_mul_assoc,Matrix.trace_smul,smul_eq_mul]


/-- These two actual projectors do not commute; the second is the Pauli Y outcome. -/
theorem xy_projectors_noncommute : projector 0*projector 2≠projector 2*projector 0 := by
  intro h
  have hi := congrArg Complex.im (congrFun (congrFun h 0) 0)
  norm_num [projector,sign,outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat,sigma,
    pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply] at hi

theorem halfEffect_xy (r : ℝ) : halfEffect r (0,2)=(1/18:ℂ) • projector 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfEffect,instrument_branch,D,effect,rho,projector,sign,outcomeEquiv,
      finProdFinEquiv,Fin.divNat,Fin.modNat,sigma,pauliX,pauliY,pauliZ,
      Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two,Matrix.one_apply] <;>
      ring_nf

theorem halfEffect_yx (r : ℝ) : halfEffect r (2,0)=(1/18:ℂ) • projector 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfEffect,instrument_branch,D,effect,rho,projector,sign,outcomeEquiv,
      finProdFinEquiv,Fin.divNat,Fin.modNat,sigma,pauliX,pauliY,pauliZ,
      Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two,Matrix.one_apply] <;>
      ring_nf <;> norm_num [Complex.I_sq]

/-- The chronological Y+,X+,Y+,X+ history has a positive actual weight. -/
theorem noncommuting_y_history (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1) :
    kernel p r hp hp1 hr hr1 (0,2) (2,0)=1/1296 := by
  rw [kernel_trace,halfEffect_xy,halfEffect_yx]
  norm_num [D,rho,projector,sign,outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat,sigma,
    pauliX,pauliY,pauliZ,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two,Matrix.one_apply]
  ring_nf

theorem halfEffect_opposite : halfEffect 1 (1,0)=0 := by
  rw [halfEffect,D_one,instrument_branch]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [effect,projector,sign,outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat,
      sigma,pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

/-- An actual impossible branch remains present; no probability division is used. -/
theorem opposite_actual_run_zero (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (v : HalfHistory) :
    run (Fin 2) Unit 6 (fourTree p 1 hp hp1 (by norm_num) le_rfl) (0,1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rho)=0 := by
  rw [actual_run (u := (1,0)),halfEffect_opposite,D_zero_matrix,FiniteInstrument.branch_zero,
    D_zero_matrix,FiniteInstrument.branch_zero,smul_zero]
  simp [GibbsMultilevelReflection.joint]

theorem opposite_history_zero (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (v : HalfHistory) :
    kernel p 1 hp hp1 (by norm_num) le_rfl (1,0) v=0 := by
  unfold kernel weight
  rw [opposite_actual_run_zero]
  simp


/-- Complex linearity is used before summing actual ordered branches. -/
def DLinear (q : ℝ) : Mat →ₗ[ℂ] Mat where
  toFun := D q
  map_add' := D_add q
  map_smul' := D_smul q

def branchLinear (o : Fin 6) : Mat →ₗ[ℂ] Mat where
  toFun := instrument.branch o
  map_add' := instrument.branch_add o
  map_smul' := instrument.branch_smul o

theorem D_sum {ι : Type*} [Fintype ι] (q : ℝ) (X : ι → Mat) : D q (∑ i, X i)=∑ i, D q (X i) :=
  map_sum (DLinear q) X Finset.univ

theorem effect_sum : ∑ o, effect o=1 := by
  simp only [effect,← Finset.smul_sum,projector_sum,smul_smul]
  norm_num

theorem branch_one (o : Fin 6) : instrument.branch o 1=effect o := by
  simp [instrument_branch,effect,projector_square]

/-- The outer outcome is summed after the actual channel and Lüders sandwich. -/
theorem halfEffect_outer (r : ℝ) (i : Fin 6) : ∑ o, halfEffect r (i,o)=effect i := by
  change (∑ o, branchLinear i (DLinear r (effect o)))=_
  rw [← map_sum,← map_sum,effect_sum]
  change instrument.branch i (D r 1)=effect i
  rw [D_unital,branch_one]

theorem midpoint_outer (p r : ℝ) (i : Fin 6) : ∑ o, midpoint p r (i,o)=D p (effect i) := by
  simp only [midpoint,← D_sum,halfEffect_outer]

def synthesis (p r : ℝ) (F : HalfHistory → ℂ) : Mat := ∑ u, F u • midpoint p r u

def synthesisLinear (p r : ℝ) : (HalfHistory → ℂ) →ₗ[ℂ] Mat where
  toFun := synthesis p r
  map_add' F G := by simp [synthesis,add_smul,Finset.sum_add_distrib]
  map_smul' c F := by simp [synthesis,Finset.smul_sum,smul_smul]

/-- Inner-only cylinders synthesize the accepted full complex Pauli observable map. -/
theorem synthesis_inner (p r : ℝ) (F : Fin 6 → ℂ) :
    synthesis p r (fun u => F u.1)=D p (PauliInstrumentReconstruction.synthesis F) := by
  unfold synthesis
  rw [Fintype.sum_prod_type]
  simp only [← Finset.smul_sum,midpoint_outer,← D_smul,← D_sum]
  rfl

theorem synthesis_constant (p r : ℝ) : synthesis p r (fun _ => 1)=1 := by
  have h := synthesis_inner p r (fun _ => 1)
  rw [PauliInstrumentReconstruction.synthesis_constant,D_unital] at h
  exact h

/-- Explicit inverse on all complex matrices; used only when central retention is positive. -/
def inverseD (p : ℝ) (X : Mat) : Mat := X.trace • rho+(p:ℂ)⁻¹ • (X-X.trace • rho)

theorem trace_centered (X : Mat) : (X-X.trace • rho).trace=0 := by
  simp [Matrix.trace_sub,Matrix.trace_smul,rho_density.2]

theorem D_centered (p : ℝ) (X : Mat) : D p (X-X.trace • rho)=(p:ℂ) • (X-X.trace • rho) := by
  rw [D,trace_centered]
  simp only [zero_smul,smul_zero,add_zero]

theorem D_inverse {p : ℝ} (hp : 0<p) (X : Mat) : D p (inverseD p X)=X := by
  have hpC : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp
  rw [inverseD,D_add,D_smul,D_stationary,D_smul,D_centered,smul_smul,inv_mul_cancel₀ hpC,one_smul]
  module

theorem inverseD_trace (p : ℝ) (X : Mat) : (inverseD p X).trace=X.trace := by
  simp [inverseD,Matrix.trace_add,Matrix.trace_smul,rho_density.2]

theorem inverse_D {p : ℝ} (hp : 0<p) (X : Mat) : inverseD p (D p X)=X := by
  have hpC : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp
  rw [inverseD,D_trace]
  have hc : D p X-X.trace • rho=(p:ℂ) • (X-X.trace • rho) := by
    unfold D
    module
  rw [hc,smul_smul,inv_mul_cancel₀ hpC,one_smul]
  module

/-- Uses the existing arbitrary-complex coefficients, including its Pauli Y term. -/
def coefficients (p : ℝ) (X : Mat) (u : HalfHistory) : ℂ :=
  PauliInstrumentReconstruction.coefficients (inverseD p X) u.1

theorem synthesis_coefficients {p : ℝ} (hp : 0<p) (r : ℝ) (X : Mat) :
    synthesis p r (coefficients p X)=X := by
  change synthesis p r (fun u => PauliInstrumentReconstruction.coefficients (inverseD p X) u.1)=X
  rw [synthesis_inner p r (PauliInstrumentReconstruction.coefficients (inverseD p X)),
    PauliInstrumentReconstruction.synthesis_coefficients,D_inverse hp]

/-- A non-Hermitian complex matrix is recovered, preserving the imaginary Y orientation. -/
theorem complex_y_right_inverse {p : ℝ} (hp : 0<p) (r : ℝ) :
    synthesis p r (coefficients p (pauliX+Complex.I • pauliY))=pauliX+Complex.I • pauliY :=
  synthesis_coefficients hp r _

/-- Full reset collapses every actual midpoint to a scalar matrix. -/
theorem midpoint_full_reset (r : ℝ) (u : HalfHistory) :
    midpoint 0 r u=(halfEffect r u).trace • rho := D_zero _

def resetMean (r : ℝ) (F : HalfHistory → ℂ) : ℂ :=
  ∑ u, F u*(halfEffect r u).trace/2

theorem synthesis_full_reset (r : ℝ) (F : HalfHistory → ℂ) :
    synthesis 0 r F=resetMean r F • (1 : Mat) := by
  simp only [synthesis,midpoint_full_reset,rho,smul_smul,← Finset.sum_smul,resetMean]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  ring

theorem scalar_identity_injective (a b : ℂ) (h : a • (1:Mat)=b • (1:Mat)) : a=b := by
  have he := congrFun (congrFun h 0) 0
  simpa using he

theorem resetMean_constant (r : ℝ) : resetMean r (fun _ => 1)=1 := by
  apply scalar_identity_injective
  rw [← synthesis_full_reset,synthesis_constant,one_smul]

theorem full_reset_zero_iff (r : ℝ) (F : HalfHistory → ℂ) :
    synthesis 0 r F=0 ↔ resetMean r F=0 := by
  rw [synthesis_full_reset]
  constructor
  · intro h
    exact scalar_identity_injective _ 0 (by simpa using h)
  · intro h
    simp [h]

theorem full_reset_nonzero (r : ℝ) : synthesis 0 r (fun _ => 1)≠0 := by
  rw [synthesis_constant]
  exact one_ne_zero


/-- The positive Y outcome has the required complex Pauli coefficient. -/
theorem y_coefficient (p : ℝ) (o : Fin 6) : coefficients p pauliY (2,o)=3/(p:ℂ) := by
  norm_num [coefficients,inverseD,PauliInstrumentReconstruction.coefficients,rho,projector,sign,
    outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat,sigma,pauliX,pauliY,pauliZ,
    Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  ring_nf
  norm_num [Complex.I_sq]

/-- Inner-only Pauli cylinder coefficients. -/
def innerMode (a : Fin 3) (u : HalfHistory) : ℂ := axisMode a u.1

theorem sigma_trace (a : Fin 3) : (sigma a).trace=0 := by
  fin_cases a <;> norm_num [sigma,pauliX,pauliY,pauliZ,Matrix.trace,Fin.sum_univ_two]

theorem synthesis_innerMode (p r : ℝ) (a : Fin 3) :
    synthesis p r (innerMode a)=(p:ℂ) • sigma a := by
  change synthesis p r (fun u => axisMode a u.1)=_
  rw [synthesis_inner,PauliInstrumentReconstruction.synthesis_axisMode,D,sigma_trace]
  simp

/-- Coefficients depending on both actual chronological outcomes. -/
def twoTimeMode (a b : Fin 3) (u : HalfHistory) : ℂ := axisMode a u.1*axisMode b u.2

theorem synthesis_twoTime (p r : ℝ) (a b : Fin 3) :
    synthesis p r (twoTimeMode a b)=
      D p (∑ i, axisMode a i • instrument.branch i (D r (sigma b))) := by
  unfold synthesis twoTimeMode midpoint halfEffect
  rw [Fintype.sum_prod_type]
  simp only [mul_smul,← D_smul,← D_sum,← Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change (∑ o, axisMode b o • branchLinear i (DLinear r (effect o))) = _
  simp only [← map_smul,← map_sum]
  change instrument.branch i (D r (PauliInstrumentReconstruction.synthesis (axisMode b))) = _
  rw [PauliInstrumentReconstruction.synthesis_axisMode]

theorem axisMode_X_table : axisMode 0=![3,-3,0,0,0,0] := by
  funext o
  fin_cases o <;> norm_num [axisMode,sign,outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat]

theorem weighted_branch_XX : (∑ i, axisMode 0 i • instrument.branch i (sigma 0))=(1:Mat) := by
  rw [axisMode_X_table]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,zero_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [instrument_branch,projector,sign,outcomeEquiv,finProdFinEquiv,
      Fin.divNat,Fin.modNat,sigma,pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

theorem weighted_branch_XZ : (∑ i, axisMode 0 i • instrument.branch i (sigma 2))=(0:Mat) := by
  change (∑ i, axisMode 0 i • instrument.branch i pauliZ)=0
  rw [axisMode_X_table]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,zero_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [instrument_branch,projector,sign,outcomeEquiv,finProdFinEquiv,
      Fin.divNat,Fin.modNat,sigma,pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

theorem D_sigma (p : ℝ) (a : Fin 3) : D p (sigma a)=(p:ℂ) • sigma a := by
  simp [D,sigma_trace]

theorem synthesis_XX (p r : ℝ) : synthesis p r (twoTimeMode 0 0)=(r:ℂ) • (1:Mat) := by
  rw [synthesis_twoTime,D_sigma]
  simp only [FiniteInstrument.branch_smul,smul_comm _ (r:ℂ),← Finset.smul_sum,
    weighted_branch_XX,D_smul,D_unital]

theorem synthesis_XZ (p r : ℝ) : synthesis p r (twoTimeMode 0 2)=0 := by
  rw [synthesis_twoTime,D_sigma]
  simp only [FiniteInstrument.branch_smul,smul_comm _ (r:ℂ),← Finset.smul_sum,
    weighted_branch_XZ,smul_zero,D_zero_matrix]

theorem twoTime_XZ_nonzero : twoTimeMode 0 2≠0 := by
  intro h
  have he := congrFun h (0,4)
  norm_num [twoTimeMode,axisMode,sign,outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat,Fin.ext_iff] at he

theorem weighted_smul (q : ℝ) (X Y : Mat) :
    (((q:ℂ) • Y)*rho*((q:ℂ) • X)ᴴ).trace=(q:ℂ)^2*(Y*rho*Xᴴ).trace := by
  simp only [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,Matrix.smul_mul,
    Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
  ring

theorem sigma_weighted (a b : Fin 3) :
    (sigma b*rho*(sigma a)ᴴ).trace=if a=b then 1 else 0 := by
  have h (c : Fin 3) : sigma c=modeMatrix c.succ := by fin_cases c <;> rfl
  rw [h,h,modeMatrix_weighted_trace]
  simp

section Reconstruction
open scoped InnerProductSpace
variable (p r : ℝ) (hp : 0≤p) (hp1 : p≤1) (hr : 0≤r) (hr1 : r≤1)
local notation "K" => kernel p r hp hp1 hr hr1
theorem kernel_posSemidef : Matrix.PosSemidef K := by
  letI := Matrix.toMatrixSeminormedAddCommGroup rho rho_density.1
  letI := Matrix.toMatrixInnerProductSpace rho rho_density.1
  have hk : K = Matrix.gram ℂ (midpoint p r) := by
    ext o p_
    exact kernel_gram p r hp hp1 hr hr1 o p_
  rw [hk]
  exact Matrix.posSemidef_gram ℂ (midpoint p r)

/-- The complete complex coefficient pairing has the conjugate-first observable orientation. -/
theorem pairing_synthesis (F G : HalfHistory → ℂ) :
    pairing K F G = (synthesis p r G * rho * (synthesis p r F)ᴴ).trace := by
  letI := Matrix.toMatrixSeminormedAddCommGroup rho rho_density.1
  letI := Matrix.toMatrixInnerProductSpace rho rho_density.1
  have hk : K = Matrix.gram ℂ (midpoint p r) := by
    ext o p_
    exact kernel_gram p r hp hp1 hr hr1 o p_
  rw [hk]
  exact Matrix.star_dotProduct_gram_mulVec (midpoint p r) F G

theorem pairing_observable (F G : HalfHistory → ℂ) :
    pairing K F G =
      ⟪GibbsObservable.observable rho_density.1 (synthesis p r F),
        GibbsObservable.observable rho_density.1 (synthesis p r G)⟫_ℂ := by
  rw [GibbsObservable.inner_observable, pairing_synthesis p r hp hp1 hr hr1]

local notation "hK" => kernel_posSemidef p r hp hp1 hr hr1

abbrev Reconstructed := Space K hK

theorem null_iff (F : HalfHistory → ℂ) : mk K hK F = 0 ↔ synthesis p r F = 0 := by
  rw [mk_eq_zero_iff, (pairing_synthesis p r hp hp1 hr hr1)]
  constructor
  · exact GibbsObservable.trace_weighted_eq_zero rho_posDef _
  · intro h
    simp [h]

def coefficientSynthesis : Coefficients hK →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (synthesisLinear p r)

theorem synthesis_null : nullSpace K hK ≤ (coefficientSynthesis p r hp hp1 hr hr1).ker := by
  intro F hF
  change synthesis p r F = 0
  apply ((null_iff p r hp hp1 hr hr1) F).mp
  rw [mk_eq_zero_iff]
  exact (mem_nullSpace_iff _ _ F).mp hF

/-- Descend the actual effect synthesis through precisely the zero-energy subspace. -/
def coordinates : (Reconstructed p r hp hp1 hr hr1) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  ((nullSpace K hK).liftQ (coefficientSynthesis p r hp hp1 hr hr1) (synthesis_null p r hp hp1 hr hr1)).comp
    (quotientEquiv K hK).symm.toLinearMap

theorem coordinates_mk (F : HalfHistory → ℂ) :
    (coordinates p r hp hp1 hr hr1) (mk K hK F) = synthesis p r F := by
  rw [← quotientEquiv_mk hK F]
  simp only [coordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  rfl

theorem coordinates_bijective (hpos : 0<p) : Function.Bijective (coordinates p r hp hp1 hr hr1) := by
  constructor
  · intro z w h
    obtain ⟨F,rfl⟩ := mk_surjective K hK z
    obtain ⟨G,rfl⟩ := mk_surjective K hK w
    rw [(coordinates_mk p r hp hp1 hr hr1), (coordinates_mk p r hp hp1 hr hr1)] at h
    apply (mk_eq_mk_iff K hK F G).mpr
    rw [(pairing_synthesis p r hp hp1 hr hr1)]
    have hz : synthesis p r (F-G) = 0 := by
      change (synthesisLinear p r) (F-G) = 0
      exact ((synthesisLinear p r).map_sub (F : HalfHistory → ℂ) G).trans (sub_eq_zero.mpr h)
    simp [hz]
  · intro X
    exact ⟨mk K hK (coefficients p X), by rw [(coordinates_mk p r hp hp1 hr hr1), synthesis_coefficients hpos]⟩

def coordinateEquiv (hpos : 0<p) : (Reconstructed p r hp hp1 hr hr1) ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearEquiv.ofBijective (coordinates p r hp hp1 hr hr1) (coordinates_bijective p r hp hp1 hr hr1 hpos)

theorem reconstructed_finrank (hpos : 0<p) : Module.finrank ℂ (Reconstructed p r hp hp1 hr hr1) = 4 := by
  rw [(coordinateEquiv p r hp hp1 hr hr1 hpos).finrank_eq]
  simpa using Module.finrank_matrix ℂ ℂ (Fin 2) (Fin 2)

def embeddingLinear : (Reconstructed p r hp hp1 hr hr1) →ₗ[ℂ] ObservableSpace :=
  (GibbsObservable.observableLinear rho_density.1).comp (coordinates p r hp hp1 hr hr1)

theorem embeddingLinear_mk (F : HalfHistory → ℂ) :
    (embeddingLinear p r hp hp1 hr hr1) (mk K hK F) =
      GibbsObservable.observable rho_density.1 (synthesis p r F) := by
  change GibbsObservable.observable rho_density.1 ((coordinates p r hp hp1 hr hr1) (mk K hK F)) = _
  rw [(coordinates_mk p r hp hp1 hr hr1)]

/-- Isometric identification with the full faithful matrix-observable space. -/
def embedding : (Reconstructed p r hp hp1 hr hr1) →ₗᵢ[ℂ] ObservableSpace :=
  (embeddingLinear p r hp hp1 hr hr1).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective K hK z
    obtain ⟨G,rfl⟩ := mk_surjective K hK w
    rw [(embeddingLinear_mk p r hp hp1 hr hr1), (embeddingLinear_mk p r hp hp1 hr hr1), inner_mk, (pairing_observable p r hp hp1 hr hr1)])

theorem embedding_mk (F : HalfHistory → ℂ) : (embedding p r hp hp1 hr hr1) (mk K hK F) =
    GibbsObservable.observable rho_density.1 (synthesis p r F) := (embeddingLinear_mk p r hp hp1 hr hr1) F

theorem embedding_surjective (hpos : 0<p) : Function.Surjective (embedding p r hp hp1 hr hr1) := by
  intro z
  obtain ⟨X,rfl⟩ := GibbsObservable.observable_surjective rho_density.1 z
  exact ⟨mk K hK (coefficients p X), by rw [(embedding_mk p r hp hp1 hr hr1), synthesis_coefficients hpos]⟩


/-- Full-reset coordinates land in the scalar identity line. -/
theorem reset_coordinates (z : Reconstructed 0 r (by norm_num) (by norm_num) hr hr1) :
    coordinates 0 r (by norm_num) (by norm_num) hr hr1 z =
      (coordinates 0 r (by norm_num) (by norm_num) hr hr1 z) 0 0 • (1:Mat) := by
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  rw [coordinates_mk,synthesis_full_reset]
  simp

def resetCoordinates : Reconstructed 0 r (by norm_num) (by norm_num) hr hr1 →ₗ[ℂ] ℂ where
  toFun z := coordinates 0 r (by norm_num) (by norm_num) hr hr1 z 0 0
  map_add' z w := by simp
  map_smul' c z := by simp

theorem resetCoordinates_mk (F : HalfHistory → ℂ) :
    resetCoordinates r hr hr1 (mk _ _ F)=resetMean r F := by
  change coordinates 0 r (by norm_num) (by norm_num) hr hr1 (mk _ _ F) 0 0 = _
  rw [coordinates_mk,synthesis_full_reset]
  simp

theorem resetCoordinates_bijective : Function.Bijective (resetCoordinates r hr hr1) := by
  constructor
  · intro z w h
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [resetCoordinates_mk,resetCoordinates_mk] at h
    apply (mk_eq_mk_iff _ _ F G).mpr
    rw [pairing_synthesis]
    have he : synthesis 0 r F=synthesis 0 r G := by rw [synthesis_full_reset,synthesis_full_reset,h]
    have hz : synthesis 0 r (F-G)=0 := (synthesisLinear 0 r).map_sub F G |>.trans (sub_eq_zero.mpr he)
    simp [hz]
  · intro c
    refine ⟨c • mk _ _ (fun _ => 1), ?_⟩
    rw [map_smul,resetCoordinates_mk,resetMean_constant]
    simp

def resetCoordinateEquiv : Reconstructed 0 r (by norm_num) (by norm_num) hr hr1 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (resetCoordinates r hr hr1) (resetCoordinates_bijective r hr hr1)

theorem reset_finrank : Module.finrank ℂ (Reconstructed 0 r (by norm_num) (by norm_num) hr hr1)=1 := by
  rw [(resetCoordinateEquiv r hr hr1).finrank_eq]
  exact Module.finrank_self ℂ


theorem innerMode_pairing (a b : Fin 3) :
    pairing K (innerMode a) (innerMode b)=if a=b then (p:ℂ)^2 else 0 := by
  rw [pairing_synthesis,synthesis_innerMode,synthesis_innerMode]
  rw [weighted_smul,sigma_weighted]
  split_ifs <;> simp

theorem innerMode_norm_sq (a : Fin 3) : ‖mk K hK (innerMode a)‖^2=p^2 := by
  rw [@norm_sq_eq_re_inner ℂ,inner_mk,innerMode_pairing,if_pos rfl]
  simp only [← Complex.ofReal_pow, RCLike.re_to_complex,Complex.ofReal_re]

theorem constant_pairing : pairing K (fun _ => 1) (fun _ => 1)=1 := by
  rw [pairing_synthesis,synthesis_constant]
  simp [rho_density.2]

theorem constant_innerMode_pairing (a : Fin 3) : pairing K (fun _ => 1) (innerMode a)=0 := by
  rw [pairing_synthesis,synthesis_constant,synthesis_innerMode]
  simp [rho,Matrix.trace_smul,sigma_trace]

def complexMode (u : HalfHistory) : ℂ := innerMode 0 u+Complex.I*innerMode 1 u

theorem synthesis_complexMode : synthesis p r complexMode=(p:ℂ) • (pauliX+Complex.I • pauliY) := by
  change synthesisLinear p r (innerMode 0+Complex.I • innerMode 1)=_
  rw [map_add,map_smul]
  change synthesis p r (innerMode 0)+Complex.I • synthesis p r (innerMode 1)=_
  rw [synthesis_innerMode,synthesis_innerMode]
  change (p:ℂ) • pauliX+Complex.I • ((p:ℂ) • pauliY)=_
  module

theorem complexMode_pairing : pairing K complexMode complexMode=2*(p:ℂ)^2 := by
  rw [pairing_synthesis,synthesis_complexMode]
  rw [weighted_smul]
  have h : ((pauliX+Complex.I • pauliY)*rho*(pauliX+Complex.I • pauliY)ᴴ).trace=2 := by
    norm_num [pauliX,pauliY,rho,Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    exact map_ofNat (starRingEnd ℂ) 2
  rw [h]
  ring

theorem twoTime_XX_pairing : pairing K (twoTimeMode 0 0) (twoTimeMode 0 0)=(r:ℂ)^2 := by
  rw [pairing_synthesis,synthesis_XX]
  rw [weighted_smul]
  simp [rho_density.2]

theorem twoTime_XZ_null : mk K hK (twoTimeMode 0 2)=0 :=
  (null_iff p r hp hp1 hr hr1 _).mpr (synthesis_XZ p r)

/-- Normalization sums the actual depth-four chronological weights. -/
theorem kernel_total : ∑ u, ∑ v, K u v=1 := by
  have h := constant_pairing p r hp hp1 hr hr1
  simpa [pairing,dotProduct,Matrix.mulVec] using h


theorem constant_norm_sq : ‖mk K hK (fun _ => 1)‖^2=1 := by
  rw [@norm_sq_eq_re_inner ℂ,inner_mk,constant_pairing]
  rfl

theorem complexMode_norm_sq : ‖mk K hK complexMode‖^2=2*p^2 := by
  rw [@norm_sq_eq_re_inner ℂ,inner_mk,complexMode_pairing]
  simp [← Complex.ofReal_pow]

theorem twoTime_XX_norm_sq : ‖mk K hK (twoTimeMode 0 0)‖^2=r^2 := by
  rw [@norm_sq_eq_re_inner ℂ,inner_mk,twoTime_XX_pairing]
  simp [← Complex.ofReal_pow]

/-- This commutator belongs to the matrix images, not a coefficientwise quotient algebra. -/
theorem image_commutator : synthesis p r (innerMode 0)*synthesis p r (innerMode 1)-
    synthesis p r (innerMode 1)*synthesis p r (innerMode 0)=
      (2*Complex.I*(p:ℂ)^2) • pauliZ := by
  simp only [synthesis_innerMode,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← smul_sub]
  have h := PauliInstrumentReconstruction.matrix_image_commutator
  simp only [PauliInstrumentReconstruction.synthesis_axisMode] at h
  rw [h]
  change ((p:ℂ)*(p:ℂ)) • ((2*Complex.I) • pauliZ)=_
  rw [smul_smul]
  congr 1
  ring

theorem image_commutator_nonzero (hpos : 0<p) :
    synthesis p r (innerMode 0)*synthesis p r (innerMode 1)-
      synthesis p r (innerMode 1)*synthesis p r (innerMode 0)≠0 := by
  rw [image_commutator]
  intro h
  have he := congrArg (fun X : Mat => (X 0 0).im) h
  norm_num [pauliZ,Complex.mul_im,Complex.mul_re,pow_two] at he
  nlinarith

/-- Both outer outcomes are marginalized in the actual four-event process. -/
theorem outer_marginal_trace (i j : Fin 6) :
    ∑ o, ∑ q, K (i,o) (j,q)=(1/2:ℂ)*(effect j*D (p*p) (effect i)).trace := by
  simp_rw [kernel_trace]
  simp only [← Finset.mul_sum,← Matrix.trace_sum,← Matrix.sum_mul,halfEffect_outer,
    ← D_sum]

/-- Actual two-event process with the squared central retention. -/
def twoTree : Tree (Fin 2) Unit 6 2 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step (p*p) (mul_nonneg hp hp) (by nlinarith)) (fun _ => .done))

def twoKernel (i j : Fin 6) : ℂ :=
  (weight (Fin 2) Unit 6 (twoTree p hp hp1) (i,j,()) (GibbsMultilevelReflection.joint rho):ℂ)

theorem twoKernel_trace (i j : Fin 6) : twoKernel p hp hp1 i j=
    (1/2:ℂ)*(effect j*D (p*p) (effect i)).trace := by
  have runEq : run (Fin 2) Unit 6 (twoTree p hp hp1) (i,j,()) (GibbsMultilevelReflection.joint rho)=
      GibbsMultilevelReflection.joint ((1/2:ℂ) • instrument.branch j (D (p*p) (effect i))) := by
    change (step (p*p) (mul_nonneg hp hp) (by nlinarith)).branch (Fin 2) Unit 6 j
      ((step 1 (by norm_num) le_rfl).branch (Fin 2) Unit 6 i (GibbsMultilevelReflection.joint rho))=_
    simp only [step_branch,D_one,branch_rho,D_smul,FiniteInstrument.branch_smul]
  unfold twoKernel weight
  rw [runEq,GibbsMultilevelReflection.joint_trace,Matrix.trace_smul,branch_trace]
  have hh := hermitian_product_real (effect j) (D (p*p) (effect i)) (effect_adjoint j)
    (by rw [D_adjoint,effect_adjoint])
  simpa using congrArg (fun z : ℂ => (1/2:ℂ)*z) hh

theorem outer_marginal (i j : Fin 6) : ∑ o, ∑ q, K (i,o) (j,q)=twoKernel p hp hp1 i j := by
  rw [outer_marginal_trace,twoKernel_trace]

theorem twoKernel_one (i j : Fin 6) : twoKernel 1 (by norm_num) le_rfl i j=
    PauliInstrumentReconstruction.kernel i j := by
  rw [twoKernel_trace]
  norm_num only [one_mul,D_one]
  rw [PauliInstrumentReconstruction.kernel_gram]
  rw [effect_adjoint]
  simp [rho,Matrix.trace_smul]


theorem halfEffect_allX (r : ℝ) : halfEffect r (0,0)=((1+(r:ℂ))/18) • projector 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfEffect,instrument_branch,D,effect,projector,rho,sign,outcomeEquiv,
      finProdFinEquiv,Fin.divNat,Fin.modNat,sigma,pauliX,pauliY,pauliZ,
      Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply] <;> ring

theorem allX_weight : K (0,0) (0,0)=((1+(r:ℂ))^2*(1+(p:ℂ)^2))/1296 := by
  rw [kernel_trace,halfEffect_allX,D_smul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
  have h : (projector 0*D (p*p) (projector 0)).trace=(1+(p:ℂ)^2)/2 := by
    norm_num [D,projector,rho,sign,outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat,
      sigma,pauliX,pauliY,pauliZ,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
    ring
  rw [h]
  ring

theorem allX_no_reset : kernel 1 1 (by norm_num) le_rfl (by norm_num) le_rfl (0,0) (0,0)=1/162 := by
  rw [allX_weight]
  norm_num

theorem allX_half_reset : kernel (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (0,0) (0,0)=5/2304 := by
  rw [allX_weight]
  norm_num


/-- The observable norm is the faithful rho-weighted Hilbert norm. -/
def observableEquiv (hpos : 0<p) : Reconstructed p r hp hp1 hr hr1 ≃ₗᵢ[ℂ] ObservableSpace :=
  LinearIsometryEquiv.ofSurjective (embedding p r hp hp1 hr hr1)
    (embedding_surjective p r hp hp1 hr hr1 hpos)

theorem reset_null_mean (F : HalfHistory → ℂ) :
    mk (kernel 0 r (by norm_num) (by norm_num) hr hr1)
      (kernel_posSemidef 0 r (by norm_num) (by norm_num) hr hr1) F=0 ↔ resetMean r F=0 := by
  rw [null_iff,full_reset_zero_iff]

theorem twoTime_XZ_value : twoTimeMode 0 2 (0,4)=9 := by
  norm_num [twoTimeMode,axisMode,sign,outcomeEquiv,finProdFinEquiv,Fin.divNat,Fin.modNat,Fin.ext_iff]

theorem twoTime_XX_positive (hrpos : 0<r) : 0<‖mk K hK (twoTimeMode 0 0)‖^2 := by
  rw [twoTime_XX_norm_sq]
  positivity

end Reconstruction

/-- Finite nonnegative waiting times use the actual normalized reset semigroup. -/
def retention (γ t : ℝ) : ℝ := Real.exp (-γ*t)

theorem retention_positive (γ t : ℝ) : 0<retention γ t := Real.exp_pos _
theorem retention_le_one (γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t) : retention γ t≤1 :=
  GibbsReset.exp_rate_le_one γ t hγ ht

theorem retention_add (γ s t : ℝ) : retention γ (s+t)=retention γ s*retention γ t := by
  unfold retention
  rw [mul_add,Real.exp_add]

theorem retention_twice (γ a : ℝ) : retention γ (2*a)=retention γ a*retention γ a := by
  rw [show 2*a=a+a by ring,retention_add]

def observationTimes (a b : ℝ) : Fin 4 → ℝ := ![-a-b,-a,a,a+b]

theorem observation_gaps (a b : ℝ) :
    observationTimes a b 1-observationTimes a b 0=b ∧
    observationTimes a b 2-observationTimes a b 1=2*a ∧
    observationTimes a b 3-observationTimes a b 2=b := by
  change -a-(-a-b)=b ∧ a-(-a)=2*a ∧ (a+b)-a=b
  constructor
  · ring
  constructor <;> ring

theorem observation_ordered (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    observationTimes a b 0≤observationTimes a b 1 ∧
    observationTimes a b 1≤observationTimes a b 2 ∧
    observationTimes a b 2≤observationTimes a b 3 := by
  change -a-b≤ -a ∧ -a≤a ∧ a≤a+b
  constructor
  · linarith
  constructor <;> linarith

/-- The actual Kraus state map agrees with the already constructed Lindblad action. -/
theorem physical_channel (γ t : ℝ) (hγ : 0≤γ) (ht : 0≤t) (X : Mat) :
    D (retention γ t) X=OpenSystems.lindbladPropagatorAction 0 (GibbsReset.jumps uniformWeights γ) t X := by
  rw [← channel_state (retention_positive γ t).le (retention_le_one γ t hγ ht)]
  exact GibbsReset.time_state_eq_propagator uniformWeights uniform_nonnegative uniform_normalized γ t hγ ht X

def physicalTree (γ a b : ℝ) (hγ : 0≤γ) (ha : 0≤a) (hb : 0≤b) : Tree (Fin 2) Unit 6 4 :=
  fourTree (retention γ a) (retention γ b) (retention_positive γ a).le
    (retention_le_one γ a hγ ha) (retention_positive γ b).le (retention_le_one γ b hγ hb)

theorem physical_central (γ a : ℝ) (X : Mat) :
    D (retention γ a*retention γ a) X=D (retention γ (2*a)) X := by rw [retention_twice]

theorem finite_time_finrank (γ a b : ℝ) (hγ : 0≤γ) (ha : 0≤a) (hb : 0≤b) :
    Module.finrank ℂ (Reconstructed (retention γ a) (retention γ b) (retention_positive γ a).le
      (retention_le_one γ a hγ ha) (retention_positive γ b).le (retention_le_one γ b hγ hb))=4 :=
  reconstructed_finrank _ _ _ _ _ _ (retention_positive γ a)

/-- Full reset is a separate boundary channel, never an attained finite waiting time. -/
theorem finite_time_not_full_reset (γ t : ℝ) : retention γ t≠0 := ne_of_gt (retention_positive γ t)

theorem retention_zero_wait (γ : ℝ) : retention γ 0=1 := by simp [retention]
theorem retention_zero_rate (t : ℝ) : retention 0 t=1 := by simp [retention]

/-! This finite stationary symmetric construction does not assert reflection positivity for
arbitrary channels, feedback, nonstationary preparations, or arbitrary-depth histories.
It supplies no continuum OS/Wightman reconstruction, field-existence theorem, tomography
protocol, or physical clock identification. Its quotient is a complex Hilbert space;
coefficientwise multiplication is not claimed to descend to its null quotient. -/

end SKEFTHawking.QuantumNetwork.PauliReflectedCylinder
