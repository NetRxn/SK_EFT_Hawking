import SKEFTHawking.FinitePauliInstrumentReconstruction
import SKEFTHawking.FiniteGibbsReset

/-!
# A stationary nontracial Pauli instrument

The six Pauli effects are realized by one explicitly normalized Kraus operator
per outcome at the faithful state diag(16/25,9/25). Branch reversal uses the
square-root sandwich on all complex matrices. The unchanged Lüders instrument
at this state has unequal reversed two-event weights.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.NontracialPauliReflection
open Matrix FiniteInterventionProcess
open scoped BigOperators ComplexOrder Kronecker

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def rhoN : Mat2 := !![16/25, 0; 0, 9/25]
def R : Mat2 := !![4/5, 0; 0, 3/5]
def Gamma (A : Mat2) : Mat2 := R * A * R
def d (o : Fin 6) : ℝ := (PauliInstrumentReconstruction.projector o * rhoN).trace.re

theorem R_adjoint : Rᴴ = R := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [R, Matrix.conjTranspose_apply]

theorem R_square : R * R = rhoN := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [R, rhoN, Matrix.mul_apply, Fin.sum_univ_two]

theorem rhoN_trace : rhoN.trace = 1 := by
  norm_num [rhoN, Matrix.trace, Fin.sum_univ_two]

theorem rhoN_posDef : rhoN.PosDef := by
  have h : rhoN = Matrix.diagonal (![16/25,9/25] : Fin 2 → ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [rhoN]
  rw [h]
  apply Matrix.PosDef.diagonal
  intro i; fin_cases i <;> norm_num [Complex.lt_def]

theorem rhoN_density : IsDensityOperator rhoN := ⟨rhoN_posDef.posSemidef, rhoN_trace⟩

theorem rhoN_not_scalar (z : ℂ) : rhoN ≠ z • (1 : Mat2) := by
  intro h
  have h0 := congrArg (fun A : Mat2 => A 0 0) h
  have h1 := congrArg (fun A : Mat2 => A 1 1) h
  norm_num [rhoN] at h0 h1
  have : (16/25 : ℂ) = 9/25 := h0.trans h1.symm
  norm_num at this

theorem d_values (o : Fin 6) : d o = ![1/2,1/2,1/2,1/2,16/25,9/25] o := by
  fin_cases o <;>
    norm_num [d, rhoN, PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

theorem d_pos (o : Fin 6) : 0 < d o := by
  rw [d_values]; fin_cases o <;> norm_num

theorem d_trace (o : Fin 6) : (d o : ℂ) = (PauliInstrumentReconstruction.projector o * rhoN).trace := by
  rw [d_values]
  fin_cases o <;>
    norm_num [rhoN, PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]

theorem projector_rho_projector (o : Fin 6) :
    PauliInstrumentReconstruction.projector o * rhoN * PauliInstrumentReconstruction.projector o = (d o : ℂ) • PauliInstrumentReconstruction.projector o := by
  rw [d_values]
  fin_cases o <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rhoN, PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv,
      Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    ring_nf <;> norm_num [Complex.I_sq]

def c (o : Fin 6) : ℂ := (Real.sqrt (3 * d o) : ℂ)⁻¹
def L (o : Fin 6) : Mat2 := c o • (R * PauliInstrumentReconstruction.projector o)

theorem c_real (o : Fin 6) : star (c o) = c o := by simp [c]

theorem c_square_d (o : Fin 6) : c o * c o * (d o : ℂ) = 1/3 := by
  have hd : d o ≠ 0 := ne_of_gt (d_pos o)
  have hc : (d o : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [c, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (mul_pos (by norm_num) (d_pos o)))]
  push_cast
  field_simp

theorem L_effect (o : Fin 6) : (L o)ᴴ * L o = PauliInstrumentReconstruction.effect o := by
  simp only [L, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    PauliInstrumentReconstruction.projector_adjoint, R_adjoint, c_real, smul_mul_smul]
  have h : PauliInstrumentReconstruction.projector o * R * (R * PauliInstrumentReconstruction.projector o) =
      PauliInstrumentReconstruction.projector o * rhoN * PauliInstrumentReconstruction.projector o := by rw [← R_square]; noncomm_ring
  rw [h, projector_rho_projector, smul_smul, c_square_d]
  rfl

def instrument : FiniteInstrument (Fin 2) 6 where
  count := 1
  operators o _ := L o
  normalized := by
    simp only [Fin.sum_univ_one, L_effect, PauliInstrumentReconstruction.effect]
    rw [← Finset.smul_sum, PauliInstrumentReconstruction.projector_sum, smul_smul]
    norm_num

def J (o : Fin 6) (A : Mat2) : Mat2 := (L o)ᴴ * A * L o

theorem instrument_branch (o : Fin 6) (X : Mat2) :
    instrument.branch o X = L o * X * (L o)ᴴ := by
  simp [FiniteInstrument.branch, instrument, krausMap]

theorem branch_Gamma (o : Fin 6) (A : Mat2) :
    instrument.branch o (Gamma A) = Gamma (J o A) := by
  rw [instrument_branch]
  simp only [Gamma, J, L, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    PauliInstrumentReconstruction.projector_adjoint, R_adjoint, c_real, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  noncomm_ring

theorem J_one (o : Fin 6) : J o 1 = PauliInstrumentReconstruction.effect o := by
  simpa [J] using L_effect o

theorem branch_rhoN (o : Fin 6) : instrument.branch o rhoN = Gamma (PauliInstrumentReconstruction.effect o) := by
  have h : rhoN = Gamma 1 := by simpa [Gamma] using R_square.symm
  rw [h, branch_Gamma, J_one]

theorem instrument_stationary : ∑ o, instrument.branch o rhoN = rhoN := by
  simp_rw [branch_rhoN, Gamma]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  simp only [PauliInstrumentReconstruction.effect]
  rw [← Finset.smul_sum, PauliInstrumentReconstruction.projector_sum, smul_smul]
  norm_num [R_square]

theorem trace_duality (o : Fin 6) (A X : Mat2) :
    (A * instrument.branch o X).trace = (J o A * X).trace := by
  rw [instrument_branch, J]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

/-- The original instrument and original tree, with only the initial state changed. -/
def originalKernel (o p : Fin 6) : ℂ :=
  (weight (Fin 2) Unit 6 PauliInstrumentReconstruction.tree (o,p,())
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem original_run (o p : Fin 6) :
    run (Fin 2) Unit 6 PauliInstrumentReconstruction.tree (o,p,())
      (GibbsMultilevelReflection.joint rhoN) =
    GibbsMultilevelReflection.joint
      ((1/9 : ℂ) • (PauliInstrumentReconstruction.projector p *
        (PauliInstrumentReconstruction.projector o * rhoN *
          PauliInstrumentReconstruction.projector o) *
        PauliInstrumentReconstruction.projector p)) := by
  change PauliInstrumentReconstruction.step.branch (Fin 2) Unit 6 p
    (PauliInstrumentReconstruction.step.branch (Fin 2) Unit 6 o
      (GibbsMultilevelReflection.joint rhoN)) = _
  rw [PauliInstrumentReconstruction.step_branch,
    PauliInstrumentReconstruction.step_branch,
    PauliInstrumentReconstruction.instrument_branch,
    PauliInstrumentReconstruction.instrument_branch]
  congr 1
  norm_num [smul_smul]

theorem original_xz : originalKernel 0 4 = 1/36 := by
  unfold originalKernel weight
  rw [original_run, GibbsMultilevelReflection.joint_trace]
  norm_num [rhoN, PauliInstrumentReconstruction.projector,
    PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
    finProdFinEquiv, Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma,
    pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two,
    Matrix.one_apply]

theorem original_zx : originalKernel 4 0 = 8/225 := by
  unfold originalKernel weight
  rw [original_run, GibbsMultilevelReflection.joint_trace]
  norm_num [rhoN, PauliInstrumentReconstruction.projector,
    PauliInstrumentReconstruction.sign, PauliInstrumentReconstruction.outcomeEquiv,
    finProdFinEquiv, Fin.divNat, Fin.modNat, PauliInstrumentReconstruction.sigma,
    pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two,
    Matrix.one_apply]

theorem original_asymmetry : originalKernel 4 0 - originalKernel 0 4 = 7/900 := by
  rw [original_zx, original_xz]
  norm_num

theorem original_asymmetry_positive :
    0 < (originalKernel 4 0 - originalKernel 0 4).re := by
  rw [original_asymmetry]
  norm_num

theorem original_not_hermitian : ¬ Matrix.IsHermitian originalKernel := by
  intro h
  have he := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℂ => A 0 4) h.eq
  simp only [Matrix.conjTranspose_apply, original_zx, original_xz] at he
  norm_num at he

theorem original_not_posSemidef : ¬ Matrix.PosSemidef originalKernel := by
  intro h
  exact original_not_hermitian h.isHermitian

open FinitePositiveKernel GibbsObservable

def weights : Fin 2 → ℝ := ![16/25,9/25]

theorem weights_nonnegative (i : Fin 2) : 0 ≤ weights i := by
  fin_cases i <;> norm_num [weights]

theorem weights_normalized : ∑ i, weights i = 1 := by
  norm_num [weights, Fin.sum_univ_two]

theorem weights_density : DiagonalLindblad.density weights = rhoN := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [DiagonalLindblad.density, weights, rhoN]

def channel (q : ℝ) := GibbsReset.timeKraus weights q

def Phi (q : ℝ) (X : Mat2) : Mat2 :=
  (q : ℂ) • X + (1-(q : ℂ)) • (X.trace • rhoN)

def Psi (q : ℝ) (A : Mat2) : Mat2 :=
  (q : ℂ) • A + (1-(q : ℂ)) • ((rhoN * A).trace • 1)

theorem channel_normalized {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    IsKrausChannel (channel q) :=
  GibbsReset.time_normalized weights weights_nonnegative weights_normalized q hq hq1

theorem channel_state {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (X : Mat2) :
    krausMap (channel q) X = Phi q X := by
  rw [channel, GibbsReset.time_state weights weights_nonnegative q hq hq1, weights_density]
  rfl

theorem channel_observable {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (A : Mat2) :
    Channel.heisenberg (channel q) A = Psi q A := by
  rw [channel, GibbsReset.time_observable weights weights_nonnegative q hq hq1, weights_density]
  rfl

theorem channel_stationary {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    krausMap (channel q) rhoN = rhoN := by
  rw [← weights_density]
  exact GibbsReset.time_stationary weights weights_nonnegative weights_normalized q hq hq1

theorem Gamma_trace (A : Mat2) : (Gamma A).trace = (rhoN * A).trace := by
  rw [Gamma, Matrix.trace_mul_cycle, R_square]

theorem Gamma_one : Gamma 1 = rhoN := by simpa [Gamma] using R_square

theorem Gamma_smul (z : ℂ) (A : Mat2) : Gamma (z • A) = z • Gamma A := by
  simp [Gamma]

theorem Gamma_add (A B : Mat2) : Gamma (A+B) = Gamma A + Gamma B := by
  simp [Gamma, mul_add, add_mul]

theorem Phi_Gamma (q : ℝ) (A : Mat2) : Phi q (Gamma A) = Gamma (Psi q A) := by
  simp only [Phi, Psi, Gamma_trace, Gamma_add, Gamma_smul, Gamma_one]

theorem Phi_Psi_duality (q : ℝ) (A X : Mat2) :
    (A * Phi q X).trace = (Psi q A * X).trace := by
  simp only [Phi, Psi, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    Matrix.trace_add, Matrix.trace_smul, one_mul, smul_eq_mul]
  rw [Matrix.trace_mul_comm A rhoN]
  ring

theorem Psi_mean (q : ℝ) (A : Mat2) : (rhoN * Psi q A).trace = (rhoN*A).trace := by
  simp only [Psi, mul_add, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul,
    mul_one, rhoN_trace, smul_eq_mul, mul_one]
  ring

theorem Psi_comp (p q : ℝ) (A : Mat2) : Psi p (Psi q A) = Psi (p*q) A := by
  rw [Psi, Psi_mean]
  simp only [Psi, smul_add, smul_smul, Complex.ofReal_mul]
  module

theorem Phi_one (X : Mat2) : Phi 1 X = X := by simp [Phi]
theorem Phi_zero (X : Mat2) : Phi 0 X = X.trace • rhoN := by simp [Phi]
theorem Psi_one (A : Mat2) : Psi 1 A = A := by simp [Psi]
theorem Psi_zero (A : Mat2) : Psi 0 A = (rhoN*A).trace • 1 := by simp [Psi]

theorem Psi_unital (q : ℝ) : Psi q 1 = 1 := by
  simp only [Psi, mul_one, rhoN_trace, one_smul]
  module

theorem Psi_smul (q : ℝ) (z : ℂ) (A : Mat2) : Psi q (z • A) = z • Psi q A := by
  simp only [Psi, mul_smul_comm, Matrix.trace_smul, smul_add, smul_smul, smul_eq_mul]
  module

theorem Psi_add (q : ℝ) (A B : Mat2) : Psi q (A+B) = Psi q A + Psi q B := by
  simp only [Psi, mul_add, Matrix.trace_add, smul_add, add_smul]
  module

theorem rhoN_adjoint : rhoNᴴ = rhoN := rhoN_density.1.isHermitian.eq

theorem Psi_adjoint (q : ℝ) (A : Mat2) : (Psi q A)ᴴ = Psi q Aᴴ := by
  simp only [Psi, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_sub, star_one, Complex.star_def, Complex.conj_ofReal,
    ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, rhoN_adjoint]
  rw [Matrix.trace_mul_comm Aᴴ rhoN]

theorem Gamma_adjoint (A : Mat2) : (Gamma A)ᴴ = Gamma Aᴴ := by
  simp [Gamma, Matrix.conjTranspose_mul, R_adjoint, Matrix.mul_assoc]

/-- Symmetric square-root-weighted form, with conjugation in its first argument. -/
def form (A B : Mat2) : ℂ := (B * R * Aᴴ * R).trace

theorem form_Psi_symmetric (q : ℝ) (A B : Mat2) :
    form A (Psi q B) = form (Psi q A) B := by
  simp only [form, Psi_adjoint]
  change (Psi q B * R * Aᴴ * R).trace = (B * R * Psi q Aᴴ * R).trace
  have hg (X Y : Mat2) : (X*R*Y*R).trace = (X*Gamma Y).trace := by
    simp only [Gamma, Matrix.mul_assoc]
  rw [hg, hg]
  rw [← Phi_Gamma, Phi_Psi_duality]

def qdiag : Fin 2 → ℝ := ![Real.sqrt (4/5),Real.sqrt (3/5)]
def Q : Mat2 := Matrix.diagonal (fun i => (qdiag i : ℂ))
def feature (A : Mat2) : Mat2 := Q * A * Q

theorem qdiag_pos (i : Fin 2) : 0 < qdiag i := by
  fin_cases i <;> norm_num [qdiag]

theorem Q_adjoint : Qᴴ = Q := by
  ext i j
  by_cases h : i=j <;> simp [Q, Matrix.conjTranspose_apply, h, eq_comm]

theorem qdiag_square (i : Fin 2) : qdiag i * qdiag i = ![4/5,3/5] i := by
  fin_cases i <;> simp only [qdiag]
  · exact Real.mul_self_sqrt (by norm_num)
  · exact Real.mul_self_sqrt (by norm_num)

theorem Q_square : Q * Q = R := by
  have h : Q*Q = Matrix.diagonal (fun i => (qdiag i : ℂ)*(qdiag i : ℂ)) := by
    exact Matrix.diagonal_mul_diagonal _ _
  rw [h]
  simp only [← Complex.ofReal_mul, qdiag_square]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [R]

theorem feature_injective : Function.Injective feature := by
  intro A B h
  ext i j
  have he := congrArg (fun M : Mat2 => M i j) h
  simp only [feature, Q, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  have hi : (qdiag i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (qdiag_pos i)
  have hj : (qdiag j : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (qdiag_pos j)
  exact mul_left_cancel₀ hi (mul_right_cancel₀ hj he)

theorem feature_gram (A B : Mat2) : (feature B * (feature A)ᴴ).trace = form A B := by
  simp only [feature, Matrix.conjTranspose_mul, Q_adjoint, form]
  rw [← Matrix.mul_assoc Q Aᴴ Q]
  calc
    (Q*B*Q*(Q*Aᴴ*Q)).trace = (Q*(B*(Q*Q)*Aᴴ)*Q).trace := by congr 1; noncomm_ring
    _ = (Q*Q*(B*(Q*Q)*Aᴴ)).trace := Matrix.trace_mul_cycle _ _ _
    _ = (R*(B*R*Aᴴ)).trace := by rw [Q_square]
    _ = (B*R*Aᴴ*R).trace := Matrix.trace_mul_comm _ _

abbrev HalfHistory := Fin 6 × Fin 6

/-- The actual reset Kraus evolution precedes the actual replacement instrument. -/
def step (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) : Step (Fin 2) Unit 6 where
  count := _
  evolution k := GibbsMultilevelReflection.joint (channel q k)
  normalized := GibbsMultilevelReflection.joint_normalized _ (channel_normalized hq hq1)
  instrument := instrument

theorem step_branch (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (o : Fin 6) (X : Mat2) :
    (step q hq hq1).branch (Fin 2) Unit 6 o (GibbsMultilevelReflection.joint X) =
      GibbsMultilevelReflection.joint (instrument.branch o (Phi q X)) := by
  change (instrument.lift Unit).branch o
    (krausMap (fun k => GibbsMultilevelReflection.joint (channel q k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus, channel_state hq hq1]
  exact GibbsMultilevelReflection.joint_kraus _ _

def negativeTree (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : Tree (Fin 2) Unit 6 2 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step r hr hr1) (fun _ => .done))

/-- Half labels are (inner,outer); chronology is outer,inner,inner,outer. -/
def fourTree (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Tree (Fin 2) Unit 6 4 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step r hr hr1) (fun _ =>
      .node (step (p*p) (mul_nonneg hp hp) (by nlinarith)) (fun _ =>
        .node (step r hr hr1) (fun _ => .done))))

/-- Defined from the actual four-node process weight before the Gram theorem. -/
def kernel (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) : ℂ :=
  (weight (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

def halfEffect (r : ℝ) (u : HalfHistory) : Mat2 :=
  J u.1 (Psi r (PauliInstrumentReconstruction.effect u.2))

def midpoint (p r : ℝ) (u : HalfHistory) : Mat2 := Psi p (halfEffect r u)

theorem J_adjoint (o : Fin 6) (A : Mat2) : (J o A)ᴴ = J o Aᴴ := by
  simp [J, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem effect_adjoint (o : Fin 6) :
    (PauliInstrumentReconstruction.effect o)ᴴ = PauliInstrumentReconstruction.effect o := by
  simp [PauliInstrumentReconstruction.effect, Matrix.conjTranspose_smul,
    PauliInstrumentReconstruction.projector_adjoint]

theorem halfEffect_adjoint (r : ℝ) (u : HalfHistory) : (halfEffect r u)ᴴ = halfEffect r u := by
  rw [halfEffect, J_adjoint, Psi_adjoint, effect_adjoint]

theorem midpoint_adjoint (p r : ℝ) (u : HalfHistory) :
    (midpoint p r u)ᴴ = midpoint p r u := by
  rw [midpoint, Psi_adjoint, halfEffect_adjoint]

theorem branch_trace (o : Fin 6) (X : Mat2) :
    (instrument.branch o X).trace = (PauliInstrumentReconstruction.effect o * X).trace := by
  simpa only [one_mul, J_one] using trace_duality o 1 X

/-- Actual negative-half state, retaining the nontracial square-root sandwich. -/
theorem negative_run (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (u : HalfHistory) :
    run (Fin 2) Unit 6 (negativeTree r hr hr1) (u.2,u.1,())
      (GibbsMultilevelReflection.joint rhoN) =
    GibbsMultilevelReflection.joint (Gamma (halfEffect r u)) := by
  change (step r hr hr1).branch (Fin 2) Unit 6 u.1
    ((step 1 (by norm_num) le_rfl).branch (Fin 2) Unit 6 u.2
      (GibbsMultilevelReflection.joint rhoN)) = _
  rw [step_branch, step_branch, Phi_one, branch_rhoN, Phi_Gamma, branch_Gamma]
  rfl

theorem actual_run (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) :
    run (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rhoN) =
    GibbsMultilevelReflection.joint (instrument.branch v.2
      (Phi r (instrument.branch v.1 (Phi (p*p) (Gamma (halfEffect r u)))))) := by
  change (step r hr hr1).branch (Fin 2) Unit 6 v.2
    ((step (p*p) (mul_nonneg hp hp) (by nlinarith)).branch (Fin 2) Unit 6 v.1
      (run (Fin 2) Unit 6 (negativeTree r hr hr1) (u.2,u.1,())
        (GibbsMultilevelReflection.joint rhoN))) = _
  rw [negative_run, step_branch, step_branch]

theorem actual_trace (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) :
    (run (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) (u.2,u.1,v.1,v.2,())
      (GibbsMultilevelReflection.joint rhoN)).trace =
      (halfEffect r v * Phi (p*p) (Gamma (halfEffect r u))).trace := by
  rw [actual_run, GibbsMultilevelReflection.joint_trace, branch_trace,
    Phi_Psi_duality, trace_duality]
  rfl

theorem hermitian_product_real (A B : Mat2) (hA : Aᴴ=A) (hB : Bᴴ=B) :
    (((A*B).trace.re : ℝ) : ℂ) = (A*B).trace := by
  have hc : star (A*B).trace = (A*B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hB,
      Matrix.trace_mul_comm]
  have hi := Complex.conj_eq_iff_im.mp hc
  apply Complex.ext
  · rfl
  · simpa using hi.symm

/-- The actual real process weight is the full complex trace, also for Pauli Y labels. -/
theorem kernel_trace (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) :
    kernel p r hp hp1 hr hr1 u v =
      (halfEffect r v * Phi (p*p) (Gamma (halfEffect r u))).trace := by
  unfold kernel weight
  rw [actual_trace]
  apply hermitian_product_real _ _ (halfEffect_adjoint r v)
  rw [Phi_Gamma, Gamma_adjoint, Psi_adjoint, halfEffect_adjoint]

theorem central_split (p : ℝ) (A B : Mat2) :
    (B * Phi (p*p) (Gamma A)).trace = (Psi p B * Gamma (Psi p A)).trace := by
  rw [Phi_Gamma, ← Psi_comp, ← Phi_Gamma, Phi_Psi_duality]

/-- Derived from actual chronology, both dual maps, and branchwise reversal. -/
theorem kernel_form (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u v : HalfHistory) :
    kernel p r hp hp1 hr hr1 u v = form (midpoint p r u) (midpoint p r v) := by
  rw [kernel_trace, central_split]
  rw [form, midpoint_adjoint]
  simp only [midpoint, Gamma, Matrix.mul_assoc]

def synthesis (p r : ℝ) (F : HalfHistory → ℂ) : Mat2 := ∑ u, F u • midpoint p r u

theorem feature_synthesis (p r : ℝ) (F : HalfHistory → ℂ) :
    feature (synthesis p r F) = ∑ u, F u • feature (midpoint p r u) := by
  simp only [feature, synthesis, Matrix.mul_sum, Matrix.sum_mul, mul_smul_comm, smul_mul_assoc]

theorem kernel_posSemidef (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Matrix.PosSemidef (kernel p r hp hp1 hr hr1) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup (1 : Mat2) Matrix.PosSemidef.one
  letI := Matrix.toMatrixInnerProductSpace (1 : Mat2) Matrix.PosSemidef.one
  have hk : kernel p r hp hp1 hr hr1 = Matrix.gram ℂ (fun u => feature (midpoint p r u)) := by
    ext u v
    rw [kernel_form, ← feature_gram]
    change (feature (midpoint p r v) * (feature (midpoint p r u))ᴴ).trace =
      (feature (midpoint p r v) * 1 * (feature (midpoint p r u))ᴴ).trace
    simp
  rw [hk]
  exact Matrix.posSemidef_gram ℂ _

/-- Arbitrary complex coefficients use the square-root-weighted form. -/
theorem pairing_synthesis (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (F G : HalfHistory → ℂ) :
    pairing (kernel p r hp hp1 hr hr1) F G = form (synthesis p r F) (synthesis p r G) := by
  letI := Matrix.toMatrixSeminormedAddCommGroup (1 : Mat2) Matrix.PosSemidef.one
  letI := Matrix.toMatrixInnerProductSpace (1 : Mat2) Matrix.PosSemidef.one
  have hk : kernel p r hp hp1 hr hr1 = Matrix.gram ℂ (fun u => feature (midpoint p r u)) := by
    ext u v
    rw [kernel_form, ← feature_gram]
    change (feature (midpoint p r v) * (feature (midpoint p r u))ᴴ).trace =
      (feature (midpoint p r v) * 1 * (feature (midpoint p r u))ᴴ).trace
    simp
  rw [hk]
  unfold pairing
  rw [Matrix.star_dotProduct_gram_mulVec, ← feature_synthesis, ← feature_synthesis]
  change (feature (synthesis p r G) * 1 * (feature (synthesis p r F))ᴴ).trace = _
  simpa using feature_gram (synthesis p r F) (synthesis p r G)

def PsiLinear (q : ℝ) : Mat2 →ₗ[ℂ] Mat2 where
  toFun := Psi q
  map_add' := Psi_add q
  map_smul' := Psi_smul q

def JLinear (o : Fin 6) : Mat2 →ₗ[ℂ] Mat2 where
  toFun := J o
  map_add' A B := by simp [J, mul_add, add_mul]
  map_smul' z A := by simp [J]

theorem Psi_sum {ι : Type*} [Fintype ι] (q : ℝ) (A : ι → Mat2) :
    Psi q (∑ i, A i) = ∑ i, Psi q (A i) :=
  map_sum (PsiLinear q) A Finset.univ

theorem effect_sum : ∑ o, PauliInstrumentReconstruction.effect o = 1 := by
  simp only [PauliInstrumentReconstruction.effect, ← Finset.smul_sum,
    PauliInstrumentReconstruction.projector_sum, smul_smul]
  norm_num

/-- The actual observable dual is unital, including complete side reset. -/
theorem halfEffect_outer (r : ℝ) (i : Fin 6) :
    ∑ o, halfEffect r (i,o) = PauliInstrumentReconstruction.effect i := by
  change (∑ o, JLinear i (PsiLinear r (PauliInstrumentReconstruction.effect o))) = _
  rw [← map_sum, ← map_sum, effect_sum]
  change J i (Psi r 1) = _
  rw [Psi_unital, J_one]

theorem midpoint_outer (p r : ℝ) (i : Fin 6) :
    ∑ o, midpoint p r (i,o) = Psi p (PauliInstrumentReconstruction.effect i) := by
  simp only [midpoint, ← Psi_sum, halfEffect_outer]

/-- Existing complex Pauli coefficients are used on the inner outcome. -/
theorem synthesis_inner (p r : ℝ) (F : Fin 6 → ℂ) :
    synthesis p r (fun u => F u.1) = Psi p (PauliInstrumentReconstruction.synthesis F) := by
  unfold synthesis
  rw [Fintype.sum_prod_type]
  simp only [← Finset.smul_sum, midpoint_outer, ← Psi_smul, ← Psi_sum]
  rfl

def xMode (u : HalfHistory) : ℂ := PauliInstrumentReconstruction.axisMode 0 u.1

theorem synthesis_xMode_one (r : ℝ) : synthesis 1 r xMode = pauliX := by
  change synthesis 1 r (fun u => PauliInstrumentReconstruction.axisMode 0 u.1) = _
  rw [synthesis_inner, PauliInstrumentReconstruction.synthesis_axisMode, Psi_one]
  rfl

theorem form_x : form pauliX pauliX = 24/25 := by
  rw [form, pauliX_conjTranspose]
  norm_num [pauliX, R, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

/-- A squared norm from the actual kernel, before constructing its quotient. -/
theorem actual_x_pairing_one (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    pairing (kernel 1 r (by norm_num) le_rfl hr hr1) xMode xMode = 24/25 := by
  rw [pairing_synthesis, synthesis_xMode_one, form_x]

theorem old_metric_x : (pauliX * rhoN * pauliXᴴ).trace = 1 := by
  rw [pauliX_conjTranspose]
  norm_num [pauliX, rhoN, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

/-- The actual stationary nontracial kernel has a strictly different X metric. -/
theorem actual_metric_mismatch (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (pairing (kernel 1 r (by norm_num) le_rfl hr hr1) xMode xMode).re <
      (pauliX * rhoN * pauliXᴴ).trace.re := by
  rw [actual_x_pairing_one, old_metric_x]
  norm_num

/-- State and observable actions are genuinely distinct even at reset. -/
theorem reset_actions_distinct : Phi 0 1 ≠ Psi 0 1 := by
  intro h
  have he := congrArg (fun A : Mat2 => A 0 0) h
  norm_num [Phi_zero, Psi_unital, Matrix.trace, Fin.sum_univ_two, rhoN] at he

/-!
The actual four-event kernel reconstructs its complex null quotient through the
Q-sandwich feature. Positive central retention gives the full matrix range;
complete central reset gives the scalar-coordinate line (the R line after the
feature map). The centered Pauli modes, complex mode, literal outer marginal,
and exact norms are consumers of this same process.

Only this fixed faithful qubit state and four events are treated. There is no
arbitrary-state/depth reconstruction, continuum or physical-gap conclusion,
physical-clock identification, postselection, or perturbed-kernel claim.
-/
def synthesisLinear (p r : ℝ) : (HalfHistory → ℂ) →ₗ[ℂ] Mat2 where
  toFun := synthesis p r
  map_add' F G := by simp [synthesis, add_smul, Finset.sum_add_distrib]
  map_smul' z F := by simp [synthesis, Finset.smul_sum, smul_smul]

def featureLinear : Mat2 →ₗ[ℂ] Mat2 where
  toFun := feature
  map_add' A B := by simp [feature, mul_add, add_mul]
  map_smul' z A := by simp [feature]

theorem feature_surjective : Function.Surjective feature :=
  LinearMap.surjective_of_injective (f := featureLinear) feature_injective

theorem synthesis_constant (p r : ℝ) : synthesis p r (fun _ => 1) = 1 := by
  rw [synthesis_inner p r (fun _ => 1), PauliInstrumentReconstruction.synthesis_constant, Psi_unital]

def inversePsi (p : ℝ) (A : Mat2) : Mat2 :=
  (rhoN*A).trace • 1 + (p : ℂ)⁻¹ • (A - (rhoN*A).trace • 1)

theorem mean_centered (A : Mat2) : (rhoN * (A - (rhoN*A).trace • 1)).trace = 0 := by
  simp [mul_sub, Matrix.trace_sub, Matrix.trace_smul, rhoN_trace]

theorem Psi_centered (p : ℝ) (A : Mat2) :
    Psi p (A - (rhoN*A).trace • 1) = (p : ℂ) • (A - (rhoN*A).trace • 1) := by
  rw [Psi, mean_centered]
  simp

theorem Psi_inverse {p : ℝ} (hp : 0 < p) (A : Mat2) : Psi p (inversePsi p A) = A := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  rw [inversePsi, Psi_add, Psi_smul, Psi_unital, Psi_smul, Psi_centered,
    smul_smul, inv_mul_cancel₀ hpC, one_smul]
  module

def coefficients (p : ℝ) (A : Mat2) (u : HalfHistory) : ℂ :=
  PauliInstrumentReconstruction.coefficients (inversePsi p A) u.1

theorem synthesis_coefficients {p : ℝ} (hp : 0 < p) (r : ℝ) (A : Mat2) :
    synthesis p r (coefficients p A) = A := by
  change synthesis p r (fun u => PauliInstrumentReconstruction.coefficients (inversePsi p A) u.1) = _
  rw [synthesis_inner, PauliInstrumentReconstruction.synthesis_coefficients, Psi_inverse hp]

def resetMean (r : ℝ) (F : HalfHistory → ℂ) : ℂ :=
  (rhoN * ∑ u, F u • halfEffect r u).trace

theorem synthesis_full_reset (r : ℝ) (F : HalfHistory → ℂ) :
    synthesis 0 r F = resetMean r F • 1 := by
  simp only [synthesis, midpoint, Psi_zero, resetMean, Matrix.mul_sum,
    mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    Finset.sum_smul, smul_smul]

theorem resetMean_constant (r : ℝ) : resetMean r (fun _ => 1) = 1 := by
  have h := congrArg (fun A : Mat2 => A 0 0) (synthesis_constant 0 r)
  rw [synthesis_full_reset] at h
  simpa using h

/-- New-instrument two-event process at central retention p². -/
def twoTree (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : Tree (Fin 2) Unit 6 2 :=
  .node (step 1 (by norm_num) le_rfl) (fun _ =>
    .node (step (p*p) (mul_nonneg hp hp) (by nlinarith)) (fun _ => .done))

def twoKernel (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i j : Fin 6) : ℂ :=
  (weight (Fin 2) Unit 6 (twoTree p hp hp1) (i,j,())
    (GibbsMultilevelReflection.joint rhoN) : ℂ)

theorem twoKernel_trace (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i j : Fin 6) :
    twoKernel p hp hp1 i j = (PauliInstrumentReconstruction.effect j *
      Phi (p*p) (Gamma (PauliInstrumentReconstruction.effect i))).trace := by
  unfold twoKernel weight
  change (((step (p*p) (mul_nonneg hp hp) (by nlinarith)).branch (Fin 2) Unit 6 j
    ((step 1 (by norm_num) le_rfl).branch (Fin 2) Unit 6 i
      (GibbsMultilevelReflection.joint rhoN))).trace.re : ℂ) = _
  rw [step_branch, step_branch, Phi_one, branch_rhoN,
    GibbsMultilevelReflection.joint_trace, branch_trace]
  apply hermitian_product_real _ _ (effect_adjoint j)
  rw [Phi_Gamma, Gamma_adjoint, Psi_adjoint, effect_adjoint]

theorem Phi_sum {ι : Type*} [Fintype ι] (q : ℝ) (A : ι → Mat2) :
    Phi q (∑ i, A i) = ∑ i, Phi q (A i) := by
  simp [Phi, Matrix.trace_sum, Finset.smul_sum, Finset.sum_smul, Finset.sum_add_distrib]

theorem Gamma_sum {ι : Type*} [Fintype ι] (A : ι → Mat2) :
    Gamma (∑ i, A i) = ∑ i, Gamma (A i) := by
  simp [Gamma, Matrix.mul_sum, Matrix.sum_mul]

/-- Literal summation of both outer labels of the actual four-event weights. -/
theorem outer_marginal (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (i j : Fin 6) :
    ∑ o, ∑ o', kernel p r hp hp1 hr hr1 (i,o) (j,o') = twoKernel p hp hp1 i j := by
  simp_rw [kernel_trace]
  simp only [← Matrix.trace_sum, ← Matrix.sum_mul, halfEffect_outer,
    ← Matrix.mul_sum, ← Phi_sum, ← Gamma_sum]
  rw [twoKernel_trace]

/-- The mean of Z in the fixed faithful state. -/
theorem mean_z : (rhoN * pauliZ).trace = 7/25 := by
  norm_num [rhoN, pauliZ, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

def centeredZ : Mat2 := pauliZ - (7/25 : ℂ) • 1

def innerMode (a : Fin 3) (u : HalfHistory) : ℂ :=
  PauliInstrumentReconstruction.axisMode a u.1 - (if a=2 then (7/25 : ℂ) else 0)

def modeMatrix : Fin 3 → Mat2 := ![pauliX,pauliY,centeredZ]

theorem mode_mean_zero (a : Fin 3) : (rhoN * modeMatrix a).trace = 0 := by
  fin_cases a <;>
    norm_num [modeMatrix, centeredZ, rhoN, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem synthesis_innerMode (p r : ℝ) (a : Fin 3) :
    synthesis p r (innerMode a) = (p : ℂ) • modeMatrix a := by
  have hs : PauliInstrumentReconstruction.synthesis
      (fun o => PauliInstrumentReconstruction.axisMode a o - (if a=2 then (7/25 : ℂ) else 0)) =
      modeMatrix a := by
    change PauliInstrumentReconstruction.synthesisLinear
      (PauliInstrumentReconstruction.axisMode a -
        (fun _ => if a=2 then (7/25 : ℂ) else 0)) = _
    rw [map_sub]
    have hc (c : ℂ) : PauliInstrumentReconstruction.synthesis (fun _ => c) = c • (1 : Mat2) := by
      simp only [PauliInstrumentReconstruction.synthesis, ← Finset.smul_sum, effect_sum]
    change PauliInstrumentReconstruction.synthesis (PauliInstrumentReconstruction.axisMode a) -
      PauliInstrumentReconstruction.synthesis (fun _ => if a=2 then (7/25 : ℂ) else 0) = _
    rw [hc]
    rw [PauliInstrumentReconstruction.synthesis_axisMode]
    fin_cases a <;> simp [modeMatrix, centeredZ, PauliInstrumentReconstruction.sigma]
  change synthesis p r (fun u => PauliInstrumentReconstruction.axisMode a u.1 - _) = _
  rw [synthesis_inner p r (fun o => PauliInstrumentReconstruction.axisMode a o -
    (if a=2 then (7/25 : ℂ) else 0)), hs, Psi, mode_mean_zero]
  simp

theorem form_smul (z w : ℂ) (A B : Mat2) :
    form (z • A) (w • B) = star z * w * form A B := by
  simp [form, Matrix.conjTranspose_smul, Matrix.trace_smul, smul_smul, smul_eq_mul]

def modeNorm : Fin 3 → ℝ := ![24/25,24/25,576/625]

theorem centeredZ_entries : centeredZ = !![18/25,0;0,-32/25] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [centeredZ,pauliZ]

theorem modeMatrix_adjoint (a : Fin 3) : (modeMatrix a)ᴴ = modeMatrix a := by
  fin_cases a <;> simp [modeMatrix, centeredZ, Matrix.conjTranspose_sub,
    pauliX_conjTranspose, pauliY_conjTranspose, pauliZ_conjTranspose]

theorem form_entries (A B : Mat2) :
    form A B = (16/25 : ℂ)*B 0 0*star (A 0 0) + (12/25 : ℂ)*B 0 1*star (A 0 1) +
      (12/25 : ℂ)*B 1 0*star (A 1 0) + (9/25 : ℂ)*B 1 1*star (A 1 1) := by
  simp [form, R, Matrix.mul_apply, Matrix.trace, Matrix.conjTranspose_apply,
    Fin.sum_univ_two]
  ring

theorem modeMatrix_form_00 : form (modeMatrix 0) (modeMatrix 0) = (modeNorm 0 : ℂ) := by
  change form pauliX pauliX = ((24/25 : ℝ) : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]

theorem modeMatrix_form_01 : form (modeMatrix 0) (modeMatrix 1) = 0 := by
  change form pauliX pauliY = (0 : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]

theorem modeMatrix_form_02 : form (modeMatrix 0) (modeMatrix 2) = 0 := by
  change form pauliX centeredZ = (0 : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]

theorem modeMatrix_form_0 (b : Fin 3) :
    form (modeMatrix 0) (modeMatrix b) = if (0 : Fin 3)=b then (modeNorm 0 : ℂ) else 0 := by
  fin_cases b
  · simpa using modeMatrix_form_00
  · simpa using modeMatrix_form_01
  · simpa using modeMatrix_form_02

theorem modeMatrix_form_10 : form (modeMatrix 1) (modeMatrix 0) = 0 := by
  change form pauliY pauliX = (0 : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]

theorem modeMatrix_form_11 : form (modeMatrix 1) (modeMatrix 1) = (modeNorm 1 : ℂ) := by
  change form pauliY pauliY = ((24/25 : ℝ) : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]
  ring_nf
  norm_num [Complex.I_sq]

theorem modeMatrix_form_12 : form (modeMatrix 1) (modeMatrix 2) = 0 := by
  change form pauliY centeredZ = (0 : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]

theorem modeMatrix_form_1 (b : Fin 3) :
    form (modeMatrix 1) (modeMatrix b) = if (1 : Fin 3)=b then (modeNorm 1 : ℂ) else 0 := by
  fin_cases b
  · simpa using modeMatrix_form_10
  · simpa using modeMatrix_form_11
  · simpa using modeMatrix_form_12

theorem modeMatrix_form_20 : form (modeMatrix 2) (modeMatrix 0) = 0 := by
  change form centeredZ pauliX = (0 : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]

theorem modeMatrix_form_21 : form (modeMatrix 2) (modeMatrix 1) = 0 := by
  change form centeredZ pauliY = (0 : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]

theorem modeMatrix_form_22 : form (modeMatrix 2) (modeMatrix 2) = (modeNorm 2 : ℂ) := by
  change form centeredZ centeredZ = ((576/625 : ℝ) : ℂ)
  rw [form_entries]
  norm_num [centeredZ_entries, pauliX, pauliY, Complex.star_def]

theorem modeMatrix_form_2 (b : Fin 3) :
    form (modeMatrix 2) (modeMatrix b) = if (2 : Fin 3)=b then (modeNorm 2 : ℂ) else 0 := by
  fin_cases b
  · simpa using modeMatrix_form_20
  · simpa using modeMatrix_form_21
  · simpa using modeMatrix_form_22

theorem modeMatrix_form (a b : Fin 3) :
    form (modeMatrix a) (modeMatrix b) = if a=b then (modeNorm a : ℂ) else 0 := by
  fin_cases a
  · exact modeMatrix_form_0 b
  · exact modeMatrix_form_1 b
  · exact modeMatrix_form_2 b

theorem constant_mode_form (a : Fin 3) : form 1 (modeMatrix a) = 0 := by
  fin_cases a <;>
    norm_num [form, modeMatrix, centeredZ, R, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem form_one : form 1 1 = 1 := by simpa [form, R_square] using rhoN_trace

def complexMode (u : HalfHistory) : ℂ := innerMode 0 u + Complex.I * innerMode 1 u

theorem synthesis_complexMode (p r : ℝ) :
    synthesis p r complexMode = (p : ℂ) • (pauliX + Complex.I • pauliY) := by
  change synthesisLinear p r (innerMode 0 + Complex.I • innerMode 1) = _
  rw [map_add, map_smul]
  change synthesis p r (innerMode 0) + Complex.I • synthesis p r (innerMode 1) = _
  rw [synthesis_innerMode, synthesis_innerMode]
  change (p : ℂ) • pauliX + Complex.I • ((p : ℂ) • pauliY) = _
  module

theorem complex_mode_form : form (pauliX+Complex.I • pauliY) (pauliX+Complex.I • pauliY) = 48/25 := by
  rw [form_entries]
  norm_num [pauliX, pauliY, Complex.star_def, map_ofNat]

theorem synthesized_commutator (p r : ℝ) :
    synthesis p r (innerMode 0) * synthesis p r (innerMode 1) -
      synthesis p r (innerMode 1) * synthesis p r (innerMode 0) =
      (2*Complex.I*(p : ℂ)^2) • pauliZ := by
  rw [synthesis_innerMode, synthesis_innerMode]
  change ((p : ℂ) • pauliX) * ((p : ℂ) • pauliY) -
    ((p : ℂ) • pauliY) * ((p : ℂ) • pauliX) = _
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem form_self_zero_iff (A : Mat2) : form A A = 0 ↔ A = 0 := by
  constructor
  · intro h
    rw [← feature_gram] at h
    have hz : feature A = 0 := GibbsObservable.trace_weighted_eq_zero
      (show (1 : Mat2).PosDef from Matrix.PosDef.one) _ (by simpa using h)
    apply feature_injective
    simpa [feature] using hz
  · rintro rfl
    simp [form]

section Reconstruction
open scoped InnerProductSpace
/-- Identity weight installs the Hilbert-Schmidt structure, not the entry sup norm. -/
local instance : NormedAddCommGroup Mat2 := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance : InnerProductSpace ℂ Mat2 := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
variable (p r : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)

abbrev Reconstructed := Space (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)

theorem null_iff (F : HalfHistory → ℂ) :
    mk (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) F = 0 ↔
      synthesis p r F = 0 := by
  rw [mk_eq_zero_iff, pairing_synthesis, form_self_zero_iff]

def coefficientSynthesis : Coefficients (kernel_posSemidef p r hp hp1 hr hr1) →ₗ[ℂ] Mat2 :=
  synthesisLinear p r

theorem synthesis_null : nullSpace (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) ≤
    (coefficientSynthesis p r hp hp1 hr hr1).ker := by
  intro F hF
  change synthesis p r F = 0
  apply (null_iff p r hp hp1 hr hr1 F).mp
  rw [mk_eq_zero_iff]
  exact (mem_nullSpace_iff _ _ F).mp hF

/-- Algebraic coordinates descend through exactly the actual kernel null space. -/
def coordinates : Reconstructed p r hp hp1 hr hr1 →ₗ[ℂ] Mat2 :=
  ((nullSpace (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)).liftQ
    (coefficientSynthesis p r hp hp1 hr hr1) (synthesis_null p r hp hp1 hr hr1)).comp
      (quotientEquiv (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1)).symm.toLinearMap

theorem coordinates_mk (F : HalfHistory → ℂ) :
    coordinates p r hp hp1 hr hr1 (mk _ _ F) = synthesis p r F := by
  rw [← quotientEquiv_mk (kernel_posSemidef p r hp hp1 hr hr1) F]
  simp only [coordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  rfl

theorem coordinates_injective : Function.Injective (coordinates p r hp hp1 hr hr1) := by
  intro z w h
  obtain ⟨F,rfl⟩ := mk_surjective _ _ z
  obtain ⟨G,rfl⟩ := mk_surjective _ _ w
  rw [coordinates_mk, coordinates_mk] at h
  apply (mk_eq_mk_iff _ _ F G).mpr
  rw [pairing_synthesis]
  have hz : synthesis p r (F-G) = 0 :=
    (synthesisLinear p r).map_sub F G |>.trans (sub_eq_zero.mpr h)
  simp [hz, form]

theorem coordinates_surjective (hpos : 0 < p) : Function.Surjective (coordinates p r hp hp1 hr hr1) := by
  intro A
  exact ⟨mk _ _ (coefficients p A), by rw [coordinates_mk, synthesis_coefficients hpos]⟩

def coordinateEquiv (hpos : 0 < p) : Reconstructed p r hp hp1 hr hr1 ≃ₗ[ℂ] Mat2 :=
  LinearEquiv.ofBijective (coordinates p r hp hp1 hr hr1)
    ⟨coordinates_injective p r hp hp1 hr hr1, coordinates_surjective p r hp hp1 hr hr1 hpos⟩

theorem reconstructed_finrank (hpos : 0 < p) :
    Module.finrank ℂ (Reconstructed p r hp hp1 hr hr1) = 4 := by
  rw [(coordinateEquiv p r hp hp1 hr hr1 hpos).finrank_eq]
  simpa using Module.finrank_matrix ℂ ℂ (Fin 2) (Fin 2)

def embeddingLinear : Reconstructed p r hp hp1 hr hr1 →ₗ[ℂ] Mat2 :=
  featureLinear.comp (coordinates p r hp hp1 hr hr1)

theorem embeddingLinear_mk (F : HalfHistory → ℂ) :
    embeddingLinear p r hp hp1 hr hr1 (mk _ _ F) = feature (synthesis p r F) := by
  change feature (coordinates p r hp hp1 hr hr1 (mk _ _ F)) = _
  rw [coordinates_mk]

/-- The actual Q-sandwich is isometric for the Hilbert-Schmidt target. -/
def embedding : Reconstructed p r hp hp1 hr hr1 →ₗᵢ[ℂ] Mat2 :=
  (embeddingLinear p r hp hp1 hr hr1).isometryOfInner (by
    intro z w
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [embeddingLinear_mk, embeddingLinear_mk, inner_mk, pairing_synthesis]
    change (feature (synthesis p r G) * 1 * (feature (synthesis p r F))ᴴ).trace = _
    simpa using feature_gram (synthesis p r F) (synthesis p r G))

theorem embedding_mk (F : HalfHistory → ℂ) :
    embedding p r hp hp1 hr hr1 (mk _ _ F) = feature (synthesis p r F) :=
  embeddingLinear_mk p r hp hp1 hr hr1 F

/-- The range consists exactly of Q*S(F)*Q for actual history coefficients. -/
theorem embedding_range : (embedding p r hp hp1 hr hr1).range =
    (featureLinear.comp (synthesisLinear p r)).range := by
  ext A
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    exact ⟨F, (embedding_mk p r hp hp1 hr hr1 F).symm⟩
  · rintro ⟨F,rfl⟩
    exact ⟨mk _ _ F, embedding_mk p r hp hp1 hr hr1 F⟩

/-- An isometric equivalence with the actual matrix range, for all p including zero. -/
def rangeEquiv : Reconstructed p r hp hp1 hr hr1 ≃ₗᵢ[ℂ]
    (embedding p r hp hp1 hr hr1).range := (embedding p r hp hp1 hr hr1).equivRange

theorem embedding_surjective (hpos : 0 < p) : Function.Surjective (embedding p r hp hp1 hr hr1) := by
  intro A
  obtain ⟨B,rfl⟩ := feature_surjective A
  refine ⟨mk _ _ (coefficients p B), ?_⟩
  rw [embedding_mk, synthesis_coefficients hpos]

theorem full_matrix_range (hpos : 0 < p) : (embedding p r hp hp1 hr hr1).range = ⊤ :=
  LinearMap.range_eq_top.mpr (embedding_surjective p r hp hp1 hr hr1 hpos)

theorem reset_null_iff (F : HalfHistory → ℂ) :
    mk (kernel 0 r (by norm_num) (by norm_num) hr hr1)
      (kernel_posSemidef 0 r (by norm_num) (by norm_num) hr hr1) F = 0 ↔ resetMean r F = 0 := by
  rw [null_iff, synthesis_full_reset]
  constructor
  · intro h
    have he := congrArg (fun A : Mat2 => A 0 0) h
    simpa using he
  · intro h
    simp [h]

def resetCoordinates : Reconstructed 0 r (by norm_num) (by norm_num) hr hr1 →ₗ[ℂ] ℂ where
  toFun z := coordinates 0 r (by norm_num) (by norm_num) hr hr1 z 0 0
  map_add' z w := by simp
  map_smul' c z := by simp

theorem resetCoordinates_mk (F : HalfHistory → ℂ) :
    resetCoordinates r hr hr1 (mk _ _ F) = resetMean r F := by
  change coordinates 0 r (by norm_num) (by norm_num) hr hr1 (mk _ _ F) 0 0 = _
  rw [coordinates_mk, synthesis_full_reset]
  simp

theorem resetCoordinates_bijective : Function.Bijective (resetCoordinates r hr hr1) := by
  constructor
  · intro z w h
    apply coordinates_injective 0 r (by norm_num) (by norm_num) hr hr1
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    obtain ⟨G,rfl⟩ := mk_surjective _ _ w
    rw [resetCoordinates_mk, resetCoordinates_mk] at h
    rw [coordinates_mk, coordinates_mk, synthesis_full_reset, synthesis_full_reset, h]
  · intro c
    refine ⟨c • mk _ _ (fun _ => 1), ?_⟩
    rw [map_smul, resetCoordinates_mk, resetMean_constant]
    simp

def resetCoordinateEquiv : Reconstructed 0 r (by norm_num) (by norm_num) hr hr1 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (resetCoordinates r hr hr1) (resetCoordinates_bijective r hr hr1)

theorem reset_finrank : Module.finrank ℂ (Reconstructed 0 r (by norm_num) (by norm_num) hr hr1) = 1 := by
  rw [(resetCoordinateEquiv r hr hr1).finrank_eq]
  exact Module.finrank_self ℂ

theorem reset_embedding (F : HalfHistory → ℂ) :
    embedding 0 r (by norm_num) (by norm_num) hr hr1 (mk _ _ F) = resetMean r F • R := by
  rw [embedding_mk, synthesis_full_reset]
  simp [feature, Q_square]

theorem reset_matrix_range : (embedding 0 r (by norm_num) (by norm_num) hr hr1).range =
    Submodule.span ℂ {R} := by
  ext A
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨F,rfl⟩ := mk_surjective _ _ z
    exact ⟨resetMean r F, (reset_embedding r hr hr1 F).symm⟩
  · rintro ⟨c,rfl⟩
    refine ⟨c • mk _ _ (fun _ => 1), ?_⟩
    rw [map_smul]
    change c • embedding 0 r (by norm_num) (by norm_num) hr hr1 (mk _ _ (fun _ => 1)) = _
    rw [reset_embedding, resetMean_constant, one_smul]

theorem innerMode_pairing (a b : Fin 3) :
    pairing (kernel p r hp hp1 hr hr1) (innerMode a) (innerMode b) =
      if a=b then (modeNorm a : ℂ)*(p : ℂ)^2 else 0 := by
  rw [pairing_synthesis, synthesis_innerMode, synthesis_innerMode, form_smul, modeMatrix_form]
  simp only [Complex.star_def, Complex.conj_ofReal]
  split_ifs <;> ring

theorem innerMode_norm_sq (a : Fin 3) :
    ‖mk (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) (innerMode a)‖^2 =
      modeNorm a * p^2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_mk, innerMode_pairing, if_pos rfl]
  simp [← Complex.ofReal_pow]

theorem constant_pairing : pairing (kernel p r hp hp1 hr hr1) (fun _ => 1) (fun _ => 1) = 1 := by
  rw [pairing_synthesis, synthesis_constant, form_one]

theorem constant_norm_sq :
    ‖mk (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) (fun _ => 1)‖^2 = 1 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_mk, constant_pairing]
  rfl

theorem constant_innerMode_pairing (a : Fin 3) :
    pairing (kernel p r hp hp1 hr hr1) (fun _ => 1) (innerMode a) = 0 := by
  rw [pairing_synthesis, synthesis_constant, synthesis_innerMode]
  have h := form_smul 1 (p : ℂ) 1 (modeMatrix a)
  simpa [constant_mode_form] using h

theorem complexMode_pairing :
    pairing (kernel p r hp hp1 hr hr1) complexMode complexMode = (48/25 : ℂ)*(p : ℂ)^2 := by
  rw [pairing_synthesis, synthesis_complexMode, form_smul, complex_mode_form]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

theorem complexMode_norm_sq :
    ‖mk (kernel p r hp hp1 hr hr1) (kernel_posSemidef p r hp hp1 hr hr1) complexMode‖^2 =
      (48/25 : ℝ)*p^2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_mk, complexMode_pairing]
  simp [← Complex.ofReal_pow]

theorem side_reset_positive_x :
    ‖mk (kernel (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (kernel_posSemidef (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (innerMode 0)‖^2 =
      (6/25 : ℝ) ∧ (0 : ℝ) < 6/25 := by
  rw [innerMode_norm_sq]
  norm_num [modeNorm]

theorem reset_modes_null (a : Fin 3) :
    mk (kernel 0 r (by norm_num) (by norm_num) hr hr1)
      (kernel_posSemidef 0 r (by norm_num) (by norm_num) hr hr1) (innerMode a) = 0 := by
  rw [null_iff, synthesis_innerMode]
  simp

theorem image_commutator_nonzero (hpos : 0 < p) :
    synthesis p r (innerMode 0) * synthesis p r (innerMode 1) -
      synthesis p r (innerMode 1) * synthesis p r (innerMode 0) ≠ 0 := by
  rw [synthesized_commutator]
  intro h
  have he := congrArg (fun A : Mat2 => (A 0 0).im) h
  norm_num [pauliZ, Complex.mul_im, Complex.mul_re, pow_two] at he
  nlinarith

/-- Sum of the actual chronological weights, including impossible outcomes. -/
theorem kernel_total : ∑ u, ∑ v, kernel p r hp hp1 hr hr1 u v = 1 := by
  have h := constant_pairing p r hp hp1 hr hr1
  simpa [pairing, dotProduct, Matrix.mulVec] using h

theorem joint_density : IsDensityOperator (GibbsMultilevelReflection.joint rhoN) := by
  refine ⟨rhoN_density.1.kronecker Matrix.PosSemidef.one, ?_⟩
  rw [GibbsMultilevelReflection.joint_trace, rhoN_trace]

theorem actual_probabilities :
    (∀ h, 0 ≤ weight (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) h
      (GibbsMultilevelReflection.joint rhoN)) ∧
    (∑ h, weight (Fin 2) Unit 6 (fourTree p r hp hp1 hr hr1) h
      (GibbsMultilevelReflection.joint rhoN)) = 1 :=
  normalized_weights (Fin 2) Unit 6 _ joint_density

theorem kernel_entry_nonnegative (u v : HalfHistory) : 0 ≤ (kernel p r hp hp1 hr hr1 u v).re :=
  (actual_probabilities p r hp hp1 hr hr1).1 _

end Reconstruction

/-- Endpoint channel actions are actual Kraus evaluations and require no inverses. -/
theorem channel_endpoints (A : Mat2) :
    krausMap (channel 0) A = A.trace • rhoN ∧
    krausMap (channel 1) A = A ∧
    Channel.heisenberg (channel 0) A = (rhoN*A).trace • 1 ∧
    Channel.heisenberg (channel 1) A = A := by
  rw [channel_state (by norm_num) (by norm_num),
    channel_state (by norm_num) (by norm_num),
    channel_observable (by norm_num) (by norm_num),
    channel_observable (by norm_num) (by norm_num), Phi_zero, Phi_one, Psi_zero, Psi_one]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem side_reset_halfEffect (u : HalfHistory) :
    halfEffect 0 u = (rhoN * PauliInstrumentReconstruction.effect u.2).trace •
      PauliInstrumentReconstruction.effect u.1 := by
  rw [halfEffect, Psi_zero]
  change JLinear u.1 (_ • 1) = _
  rw [map_smul]
  change _ • J u.1 1 = _
  rw [J_one]

theorem side_identity_halfEffect (u : HalfHistory) :
    halfEffect 1 u = J u.1 (PauliInstrumentReconstruction.effect u.2) := by
  rw [halfEffect, Psi_one]

/-- Explicit full complex expansion in the centered Pauli matrices. -/
theorem matrix_mode_decomposition (A : Mat2) :
    ∃ z0 zx zy zz : ℂ, A = z0 • (1 : Mat2) + zx • pauliX + zy • pauliY + zz • centeredZ := by
  let F := PauliInstrumentReconstruction.coefficients A
  have h := PauliInstrumentReconstruction.synthesis_decomposition F
  rw [PauliInstrumentReconstruction.synthesis_coefficients] at h
  refine ⟨(∑ o, F o)/6 + (7/25 : ℂ)*(PauliInstrumentReconstruction.difference F 2/6),
    PauliInstrumentReconstruction.difference F 0/6,
    PauliInstrumentReconstruction.difference F 1/6,
    PauliInstrumentReconstruction.difference F 2/6, ?_⟩
  rw [h, centeredZ]
  module

def fourMode : Fin 4 → HalfHistory → ℂ := ![fun _ => 1, innerMode 0, innerMode 1, innerMode 2]

theorem fourMode_spans {p : ℝ} (hp : 0 < p) (r : ℝ) (A : Mat2) :
    ∃ c : Fin 4 → ℂ, ∑ i, c i • synthesis p r (fourMode i) = A := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  obtain ⟨z0,zx,zy,zz,hA⟩ := matrix_mode_decomposition A
  refine ⟨![z0,zx/(p : ℂ),zy/(p : ℂ),zz/(p : ℂ)], ?_⟩
  rw [Fin.sum_univ_four]
  change z0 • synthesis p r (fun _ => 1) +
    (zx/(p : ℂ)) • synthesis p r (innerMode 0) +
    (zy/(p : ℂ)) • synthesis p r (innerMode 1) +
    (zz/(p : ℂ)) • synthesis p r (innerMode 2) = A
  rw [synthesis_constant, synthesis_innerMode, synthesis_innerMode, synthesis_innerMode]
  simp only [smul_smul, div_mul_cancel₀ _ hpC]
  exact hA.symm

theorem fourMode_span {p : ℝ} (hp : 0 < p) (r : ℝ) :
    Submodule.span ℂ (Set.range (fun i => synthesis p r (fourMode i))) = ⊤ := by
  apply top_unique
  intro A _
  obtain ⟨c,hc⟩ := fourMode_spans hp r A
  rw [← hc]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))


/-- The new and old instruments share effects, but their selected output states differ. -/
theorem selected_output_differs : instrument.branch 0 rhoN ≠
    PauliInstrumentReconstruction.instrument.branch 0 rhoN := by
  intro h
  rw [branch_rhoN, PauliInstrumentReconstruction.instrument_branch] at h
  have he := congrArg (fun A : Mat2 => A 0 0) h
  norm_num [Gamma, R, rhoN, PauliInstrumentReconstruction.effect,
    PauliInstrumentReconstruction.projector, PauliInstrumentReconstruction.sign,
    PauliInstrumentReconstruction.outcomeEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat,
    PauliInstrumentReconstruction.sigma, pauliX, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.vecMul, dotProduct] at he

theorem step_endpoints (o : Fin 6) (A : Mat2) :
    (step 0 (by norm_num) (by norm_num)).branch (Fin 2) Unit 6 o
      (GibbsMultilevelReflection.joint A) =
      GibbsMultilevelReflection.joint (instrument.branch o (A.trace • rhoN)) ∧
    (step 1 (by norm_num) (by norm_num)).branch (Fin 2) Unit 6 o
      (GibbsMultilevelReflection.joint A) =
      GibbsMultilevelReflection.joint (instrument.branch o A) := by
  rw [step_branch, step_branch, Phi_zero, Phi_one]
  exact ⟨rfl,rfl⟩

end SKEFTHawking.QuantumNetwork.NontracialPauliReflection
