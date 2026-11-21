import SKEFTHawking.ContinuousRetainedModular
import SKEFTHawking.QuantumNetwork.FiniteClockHandReadout

/-! The projective clock-hand law evaluated on the retained Gibbs modular group. -/
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
open QuantumNetwork GibbsObservable FiniteGibbsClock DiagonalLindblad
open QuantumNetwork.FiniteClockHandReadout (H H_hermitian Q U U_adjoint rhoPlus rho mass born p p_zero
  p_keep p_reflection)

section PreparedGibbsExpectation

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {H₀ : Matrix n n ℂ} (hH₀ : H₀.IsHermitian) (β : ℝ)

private def faithfulObservableEquiv : Matrix n n ℂ ≃ₗ[ℂ] GibbsSpace H₀ hH₀ β := by
  let hρ := gibbs_posDef hH₀ β
  exact LinearEquiv.ofBijective (observableLinear hρ.posSemidef)
    ⟨observable_injective hρ, observable_surjective hρ.posSemidef⟩

/-- The real expectation of the reconstructed observable in an independently prepared state. -/
def preparedGibbsExpectation (ρ : Matrix n n ℂ) (z : GibbsSpace H₀ hH₀ β) : ℝ :=
  (((faithfulObservableEquiv hH₀ β).symm z * ρ).trace).re

theorem preparedGibbsExpectation_observable (ρ X : Matrix n n ℂ) :
    preparedGibbsExpectation hH₀ β ρ
      (observable (gibbs_posDef hH₀ β).posSemidef X) = (X * ρ).trace.re := by
  change (((faithfulObservableEquiv hH₀ β).symm
    ((faithfulObservableEquiv hH₀ β) X) * ρ).trace).re = _
  rw [LinearEquiv.symm_apply_apply]

theorem preparedGibbsExpectation_continuous (ρ : Matrix n n ℂ) :
    Continuous (preparedGibbsExpectation hH₀ β ρ) := by
  let traceEval := (Matrix.traceLinearMap n ℂ ℂ).comp
    ((LinearMap.mulRight ℂ ρ).comp (faithfulObservableEquiv hH₀ β).symm.toLinearMap)
  change Continuous (fun z => (traceEval z).re)
  exact Complex.continuous_re.comp traceEval.continuous_of_finiteDimensional

end PreparedGibbsExpectation

/-- Evaluate a vector in the faithful two-level Gibbs space in the independently prepared hand. -/
def preparedClockReadout (ω ℏ β : ℝ) (z : GibbsSpace (H ω ℏ) (H_hermitian ω ℏ) β) : ℝ :=
  preparedGibbsExpectation (H_hermitian ω ℏ) β rhoPlus z

theorem preparedClockReadout_observable (ω ℏ β : ℝ) (X : QuantumNetwork.FiniteClockHandReadout.Mat) :
    preparedClockReadout ω ℏ β
      (observable (gibbs_posDef (H_hermitian ω ℏ) β).posSemidef X) = (X * rhoPlus).trace.re :=
  preparedGibbsExpectation_observable (H_hermitian ω ℏ) β rhoPlus X

theorem preparedClockReadout_continuous (ω ℏ β : ℝ) :
    Continuous (preparedClockReadout ω ℏ β) :=
  preparedGibbsExpectation_continuous (H_hermitian ω ℏ) β rhoPlus

/-- Time continuity of the retained group passes to the prepared readout. -/
theorem retainedModular_clockHand_readout_continuous {κ : Type*} [Fintype κ]
    (ell : κ → Fin 2 → ℝ) (ω ℏ β : ℝ) (hH : H ω ℏ ∈ fixedAlgebra ell)
    (z : retainedGibbsSpace ell (H_hermitian ω ℏ) hH β) :
    Continuous (fun s => preparedClockReadout ω ℏ β
      (retainedModular ell (H_hermitian ω ℏ) hH β s z).1) :=
  (preparedClockReadout_continuous ω ℏ β).comp (continuous_subtype_val.comp
    (retainedModular_time_continuous ell (H_hermitian ω ℏ) hH β z))

private theorem clock_heisenberg_adjoint {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ)
    (X : QuantumNetwork.FiniteClockHandReadout.Mat) :
    heisenberg (H ω ℏ) ℏ t X = (U ω ℏ t)ᴴ * X * U ω ℏ t := by
  rw [U_adjoint hℏ]
  simp [heisenberg, conjugate, U, neg_div]

/-- Trace cyclicity turns the Heisenberg projector into the actual Born law
of the prepared state at the dimensionful physical time. -/
theorem clockHand_heisenberg_born {ℏ : ℝ} (hℏ : ℏ ≠ 0) (ω t : ℝ) (a : Fin 2) :
    (heisenberg (H ω ℏ) ℏ t (Q a) * rhoPlus).trace.re = mass ω t a := by
  rw [clock_heisenberg_adjoint hℏ, ← born hℏ]
  unfold rho
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (U ω ℏ t)ᴴ]
  simp only [Matrix.mul_assoc]

/-- Whenever the readout projector is in the fixed block algebra, evaluating
its retained modular orbit in the prepared state gives the same Born law. -/
theorem retainedModular_clockHand_born {κ : Type*} [Fintype κ] (ell : κ → Fin 2 → ℝ)
    (ω ℏ β s : ℝ) (hℏ : 0 < ℏ) (a : Fin 2)
    (hH : H ω ℏ ∈ fixedAlgebra ell) (hQ : Q a ∈ fixedAlgebra ell) :
    let z : retainedGibbsSpace ell (H_hermitian ω ℏ) hH β :=
      ⟨observable (gibbs_posDef (H_hermitian ω ℏ) β).posSemidef (Q a),
        (observable_mem_retainedGibbsSpace ell (H_hermitian ω ℏ) hH β (Q a)).mpr hQ⟩
    preparedClockReadout ω ℏ β (retainedModular ell (H_hermitian ω ℏ) hH β s z).1 =
      mass ω (-β * ℏ * s) a := by
  change preparedClockReadout ω ℏ β (Clock.quotientModular (H_hermitian ω ℏ) β s
    (observable (gibbs_posDef (H_hermitian ω ℏ) β).posSemidef (Q a))) = _
  rw [Clock.quotientModular_eq_heisenberg _ _ _ _ hℏ, preparedClockReadout_observable]
  exact clockHand_heisenberg_born hℏ.ne' ω _ a

private def commonSignature : Fin 1 → Fin 2 → ℝ := fun _ _ => 0

private theorem commonSignature_fixed (X : QuantumNetwork.FiniteClockHandReadout.Mat) :
    X ∈ fixedAlgebra commonSignature := by
  change blockExpectation commonSignature X = X
  ext i j
  rw [expectation_entry, if_pos ((blockClass_eq_iff _ i j).2 (fun _ => rfl))]

/-- The same retained projector gives probability zero initially and probability
one after a modular half-turn, using a fixed state preparation. -/
theorem retained_clockHand_halfTurn :
    let hH := commonSignature_fixed (H 1 1)
    let z : retainedGibbsSpace commonSignature (H_hermitian 1 1) hH 1 :=
      ⟨observable (gibbs_posDef (H_hermitian 1 1) 1).posSemidef (Q 0),
        (observable_mem_retainedGibbsSpace commonSignature (H_hermitian 1 1) hH 1 (Q 0)).mpr
          (commonSignature_fixed (Q 0))⟩
    preparedClockReadout 1 1 1 (retainedModular commonSignature (H_hermitian 1 1) hH 1 0 z).1 = 0 ∧
      preparedClockReadout 1 1 1
        (retainedModular commonSignature (H_hermitian 1 1) hH 1 Real.pi z).1 = 1 := by
  dsimp only
  have h (s : ℝ) := retainedModular_clockHand_born commonSignature 1 1 1 s (by norm_num) 0
    (commonSignature_fixed (H 1 1)) (commonSignature_fixed (Q 0))
  constructor
  · rw [h 0]
    norm_num [mass, p]
  · rw [h Real.pi]
    change p 1 (-1 * 1 * Real.pi) = 1
    rw [show -1 * 1 * Real.pi = -(Real.pi / 1) by ring, p_reflection]
    exact p_keep (by norm_num)

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation
