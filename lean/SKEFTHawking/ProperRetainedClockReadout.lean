import SKEFTHawking.RetainedGibbsClockReadout

/-! A clock hand supported in a proper three-level retained sector. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
open QuantumNetwork GibbsObservable FiniteGibbsClock DiagonalLindblad

open QuantumNetwork.FiniteClockHandReadout (rhoPlus rhoPlus_density Q Q_adjoint Q_mul Q_complete
  mass p p_keep p_reflection)

abbrev Level := Fin 2 ⊕ Unit
abbrev Mat := Matrix Level Level ℂ

/-- Zero extension of the hand to the doublet in the three-level carrier. -/
def corner (X : Matrix (Fin 2) (Fin 2) ℂ) : Mat := Matrix.fromBlocks X 0 0 0

private theorem corner_mul (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    corner X * corner Y = corner (X * Y) := by
  ext i j
  cases i <;> cases j <;> simp [corner, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem corner_trace (X : Matrix (Fin 2) (Fin 2) ℂ) : (corner X).trace = X.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type, corner]

private theorem corner_adjoint (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (corner X)ᴴ = corner Xᴴ := by
  ext i j
  cases i <;> cases j <;> simp [corner, Matrix.conjTranspose_apply]

/-- The prepared hand is supported in the doublet and has trace one in the ambient space. -/
def prepared : Mat := corner rhoPlus

theorem prepared_density : IsDensityOperator prepared := by
  let v' : Level → ℂ := Sum.elim QuantumNetwork.FiniteClockHandReadout.v (fun _ => 0)
  have he : prepared = Matrix.vecMulVec v' (star v') := by
    ext i j
    cases i <;> cases j <;> simp [prepared, corner, rhoPlus, Matrix.vecMulVec, v']
  exact ⟨he ▸ Matrix.posSemidef_vecMulVec_self_star v', (corner_trace rhoPlus).trans rhoPlus_density.2⟩

/-- The two projective hand events, extended by zero on the spectator. -/
def event (a : Fin 2) : Mat := corner (Q a)

theorem event_adjoint (a : Fin 2) : (event a)ᴴ = event a := by
  rw [event, corner_adjoint, Q_adjoint]

theorem event_mul (a b : Fin 2) : event a * event b = if a = b then event a else 0 := by
  rw [event, event, corner_mul, Q_mul]
  split
  · rfl
  · ext i j
    cases i <;> cases j <;> simp [corner]

/-- The spectator is an orthogonal third outcome completing the two hand events. -/
def spectator : Mat := Matrix.fromBlocks 0 0 0 1

theorem readout_complete : (∑ a : Fin 2, event a) + spectator = 1 := by
  ext i j
  cases i <;> cases j
  · rename_i i j
    have h := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X i j) Q_complete
    simpa [event, corner, spectator, Matrix.one_apply, Fin.sum_univ_two] using h
  all_goals simp [event, corner, spectator, Fin.sum_univ_two]

/-- The doublet has equal signatures and the spectator is in its own block. -/
def signatures : Fin 1 → Level → ℝ := fun _ => Sum.elim (fun _ => 0) (fun _ => 1)

private theorem corner_fixed (X : Matrix (Fin 2) (Fin 2) ℂ) : corner X ∈ fixedAlgebra signatures := by
  change blockExpectation signatures (corner X) = corner X
  ext i j
  rw [expectation_entry]
  cases i <;> cases j
  · rename_i i j
    have h : blockClass signatures (Sum.inl i) = blockClass signatures (Sum.inl j) :=
      (blockClass_eq_iff signatures _ _).2 (fun _ => rfl)
    simp only [h, if_true]
  all_goals simp [corner]

theorem spectator_adjoint : spectatorᴴ = spectator := by
  ext i j
  cases i <;> cases j <;> simp [spectator, Matrix.conjTranspose_apply]

theorem spectator_mul_self : spectator * spectator = spectator := by
  ext i j
  cases i <;> cases j <;> simp [spectator, Matrix.mul_apply, Fintype.sum_sum_type]

theorem event_mul_spectator (a : Fin 2) : event a * spectator = 0 := by
  ext i j
  cases i <;> cases j <;> simp [event, corner, spectator, Matrix.mul_apply, Fintype.sum_sum_type]

theorem spectator_mul_event (a : Fin 2) : spectator * event a = 0 := by
  have h := congrArg Matrix.conjTranspose (event_mul_spectator a)
  simpa only [Matrix.conjTranspose_mul, spectator_adjoint, event_adjoint,
    Matrix.conjTranspose_zero] using h

private def energies (ω ℏ E : ℝ) : Level → ℂ :=
  Sum.elim (![0, ((ℏ * ω : ℝ) : ℂ)] : Fin 2 → ℂ) (fun _ => E)

/-- A two-level hand and an uncoupled spectator of arbitrary energy. -/
def hamiltonian (ω ℏ E : ℝ) : Mat := Matrix.diagonal (energies ω ℏ E)

theorem hamiltonian_hermitian (ω ℏ E : ℝ) : (hamiltonian ω ℏ E).IsHermitian := by
  change (Matrix.diagonal (energies ω ℏ E))ᴴ = Matrix.diagonal (energies ω ℏ E)
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases h : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    cases i with
    | inl i => fin_cases i <;> simp [energies]
    | inr _ => simp [energies]
  · rw [Matrix.diagonal_apply_ne _ (show j ≠ i from fun e => h e.symm), Matrix.diagonal_apply_ne _ h, star_zero]

private theorem diagonal_fixed (d : Level → ℂ) : Matrix.diagonal d ∈ fixedAlgebra signatures := by
  change blockExpectation signatures (Matrix.diagonal d) = Matrix.diagonal d
  ext i j
  rw [expectation_entry]
  by_cases h : i = j
  · subst j
    simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem hamiltonian_fixed (ω ℏ E : ℝ) : hamiltonian ω ℏ E ∈ fixedAlgebra signatures :=
  diagonal_fixed (energies ω ℏ E)

theorem spectator_fixed : spectator ∈ fixedAlgebra signatures := by
  have h : spectator = Matrix.diagonal (Sum.elim (fun (_ : Fin 2) => (0 : ℂ)) (fun (_ : Unit) => 1)) := by
    ext i j
    cases i <;> cases j <;> simp [spectator, Matrix.diagonal_apply]
  rw [h]
  exact diagonal_fixed _

private theorem corner_heisenberg (ω ℏ E t : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    heisenberg (hamiltonian ω ℏ E) ℏ t (corner X) =
      corner (heisenberg (QuantumNetwork.FiniteClockHandReadout.H ω ℏ) ℏ t X) := by
  unfold heisenberg hamiltonian QuantumNetwork.FiniteClockHandReadout.H twoLevel
  ext i j
  cases i <;> cases j <;> simp [diagonal_conjugate_entry, corner, energies]

/-- The spectator outcome has zero probability for the prepared hand at all physical times. -/
theorem spectator_dark (ω ℏ E t : ℝ) :
    (heisenberg (hamiltonian ω ℏ E) ℏ t spectator * prepared).trace = 0 := by
  have hs : heisenberg (hamiltonian ω ℏ E) ℏ t spectator = spectator := by
    unfold heisenberg hamiltonian
    ext i j
    cases i <;> cases j <;> simp [diagonal_conjugate_entry, spectator, energies]
  rw [hs]
  have hp : spectator * prepared = 0 := by
    ext i j
    cases i <;> cases j <;> simp [spectator, prepared, corner, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [hp, Matrix.trace_zero]

theorem sector_proper (ω ℏ E β : ℝ) :
    retainedGibbsSpace signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β ≠ ⊤ := by
  intro htop
  let X : Mat := Matrix.single (Sum.inl 0) (Sum.inr ()) 1
  let hρ := gibbs_posDef (hamiltonian_hermitian ω ℏ E) β
  have hm : observable hρ.posSemidef X ∈
      retainedGibbsSpace signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β := by
    rw [htop]
    trivial
  have hf := (observable_mem_retainedGibbsSpace signatures
    (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β X).mp hm
  have hd : blockClass signatures (Sum.inl 0) ≠ blockClass signatures (Sum.inr ()) := by
    intro h
    have hx := (blockClass_eq_iff _ _ _).mp h (0 : Fin 1)
    norm_num [signatures] at hx
  have hz := fixed_entry_zero signatures X hf (Sum.inl 0) (Sum.inr ()) hd
  norm_num [X, Matrix.single] at hz

private def retainedObservable (ω ℏ E β : ℝ) (X : Mat) (hX : X ∈ fixedAlgebra signatures) :
    retainedGibbsSpace signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β :=
  ⟨observable (gibbs_posDef (hamiltonian_hermitian ω ℏ E) β).posSemidef X,
    (observable_mem_retainedGibbsSpace signatures
      (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β X).mpr hX⟩

/-- Each hand projector belongs to the reconstructed proper retained space. -/
def eventVector (ω ℏ E β : ℝ) (a : Fin 2) :
    retainedGibbsSpace signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β :=
  retainedObservable ω ℏ E β (event a) (corner_fixed (Q a))

/-- The third projector also belongs to the same retained space. -/
def spectatorVector (ω ℏ E β : ℝ) :
    retainedGibbsSpace signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β :=
  retainedObservable ω ℏ E β spectator spectator_fixed

/-- A physical hand event in the proper retained sector has the original Born law
under the actual modular evolution, at every spectator energy. -/
theorem retained_born (ω ℏ E β s : ℝ) (hℏ : 0 < ℏ) (a : Fin 2) :
    preparedGibbsExpectation (hamiltonian_hermitian ω ℏ E) β prepared
      (retainedModular signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β s
        (eventVector ω ℏ E β a)).1 = mass ω (-β * ℏ * s) a := by
  change preparedGibbsExpectation (hamiltonian_hermitian ω ℏ E) β prepared
    (Clock.quotientModular (hamiltonian_hermitian ω ℏ E) β s
      (observable (gibbs_posDef (hamiltonian_hermitian ω ℏ E) β).posSemidef (event a))) = _
  rw [Clock.quotientModular_eq_heisenberg _ _ _ _ hℏ, preparedGibbsExpectation_observable,
    event, corner_heisenberg, prepared, corner_mul, corner_trace]
  exact clockHand_heisenberg_born hℏ.ne' ω _ a

/-- The third outcome has zero readout along its actual retained modular orbit. -/
theorem retained_spectator_dark (ω ℏ E β s : ℝ) (hℏ : 0 < ℏ) :
    preparedGibbsExpectation (hamiltonian_hermitian ω ℏ E) β prepared
      (retainedModular signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β s
        (spectatorVector ω ℏ E β)).1 = 0 := by
  change preparedGibbsExpectation (hamiltonian_hermitian ω ℏ E) β prepared
    (Clock.quotientModular (hamiltonian_hermitian ω ℏ E) β s
      (observable (gibbs_posDef (hamiltonian_hermitian ω ℏ E) β).posSemidef spectator)) = _
  rw [Clock.quotientModular_eq_heisenberg _ _ _ _ hℏ, preparedGibbsExpectation_observable,
    spectator_dark, Complex.zero_re]

/-- Strong modular continuity gives a continuous readout on the proper sector. -/
theorem retained_readout_continuous (ω ℏ E β : ℝ)
    (z : retainedGibbsSpace signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β) :
    Continuous (fun s => preparedGibbsExpectation (hamiltonian_hermitian ω ℏ E) β prepared
      (retainedModular signatures (hamiltonian_hermitian ω ℏ E) (hamiltonian_fixed ω ℏ E) β s z).1) :=
  (preparedGibbsExpectation_continuous (hamiltonian_hermitian ω ℏ E) β prepared).comp
    (continuous_subtype_val.comp
      (retainedModular_time_continuous signatures (hamiltonian_hermitian ω ℏ E)
        (hamiltonian_fixed ω ℏ E) β z))

/-- Exact probabilities at zero and a half-turn in the proper three-level sector. -/
theorem retained_halfTurn (E : ℝ) :
    let readout := fun s =>
      preparedGibbsExpectation (hamiltonian_hermitian 1 1 E) 1 prepared
        (retainedModular signatures (hamiltonian_hermitian 1 1 E) (hamiltonian_fixed 1 1 E) 1 s
          (eventVector 1 1 E 1 0)).1
    readout 0 = 0 ∧ readout Real.pi = 1 := by
  dsimp only
  constructor
  · rw [retained_born _ _ _ _ _ (by norm_num)]
    norm_num [mass, p]
  · rw [retained_born _ _ _ _ _ (by norm_num)]
    change p 1 (-1 * 1 * Real.pi) = 1
    rw [show -1 * 1 * Real.pi = -(Real.pi / 1) by ring, p_reflection]
    exact p_keep (by norm_num)

end SKEFTHawking.FinitePositiveKernel.BlockConditionalExpectation.ProperClock
