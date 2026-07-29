import SKEFTHawking.GKSLStructure
import SKEFTHawking.QuantumNetwork.NumericalBounds

/-!
# Damped two-level system: a certified GKSL model (Phase 6BC, Wave 4)

A concrete instance of the GKSL generator: a two-level system (`d = Fin 2`, ground `|0⟩`, excited
`|1⟩`) undergoing spontaneous emission at rate `γ`, with no Hamiltonian drive (`H = 0`) and a single
jump operator `L = √γ σ₋`, where `σ₋ = |0⟩⟨1|` is the lowering operator
(`dampedTwoLevelGenerator`). This is the textbook amplitude-damping / `T₁`-relaxation model.

* **Decay rate from the generator** (`dampedTwoLevel_generator_decay_rate`) — the excited-state
  population entry obeys `(ℒρ)₁₁ = −γ·ρ₁₁`: the generator drives `ṗ_e = −γ p_e`, the defining
  property of relaxation at rate `γ`. This is computed directly from the GKSL canonical form
  (Wave 2), so the model genuinely instantiates the abstract generator.
* **Certified decay envelope** (`dampedTwoLevel_decay_envelope`) — the population decay factor
  `e^{−γt}` (the solution `p_e(t) = p_e(0) e^{−γt}` of the rate equation) admits the **rational
  enclosure** `1 − γt ≤ e^{−γt} ≤ 1/(1+γt)` with no floating-point `exp`, via the project's
  `expNeg_enclosure` Bernoulli bracket. `dampedTwoLevel_decay_envelope_half` is a worked
  `norm_num`-backed operating point at `γt = ½`: `e^{−1/2} ∈ [½, ⅔]`.

**Two-layer honesty.** The generator algebra and the decay-factor enclosure are Lean-verified. The
identification of `√γ σ₋` with a specific physical bath/transition (which atomic line, which emission
channel) is the literature-cited modelling input; here `γ ≥ 0` is an abstract rate.

Invariants (Phase 6BC): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new
project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.OpenSystems

open scoped Matrix
open Matrix

/-- The lowering operator `σ₋ = |0⟩⟨1|` on a two-level system (ground `|0⟩`, excited `|1⟩`). -/
def sigmaMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The **damped two-level GKSL generator**: spontaneous emission at rate `γ`, no Hamiltonian drive,
single jump operator `L = √γ σ₋`. -/
noncomputable def dampedTwoLevelGenerator (γ : ℝ) : MatrixMap (Fin 2) (Fin 2) ℂ :=
  lindbladGenerator 0 (fun _ : Fin 1 => (Real.sqrt γ : ℂ) • sigmaMinus)

/-- **Decay rate from the generator.** The excited-state population entry obeys `(ℒρ)₁₁ = −γ·ρ₁₁`:
the generator drives relaxation `ṗ_e = −γ p_e` at rate `γ`. Computed from the GKSL canonical form. -/
theorem dampedTwoLevel_generator_decay_rate (γ : ℝ) (hγ : 0 ≤ γ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dampedTwoLevelGenerator γ ρ 1 1 = -(γ : ℂ) * ρ 1 1 := by
  rw [dampedTwoLevelGenerator, gksl_canonical_form]
  have hsq : (Real.sqrt γ : ℂ) ^ 2 = (γ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hγ]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, sigmaMinus,
    sub_zero, smul_zero, zero_add,
    Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul, mul_zero, mul_one, zero_mul, add_zero,
    Complex.star_def, Complex.conj_ofReal, map_zero]
  ring_nf
  rw [hsq]
  ring

/-- **Population trajectory solves the rate equation.** The factor `p₀ · e^{−γt}` is the solution of
the relaxation rate equation `ṗ_e = −γ p_e` that the generator induces (rate `−γ` proven in
`dampedTwoLevel_generator_decay_rate`): its time-derivative is `−γ` times itself. This makes the
identification of `e^{−γt}` as the excited-population factor a Lean-verified consequence of the
generator's rate, not a by-hand step. (The remaining two-layer input — that the population literally
evolves under `e^{tℒ}` — is the propagator action of Wave 3.) -/
theorem dampedTwoLevel_population_solves_rate (γ p₀ t : ℝ) :
    HasDerivAt (fun τ : ℝ => p₀ * Real.exp (-(γ * τ))) (-γ * (p₀ * Real.exp (-(γ * t)))) t := by
  have h : HasDerivAt (fun τ : ℝ => -(γ * τ)) (-γ) t := by
    exact ((hasDerivAt_id t).const_mul γ).neg.congr_deriv (by ring)
  have h2 := (h.exp).const_mul p₀
  exact h2.congr_deriv (by ring)

/-- **Certified decay envelope.** The excited-population decay factor `e^{−γt}` — the solution of the
generator-induced rate equation `ṗ_e = −γ p_e` (`dampedTwoLevel_population_solves_rate`, with rate from
`dampedTwoLevel_generator_decay_rate`) — admits the rational enclosure `1 − γt ≤ e^{−γt} ≤ 1/(1+γt)`,
with no floating-point `exp`: the project `expNeg_enclosure` Bernoulli bracket at `r = γt`. -/
theorem dampedTwoLevel_decay_envelope {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    1 - γ * t ≤ Real.exp (-(γ * t)) ∧ Real.exp (-(γ * t)) ≤ 1 / (1 + γ * t) :=
  SKEFTHawking.QuantumNetwork.expNeg_enclosure (mul_nonneg hγ ht)

/-- Worked `norm_num` operating point of the decay envelope at `γt = ½`: `e^{−1/2} ∈ [½, ⅔]`. -/
theorem dampedTwoLevel_decay_envelope_half :
    (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) ∧ Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
  have h := dampedTwoLevel_decay_envelope (γ := 1) (t := 1 / 2) (by norm_num) (by norm_num)
  constructor
  · have h1 := h.1; norm_num at h1 ⊢; linarith
  · have h2 := h.2; norm_num at h2 ⊢; linarith

end SKEFTHawking.OpenSystems
