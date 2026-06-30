import SKEFTHawking.LindbladGenerator
import SKEFTHawking.QuantumNetwork.CPTPChannel
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Markovian semigroup and trace-distance contractivity (Phase 6BC, Wave 3)

The dynamical map of the GKSL master equation `ρ̇ = ℒ(ρ)` is the one-parameter Markovian semigroup
`Λ_t = e^{tℒ}`. Because `ℒ` is a *superoperator* (a linear endomorphism of `Matrix d d ℂ`) and the
Liouvillian is **non-Hermitian**, the exponential is taken on the **vectorized** generator: choosing
the standard matrix basis identifies `ℒ` with a matrix `Matrix (d × d) (d × d) ℂ`
(`lindbladLiouvillian`, via `LinearMap.toMatrix`), and `Λ_t = NormedSpace.exp (t · L_vec)` is Mathlib's
matrix exponential (`Matrix.exp` machinery) — *not* `HermitianMat.exp`, which only applies to Hermitian
operators.

* **Semigroup law** (`lindblad_semigroup`) — `Λ_t · Λ_s = Λ_{t+s}` (matrix product = vectorized
  composition `Λ_t ∘ Λ_s`), with `lindblad_propagator_zero` giving `Λ_0 = 1`: a genuine one-parameter
  semigroup. Proven from `Matrix.exp_add_of_commute` (the scalar multiples `t·L_vec`, `s·L_vec`
  commute).
* **Trace-distance contractivity** (`traceDist_lindblad_monotone`) — the data-processing inequality
  `D(Λ_t ρ, Λ_t σ) ≤ D(ρ, σ)`. This is contractivity of a CPTP channel: it holds for the dynamical map
  *because* `Λ_t` is completely positive and trace preserving (the GKSL semigroup is CPTP). That CPTP
  property — equivalently, a Kraus realization of `Λ_t` — is the genuine physical content of the GKSL
  theorem; here it is **disclosed as a hypothesis** (`hreal`: the propagator's action coincides with a
  `krausMap` whose Kraus operators form an `IsKrausChannel`), and the contraction is then the project's
  data-processing inequality `traceDist_krausMap_le`. *(Discharge plan: the GKSL CP-semigroup theorem
  via the Lie–Trotter product `e^{tℒ} = lim (e^{tℒ/n})^n` with each factor CP — using the Wave-1
  dissipator complete positivity `lindblad_generator_CP`.)*

**Two-layer honesty.** The semigroup/exponential *formulas* are Lean-verified; the CPTP Kraus
realization of `e^{tℒ}` (which jump operators, which bath) is the literature-cited physical input.

Invariants (Phase 6BC): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new
project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.OpenSystems

open scoped Matrix
open Matrix SKEFTHawking.QuantumNetwork

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {κ : Type*} [Fintype κ]

/-- The **vectorized Liouvillian**: the GKSL generator `ℒ` expressed as a matrix on `d × d` via the
standard matrix basis. The Markovian semigroup is the matrix exponential of `t · L_vec`. -/
noncomputable def lindbladLiouvillian (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) :
    Matrix (d × d) (d × d) ℂ :=
  LinearMap.toMatrix (Matrix.stdBasis ℂ d d) (Matrix.stdBasis ℂ d d) (lindbladGenerator H L)

/-- The **Markovian (GKSL) propagator** `Λ_t = e^{tℒ}`, as the matrix exponential of the vectorized
(non-Hermitian) Liouvillian. -/
noncomputable def lindbladPropagator (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) (t : ℝ) :
    Matrix (d × d) (d × d) ℂ :=
  NormedSpace.exp ((t : ℂ) • lindbladLiouvillian H L)

/-- The propagator's action as a superoperator on density matrices (de-vectorization via
`Matrix.toLin`): `Λ_t : Matrix d d ℂ →ₗ Matrix d d ℂ`. -/
noncomputable def lindbladPropagatorAction (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) (t : ℝ) :
    Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ :=
  Matrix.toLin (Matrix.stdBasis ℂ d d) (Matrix.stdBasis ℂ d d) (lindbladPropagator H L t)

/-- **`Λ_0 = 1`** — the propagator is the identity at time zero. -/
theorem lindblad_propagator_zero (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) :
    lindbladPropagator H L 0 = 1 := by
  rw [lindbladPropagator, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

/-- **GKSL semigroup law.** `Λ_t · Λ_s = Λ_{t+s}` — the matrix product (vectorized composition
`Λ_t ∘ Λ_s`) of propagators is the propagator at the summed time. Proven via `Matrix.exp_add_of_commute`
(the commuting scalar multiples of the Liouvillian). -/
theorem lindblad_semigroup (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) (t s : ℝ) :
    lindbladPropagator H L t * lindbladPropagator H L s = lindbladPropagator H L (t + s) := by
  rw [lindbladPropagator, lindbladPropagator, lindbladPropagator, Complex.ofReal_add, add_smul]
  exact (Matrix.exp_add_of_commute _ _
    (((Commute.refl (lindbladLiouvillian H L)).smul_left (t : ℂ)).smul_right (s : ℂ))).symm

/- **Trace-distance contractivity (`traceDist_lindblad_monotone`)** now lives — *unconditionally* — in
`SKEFTHawking.LindbladCPSemigroup`. It formerly disclosed `hreal` (the propagator's action realized by a
Kraus channel) as a hypothesis; that hypothesis has since been **discharged**: the propagator is proven
completely positive (`isCompletelyPositive_lindbladPropagatorAction`) and trace-preserving
(`trace_lindbladPropagatorAction`), hence CPTP, so the realization is extracted (`exists_kraus`) rather
than assumed. The unconditional theorem is stated downstream because the CP proof depends on this module. -/

end SKEFTHawking.OpenSystems
