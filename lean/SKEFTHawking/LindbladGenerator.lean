import QuantumInfo.Channels.CPTP

/-!
# GKSL / Lindblad generator and complete positivity of its dissipator (Phase 6BC, Wave 1)

The Gorini–Kossakowski–Sudarshan–Lindblad (GKSL) generator of a Markovian open-system master
equation `ρ̇ = ℒ(ρ)`:

  `ℒ(ρ) = −i[H,ρ] + Σ_k (L_k ρ L_k† − ½{L_k†L_k, ρ})`,

with a Hermitian Hamiltonian `H` and jump operators `L_k`. The generator splits into three linear
pieces on `Matrix d d ℂ`:

* the **Hamiltonian (unitary) part** `−i[H,ρ]` (`lindbladHamPart`), built from
  `LinearMap.mulLeft`/`mulRight` so linearity is automatic;
* the **dissipative jump part** `Σ_k L_k ρ L_k†` (`lindbladJump`) — a Kraus map with `M = N = L`,
  which is the *completely positive* engine of the dynamics (PhysLib `MatrixMap.of_kraus`);
* the **anticommutator (decay) part** `−½{G,ρ}` with `G = Σ_k L_k†L_k` (`lindbladAnticommPart`).

**Wave-1 headline (`lindblad_generator_CP`).** The dissipative jump part is completely positive,
proven through the PhysLib Choi route (`MatrixMap.of_kraus_CP`, whose proof certifies the Choi matrix
`Σ_k vecMulVec …` is PSD). Complete positivity of the dissipator is the physical-consistency condition
that singles out the GKSL form: the generator's dissipative engine acts completely positively. (The
full generator `ℒ` is only *conditionally* completely positive — its non-CP part is exactly the
Hamiltonian + anticommutator drift — so CP is asserted for the dissipator, the object that carries it.)

**Two-layer honesty.** The generator/CP *formulas* here are Lean-verified. The physical-channel
identification — which bath, which microscopic jump operators `L_k` realise a given open system — stays
literature-cited at the point of use; this module fixes only the algebraic GKSL structure.

Invariants (Phase 6BC): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new
project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.OpenSystems

open scoped Matrix
open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {κ : Type*} [Fintype κ]

/-- The Hamiltonian (unitary) part of the GKSL generator: `ρ ↦ −i[H, ρ] = −i(Hρ − ρH)`. -/
noncomputable def lindbladHamPart (H : Matrix d d ℂ) : MatrixMap d d ℂ :=
  -Complex.I • (LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H)

/-- The dissipative *jump* part of the GKSL generator: `ρ ↦ Σ_k L_k ρ L_k†`. A Kraus map with
`M = N = L`; this is the completely-positive engine of the dynamics. -/
noncomputable def lindbladJump (L : κ → Matrix d d ℂ) : MatrixMap d d ℂ := MatrixMap.of_kraus L L

/-- The anticommutator (decay) part: `ρ ↦ −½{G, ρ}` with `G = Σ_k L_k† L_k`. -/
noncomputable def lindbladAnticommPart (L : κ → Matrix d d ℂ) : MatrixMap d d ℂ :=
  -(2⁻¹ : ℂ) • (LinearMap.mulLeft ℂ (∑ k, (L k)ᴴ * L k)
    + LinearMap.mulRight ℂ (∑ k, (L k)ᴴ * L k))

/-- The **GKSL / Lindblad generator**
`ℒ(ρ) = −i[H,ρ] + Σ_k (L_k ρ L_k† − ½{L_k†L_k, ρ})`. -/
noncomputable def lindbladGenerator (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) : MatrixMap d d ℂ :=
  lindbladHamPart H + lindbladJump L + lindbladAnticommPart L

/-- The Hamiltonian part acts as the commutator `−i[H, ρ]`. -/
theorem lindbladHamPart_apply (H ρ : Matrix d d ℂ) :
    lindbladHamPart H ρ = -Complex.I • (H * ρ - ρ * H) := by
  simp [lindbladHamPart]

omit [DecidableEq d] in
/-- The dissipative jump part acts as the explicit Kraus sum `Σ_k L_k ρ L_k†`. -/
theorem lindbladJump_apply (L : κ → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    lindbladJump L ρ = ∑ k, L k * ρ * (L k)ᴴ := by
  simp only [lindbladJump, MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- The anticommutator part acts as `−½{G, ρ}` with `G = Σ_k L_k† L_k`. -/
theorem lindbladAnticommPart_apply (L : κ → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    lindbladAnticommPart L ρ
      = -(2⁻¹ : ℂ) • ((∑ k, (L k)ᴴ * L k) * ρ + ρ * (∑ k, (L k)ᴴ * L k)) := by
  simp [lindbladAnticommPart]

/-- **Wave-1 headline — complete positivity of the dissipator.** The dissipative jump map
`Σ_k L_k · L_k†` of the GKSL generator is completely positive, via the PhysLib Choi route
(`MatrixMap.of_kraus_CP`). This is the physical-consistency condition singling out the GKSL form. -/
theorem lindblad_generator_CP (L : κ → Matrix d d ℂ) :
    (lindbladJump L).IsCompletelyPositive :=
  MatrixMap.of_kraus_CP L

end SKEFTHawking.OpenSystems
