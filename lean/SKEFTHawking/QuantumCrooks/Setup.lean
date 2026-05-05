/-
# Phase 6n Wave 2b (QCrooks-α) — Setup

Common substrate for the parallel-axiomatization tableau on quantum-Crooks
fluctuation theorems. Defines the work-distribution and measurement-scheme
types every candidate axiomatization (Tasaki, Åberg, Kafri-Deffner,
Quasiprobability) parameterizes over, plus the Crooks-ratio predicate
that classical Crooks satisfies and that each quantum candidate either
recovers, weakens, or replaces.

**Stage 1 substantive scope.** Ships the lightweight type structure
(`WorkDistribution`, `IsCrooksRatio`, `MeasurementScheme`) needed for the
parallel tableau. Heavier finite-dim quantum substrate (density matrices,
Hamiltonians, unitary evolution) is deferred to Stage 2-3 where Aristotle
will operate on small `Fin n`-dim sandboxes; Stage 1 keeps the work
distribution abstract (`ℝ → ℝ` density) so the candidate-axiomatization
predicates can be stated and cross-compared without committing to a
specific quantum-substrate shape.

References:
- Talkner-Hänggi 2007, J. Phys. A 40, F569, arXiv:0705.1252 (Tasaki-Crooks)
- Phase 6n DR Appendix §5 (G10-QCrooks-α track structure;
  Lit-Search/_Exploratory/Appendix- Re-assessment of Deferred Tracks for SK_EFT_Hawking Phase 6n+.md)
- temporary/working-docs/phase6n/wave_2b_QCrooks_stage1.md
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

namespace SKEFTHawking.QuantumCrooks

/--
**A work distribution: a non-negative density on `ℝ`.**

Stage-1 abstract form: `P : ℝ → ℝ` returning a probability density at each
work value `W`. Stage 2-3 promotion to a Mathlib `Measure ℝ` once the
substantive integral content (average work, normalization) is required by
downstream theorems.

This is the type every candidate quantum-Crooks axiomatization predicate
operates on — Tasaki's TPM-derived distribution, Åberg's coherent
inferred distribution, Kirkwood-Dirac quasiprobability (with the
non-negativity condition relaxed for the quasiprobability case via a
separate predicate). -/
structure WorkDistribution where
  /-- The probability density at work value `W`. -/
  P : ℝ → ℝ
  /-- Non-negativity: `0 ≤ P W` for every work value. -/
  nonneg : ∀ W : ℝ, 0 ≤ P W

/-- The trivial zero work distribution. Used as a Stage-1 placeholder
witness for forward/reverse distribution constructors that haven't yet
shipped their substantive Stage-2-3 implementations. -/
noncomputable def WorkDistribution.zero : WorkDistribution where
  P := fun _ => 0
  nonneg := fun _ => le_refl 0

/--
**The classical Crooks ratio predicate.**

A pair `(P_F, P_R)` of forward/reverse work distributions at inverse
temperature `β` satisfies the *classical Crooks ratio* if

    P_F(W) = exp(β W) · P_R(-W)    for all  W ∈ ℝ.

This is the predicate every candidate quantum-Crooks axiomatization either
*recovers* (Tasaki-Crooks on diagonal initial states), *weakens to a
quasiprobability version* (Kirkwood-Dirac), *replaces with a coherent
analog* (Åberg), or *generalizes via a unital-channel form* (Kafri-Deffner).
-/
def IsCrooksRatio (P_F P_R : WorkDistribution) (β : ℝ) : Prop :=
  ∀ W : ℝ, P_F.P W = Real.exp (β * W) * P_R.P (-W)

/--
**The classical Crooks ratio holds trivially when both distributions are
zero.**

Substantive Stage-1 content: the trivial zero distributions satisfy the
Crooks ratio at any inverse temperature β (both sides equal 0). This is the
well-posedness witness for `IsCrooksRatio` — it shows the predicate has at
least one inhabitant pair for any β, so downstream theorems parameterized
on `IsCrooksRatio` are not vacuous. -/
theorem isCrooksRatio_zero (β : ℝ) :
    IsCrooksRatio WorkDistribution.zero WorkDistribution.zero β := by
  intro W
  simp [WorkDistribution.zero]

/--
**Symmetry of the Crooks ratio: `IsCrooksRatio P_F P_R β ↔ IsCrooksRatio P_R P_F β`.**

Substantive Stage-1 content: the Crooks-ratio predicate is *symmetric*
in its forward / reverse arguments — if `(P_F, P_R, β)` satisfies the
Crooks ratio, then so does `(P_R, P_F, β)`. This is a non-trivial algebraic
consequence of the multiplicative structure: from
`P_F(W) = exp(β·W) · P_R(-W)` evaluated at `-W` we get
`P_F(-W) = exp(-β·W) · P_R(W)`, which inverts to
`P_R(W) = exp(β·W) · P_F(-W)`.

The forward / reverse roles of an experimental protocol are symmetric in
the Crooks fluctuation theorem framework — neither direction is "physically
preferred." This is a load-bearing structural property used by
trajectory-Crooks downstream content (Wave 2c, Wave 2d) when constructing
reverse protocols at the Rindler horizon. -/
theorem IsCrooksRatio.symm {P_F P_R : WorkDistribution} {β : ℝ}
    (h : IsCrooksRatio P_F P_R β) : IsCrooksRatio P_R P_F β := by
  intro W
  -- Apply h at -W: P_F.P (-W) = exp(β · -W) · P_R.P (-(-W)) = exp(-β·W) · P_R.P W
  have h_neg : P_F.P (-W) = Real.exp (β * -W) * P_R.P W := by
    have := h (-W); rwa [neg_neg] at this
  -- Goal: P_R.P W = exp(β·W) · P_F.P (-W)
  rw [h_neg, ← mul_assoc]
  -- Goal: P_R.P W = (exp(β·W) · exp(-β·W)) · P_R.P W
  have hexp_one : Real.exp (β * W) * Real.exp (β * -W) = 1 := by
    rw [← Real.exp_add, show β * W + β * -W = 0 by ring, Real.exp_zero]
  rw [hexp_one, one_mul]

/--
**The Crooks ratio is an equivalence relation on the forward / reverse
roles.**

Combining `IsCrooksRatio.symm` with reflexivity-on-zero, the Crooks ratio
defines a *symmetric* relation on `WorkDistribution × WorkDistribution`
parameterized by β. This is the cleanest abstract statement of the
forward / reverse symmetry of the classical Crooks fluctuation theorem. -/
theorem IsCrooksRatio.iff_symm {P_F P_R : WorkDistribution} {β : ℝ} :
    IsCrooksRatio P_F P_R β ↔ IsCrooksRatio P_R P_F β :=
  ⟨IsCrooksRatio.symm, IsCrooksRatio.symm⟩

/--
**A measurement scheme on a single copy of a quantum work-fluctuation
protocol.**

Stage-1 abstract form: a measurement scheme is anything that, given an
inverse temperature `β`, produces a forward and reverse work distribution.
The actual quantum-protocol input (initial state ρ, evolution U,
Hamiltonians H_i / H_f) is abstracted away at Stage 1; Stage 2 will pin
the scheme to operate on a concrete `CrooksProtocol n` finite-dim
substrate so Aristotle can search for counterexamples to specific
candidate schemes.

Different inhabitants of `MeasurementScheme` correspond to:
- **Tasaki-TPM**: project, evolve, project — work from energy differences.
- **Åberg-coherent**: coherent reservoir + global unitary — work from
  reservoir displacement.
- **Kafri-Deffner-unital**: unital channel applied to ρ — work from
  Holevo-bound entropy production.
- **Kirkwood-Dirac quasiprobability**: q(E_f, E_i) = ⟨E_f|UρU†|E_i⟩⟨E_i|E_f⟩
  — work as quasiprobability density.

The Perarnau-Llobet et al. no-go theorem (`PerarnauLlobet.lean`) is a
constraint on which (forward, reverse) distribution pairs an MS can
produce while simultaneously reproducing the average energy and recovering
TPM on diagonal states. -/
structure MeasurementScheme where
  /-- Given an inverse temperature `β`, return the forward work distribution
      this scheme assigns to the (abstract Stage-1) protocol. -/
  forward : ℝ → WorkDistribution
  /-- Given an inverse temperature `β`, return the reverse work distribution
      this scheme assigns to the (abstract Stage-1) protocol. -/
  reverse : ℝ → WorkDistribution

/-- The trivial measurement scheme: returns the zero distribution for both
forward and reverse, regardless of `β`. Used as a Stage-1 well-posedness
witness for `MeasurementScheme` (the type is non-empty). -/
noncomputable def MeasurementScheme.trivial : MeasurementScheme where
  forward := fun _ => WorkDistribution.zero
  reverse := fun _ => WorkDistribution.zero

end SKEFTHawking.QuantumCrooks
