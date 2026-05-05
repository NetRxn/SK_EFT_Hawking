/-
# Phase 6n Wave 2b — QuantumCrooks ↔ SKEFTAxioms cross-bridge (Session 14, 2026-05-05)

Connects the four Stage-1 axiomatization predicates of Wave 2b
(`IsTasakiTPMScheme`, `IsAbergCoherentScheme`, `IsKafriDeffnerUnitalScheme`,
`IsKirkwoodDiracScheme`) to Wave 2a's `SKEFTAxioms` substrate via the
linear-response Gaussian work distribution. Mirrors the structure of
`CrooksAnalogHawking/SKEFTGallavottiCohen.lean` (Wave 2c Stage 4) at the
quantum-Crooks-axiomatization level.

**Substantive content shipped here:**

  1. `linearResponseGaussian μ σ²` — unnormalized Gaussian density
     `exp(-(W - μ)²/(2σ²))` on `ℝ`. Non-negativity is `Real.exp_nonneg`.
  2. `linearResponseWorkDistribution β σ²` — `WorkDistribution` with the
     FDT-pinned mean `β·σ²/2` (cyclic linear-response form, ΔF = 0).
  3. `linearResponseMeasurementScheme σ²` — `MeasurementScheme` whose
     forward and reverse distributions at every β are the same FDT-pinned
     Gaussian (cyclic-process specialization).
  4. `linearResponseMeasurementScheme_isCrooksRatio` — at every β and any
     σ² ≠ 0, the linear-response scheme satisfies the classical Crooks
     ratio. The algebra reduces to the identity
     `(W + β·σ²/2)² - (W - β·σ²/2)² = 2·σ²·β·W`.
  5. **First non-trivial substantive witnesses** for each of the four
     Stage-1 axiomatization predicates: `IsTasakiTPMScheme`,
     `IsAbergCoherentScheme`, `IsKafriDeffnerUnitalScheme`,
     `IsKirkwoodDiracScheme` — all satisfied by the linear-response scheme.
     (The previously-shipped `trivialScheme_is_*` witnesses use the zero
     distribution; this is the first non-degenerate witness.)
  6. **Wave 2a → Wave 2b cross-bridge `skeft_substrate_yields_TPM_scheme`**:
     given `A : SKEFTAxioms action β`, extract `c : FirstOrderCoeffs` with
     `FirstOrderKMS c β` from `A.dynamical_KMS`; the linear-response
     measurement scheme parameterized by σ² := c.i₂ then satisfies all
     four Stage-1 axiomatization predicates conditional on c.i₂ ≠ 0.
     This is the structural analog of Wave 2c's
     `skeft_substrate_yields_WFormGC`.
  7. **Concrete witness `firstOrderDissipative_yields_TPM_scheme`** for
     `firstOrderDissipativeAction(coeffs, β)` with `coeffs.gamma_2 > 0`
     (so c.i₂ = γ₂/β > 0) — the cross-bridge holds unconditionally.
  8. **Closure `wave_2b_typeclass_connections_closure`** — 9-conjunct
     summary: the canonical first-order dissipative SK-EFT action with
     γ₂ > 0 yields a single `MeasurementScheme` simultaneously satisfying
     the Stage-1 form of all four Wave 2b axiomatization predicates
     plus the FDR-extracted `c : FirstOrderCoeffs` with `FirstOrderKMS`.

**Substantive load-bearing finding.** The four Wave 2b axiomatization
predicates at Stage 1 have identical surface form (each is
`∀ β, IsCrooksRatio (MS.forward β) (MS.reverse β) β`) but encode
distinct semantic content lifted at Stage 2-3. The linear-response
substrate witnesses Stage-1 simultaneous satisfiability — a single MS
satisfies all four. The Perarnau-Llobet et al. no-go theorem
(`PerarnauLlobet.lean`) operates on the *Stage 2-3 distinguishing
predicates* (`ReproducesAverageEnergy`, `RecoversTPMOnDiagonal`) and
shows pairwise incompatibility there; the no-go does NOT contradict
Stage-1 simultaneous satisfiability. This module establishes that
the SK-EFT substrate produces a measurement scheme that meets the
Stage-1 axiomatization predicates non-vacuously, before the Stage 2-3
distinguishing structure is imposed.

**MCP-driven, zero Aristotle escalation, zero new sorry, zero new axioms.**

References:
- `lean/SKEFTHawking/CrooksAnalogHawking/SKEFTGallavottiCohen.lean` —
  Wave 2c Stage-4 substrate-level bridge (W-form GC analog of this).
- `lean/SKEFTHawking/GloriosoLiu/Axioms.lean` — `SKEFTAxioms` +
  `SKEFTAxioms_for_dissipative` substantive witness.
- `lean/SKEFTHawking/QuantumCrooks/{Tasaki,Aberg,KafriDeffner,Quasiprobability}.lean`
  — Stage-1 axiomatization predicates.
- `temporary/working-docs/phase6n/6n_gamma_kms_framework_finding.md` —
  KMS framework finding establishing the algebraic-FDR `FirstOrderKMS`
  as the substantive form of dynamical-KMS for SK-EFT.
- Phase 6n Roadmap recommended-next-up #12 (Session-13 list).
-/
import SKEFTHawking.QuantumCrooks.Setup
import SKEFTHawking.QuantumCrooks.Tasaki
import SKEFTHawking.QuantumCrooks.Aberg
import SKEFTHawking.QuantumCrooks.KafriDeffner
import SKEFTHawking.QuantumCrooks.Quasiprobability
import SKEFTHawking.GloriosoLiu.Axioms

namespace SKEFTHawking.QuantumCrooks

open SKEFTHawking.GloriosoLiu
open SKEFTHawking.SKDoubling

/-! ## §1. Linear-response Gaussian work distribution -/

/-- **Unnormalized Gaussian density** with mean `μ` and variance parameter
`σ²`. Returns `exp(-(W - μ)²/(2·σ²))`; non-negative for any μ, σ², W via
`Real.exp_nonneg`. This is the linear-response work distribution shape;
the prefactor `1/√(2πσ²)` is omitted because the Crooks ratio
`P_F(W)/P_R(-W) = exp(β·W)` is prefactor-invariant when both
distributions share the same Gaussian normalization. -/
noncomputable def linearResponseGaussian (μ σ_sq : ℝ) : ℝ → ℝ :=
  fun W => Real.exp (-(W - μ) ^ 2 / (2 * σ_sq))

theorem linearResponseGaussian_nonneg (μ σ_sq W : ℝ) :
    0 ≤ linearResponseGaussian μ σ_sq W := by
  unfold linearResponseGaussian
  exact Real.exp_nonneg _

/-- **Linear-response work distribution** at inverse temperature `β` with
variance parameter `σ²`. The mean is FDT-pinned to `β·σ²/2`, the cyclic-
process value (ΔF = 0). For the non-cyclic case the mean would shift
by ΔF; the cyclic specialization is sufficient for Stage-1 cross-bridge. -/
noncomputable def linearResponseWorkDistribution (β σ_sq : ℝ) :
    WorkDistribution where
  P := linearResponseGaussian (β * σ_sq / 2) σ_sq
  nonneg := fun _ => linearResponseGaussian_nonneg _ _ _

/-! ## §2. Linear-response measurement scheme + Crooks ratio -/

/-- **Linear-response measurement scheme.** Forward and reverse work
distributions at every β are the same FDT-pinned Gaussian (cyclic-
process specialization, μ_F = μ_R = β·σ²/2). The Crooks ratio at this
specialization is the textbook linear-response result. -/
noncomputable def linearResponseMeasurementScheme (σ_sq : ℝ) :
    MeasurementScheme where
  forward := fun β => linearResponseWorkDistribution β σ_sq
  reverse := fun β => linearResponseWorkDistribution β σ_sq

/-- **Substantive Stage-1 algebraic content: the linear-response measurement
scheme satisfies the classical Crooks ratio at every inverse temperature β.**

Direct algebra. Setting μ := β·σ²/2 (the FDT-pinned mean), the Crooks
identity `P_F(W) = exp(β·W) · P_R(-W)` reduces (after `← Real.exp_add`
on the RHS) to the exponent identity:

    -(W - μ)²/(2σ²) = β·W + -(-W - μ)²/(2σ²)

equivalently, `(W + μ)² - (W - μ)² = 2σ²·β·W` — which expands via
`(a+b)² - (a-b)² = 4ab` to `4Wμ = 2σ²·β·W`, true under `μ = β·σ²/2`.

The hypothesis `σ_sq ≠ 0` is needed to clear denominators via
`field_simp`. The case σ_sq = 0 is degenerate (the Gaussian becomes a
delta-distribution-like object beyond Stage-1 scope). -/
theorem linearResponseMeasurementScheme_isCrooksRatio
    (σ_sq : ℝ) (h_σ : σ_sq ≠ 0) (β : ℝ) :
    IsCrooksRatio ((linearResponseMeasurementScheme σ_sq).forward β)
                  ((linearResponseMeasurementScheme σ_sq).reverse β) β := by
  intro W
  -- Unfold to reach gaussian densities.
  show linearResponseGaussian (β * σ_sq / 2) σ_sq W
       = Real.exp (β * W) * linearResponseGaussian (β * σ_sq / 2) σ_sq (-W)
  unfold linearResponseGaussian
  -- Goal: exp(-(W - β·σ²/2)²/(2·σ²))
  --     = exp(β·W) · exp(-(-W - β·σ²/2)²/(2·σ²))
  rw [← Real.exp_add]
  -- Goal: exp(-(W - β·σ²/2)²/(2·σ²))
  --     = exp(β·W + -(-W - β·σ²/2)²/(2·σ²))
  congr 1
  -- Goal: -(W - β·σ²/2)²/(2·σ²) = β·W + -(-W - β·σ²/2)²/(2·σ²)
  field_simp
  ring

/-! ## §3. The four Stage-1 axiomatization predicates all hold -/

/-- **First non-trivial substantive witness for `IsTasakiTPMScheme`.**

The linear-response measurement scheme satisfies the Tasaki-TPM Stage-1
predicate. (At Stage 1, `IsTasakiTPMScheme MS = ∀ β, IsCrooksRatio
(MS.forward β) (MS.reverse β) β`; this reduces to §2's algebraic
content.) Companion to `trivialScheme_is_TPM` — that one uses the zero
distribution; this one uses the FDT-pinned linear-response Gaussian. -/
theorem linearResponseMeasurementScheme_isTasakiTPM
    (σ_sq : ℝ) (h_σ : σ_sq ≠ 0) :
    IsTasakiTPMScheme (linearResponseMeasurementScheme σ_sq) := by
  intro β
  exact linearResponseMeasurementScheme_isCrooksRatio σ_sq h_σ β

/-- **Substantive witness for `IsAbergCoherentScheme`** — the linear-response
scheme satisfies the Stage-1 Åberg predicate (which has the same shape as
Tasaki at Stage 1; substantive distinction is at Stage 2-3). -/
theorem linearResponseMeasurementScheme_isAbergCoherent
    (σ_sq : ℝ) (h_σ : σ_sq ≠ 0) :
    IsAbergCoherentScheme (linearResponseMeasurementScheme σ_sq) := by
  intro β
  exact linearResponseMeasurementScheme_isCrooksRatio σ_sq h_σ β

/-- **Substantive witness for `IsKafriDeffnerUnitalScheme`** — the
linear-response scheme satisfies the Stage-1 Kafri-Deffner predicate. -/
theorem linearResponseMeasurementScheme_isKafriDeffnerUnital
    (σ_sq : ℝ) (h_σ : σ_sq ≠ 0) :
    IsKafriDeffnerUnitalScheme (linearResponseMeasurementScheme σ_sq) := by
  intro β
  exact linearResponseMeasurementScheme_isCrooksRatio σ_sq h_σ β

/-- **Substantive witness for `IsKirkwoodDiracScheme`** — the linear-response
scheme satisfies the Stage-1 Kirkwood-Dirac quasiprobability predicate. -/
theorem linearResponseMeasurementScheme_isKirkwoodDirac
    (σ_sq : ℝ) (h_σ : σ_sq ≠ 0) :
    IsKirkwoodDiracScheme (linearResponseMeasurementScheme σ_sq) := by
  intro β
  exact linearResponseMeasurementScheme_isCrooksRatio σ_sq h_σ β

/-! ## §4. Wave 2a → Wave 2b cross-bridge -/

/-- **Substantive substrate-level bridge: under SKEFTAxioms at β, the
dynamical-KMS algebraic-FDR witness extracts a `c : FirstOrderCoeffs`
whose noise coefficient `c.i₂` parameterizes a linear-response
measurement scheme satisfying all four Wave 2b Stage-1 axiomatization
predicates (conditional on `c.i₂ ≠ 0` for non-vacuity).**

Mirrors `skeft_substrate_yields_WFormGC` (Wave 2c Session 8) at the
quantum-Crooks-axiomatization level.

The proof body destructures `A.dynamical_KMS` (the algebraic-FDR form
per `hasDynamicalKMS_algebraic`) to extract `c` with `FirstOrderKMS c β`
and the polynomial-form witness. The W-form Crooks ratio at variance
σ² := c.i₂ is then discharged via §3 conditional on `c.i₂ ≠ 0`.

The conditional form `c.i₂ ≠ 0 → ...` is structural — for degenerate
substrates with zero noise, the linear-response Gaussian is degenerate
and the Crooks-ratio statement is vacuous. For dissipative substrates
with c.i₂ > 0 (e.g., `firstOrderDissipativeAction` with γ₂ > 0; see §5),
the cross-bridge is unconditional. -/
theorem skeft_substrate_yields_TPM_scheme
    (action : SKAction) (β : ℝ) (_hβ : 0 < β) (A : SKEFTAxioms action β) :
    ∃ c : FirstOrderCoeffs,
      (∀ f : SKFields, action.lagrangian f = (firstOrderAction c).lagrangian f) ∧
      FirstOrderKMS c β ∧
      (c.i2 ≠ 0 →
        IsTasakiTPMScheme (linearResponseMeasurementScheme c.i2) ∧
        IsAbergCoherentScheme (linearResponseMeasurementScheme c.i2) ∧
        IsKafriDeffnerUnitalScheme (linearResponseMeasurementScheme c.i2) ∧
        IsKirkwoodDiracScheme (linearResponseMeasurementScheme c.i2)) := by
  obtain ⟨c, hL, hKMS⟩ := A.dynamical_KMS
  refine ⟨c, hL, hKMS, fun hi2 => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact linearResponseMeasurementScheme_isTasakiTPM c.i2 hi2
  · exact linearResponseMeasurementScheme_isAbergCoherent c.i2 hi2
  · exact linearResponseMeasurementScheme_isKafriDeffnerUnital c.i2 hi2
  · exact linearResponseMeasurementScheme_isKirkwoodDirac c.i2 hi2

/-! ## §5. Concrete substantive witness for `firstOrderDissipativeAction` -/

/-- **Concrete substantive witness: `firstOrderDissipativeAction` with
γ₂ > 0 yields the full Wave 2a → Wave 2b cross-bridge unconditionally.**

For `firstOrderDissipativeAction(coeffs, β)` with `coeffs.gamma_2 > 0`
and `β > 0`, the explicit FirstOrderCoeffs witness
`c = ⟨γ₁+γ₂, -γ₁, 0, 0, 0, 0, γ₁/β, γ₂/β, 0⟩` satisfies the polynomial-form
clause (Lagrangian equality), `FirstOrderKMS c β` (algebraic FDR), and
`0 < c.i₂ = γ₂/β` (positive noise from positive dissipation). All four
Stage-1 axiomatization predicates of Wave 2b then hold on the
linear-response scheme parameterized by σ² := c.i₂.

Parallels Wave 2c's `firstOrderDissipative_yields_WFormGC` (Session 8). -/
theorem firstOrderDissipative_yields_TPM_scheme
    (coeffs : DissipativeCoeffs) (β : ℝ) (hβ : 0 < β)
    (h_gamma2 : 0 < coeffs.gamma_2) :
    ∃ c : FirstOrderCoeffs,
      (∀ f : SKFields,
        (firstOrderDissipativeAction coeffs β).lagrangian f
          = (firstOrderAction c).lagrangian f) ∧
      FirstOrderKMS c β ∧
      0 < c.i2 ∧
      IsTasakiTPMScheme (linearResponseMeasurementScheme c.i2) ∧
      IsAbergCoherentScheme (linearResponseMeasurementScheme c.i2) ∧
      IsKafriDeffnerUnitalScheme (linearResponseMeasurementScheme c.i2) ∧
      IsKirkwoodDiracScheme (linearResponseMeasurementScheme c.i2) := by
  refine ⟨⟨coeffs.gamma_1 + coeffs.gamma_2, -coeffs.gamma_1, 0, 0, 0, 0,
          coeffs.gamma_1 / β, coeffs.gamma_2 / β, 0⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Lagrangian equality (mirrors SKEFTAxioms_for_dissipative body)
    intro f
    simp [firstOrderDissipativeAction, firstOrderAction]
    ring
  · -- FirstOrderKMS witness
    refine { r3_zero := rfl, r4_zero := rfl, r5_zero := rfl, r6_zero := rfl,
             fdr_i1 := ?_, fdr_i2 := ?_, i3_zero := rfl }
    · field_simp
    · field_simp; ring
  · -- 0 < c.i₂ = γ₂/β
    exact div_pos h_gamma2 hβ
  · exact linearResponseMeasurementScheme_isTasakiTPM _ (div_pos h_gamma2 hβ).ne'
  · exact linearResponseMeasurementScheme_isAbergCoherent _ (div_pos h_gamma2 hβ).ne'
  · exact linearResponseMeasurementScheme_isKafriDeffnerUnital _ (div_pos h_gamma2 hβ).ne'
  · exact linearResponseMeasurementScheme_isKirkwoodDirac _ (div_pos h_gamma2 hβ).ne'

/-! ## §6. Consolidated master theorem and closure summary

**Strengthening pass (Session 14):** at Stage 1 the four axiomatization
predicates `IsTasakiTPMScheme`, `IsAbergCoherentScheme`,
`IsKafriDeffnerUnitalScheme`, `IsKirkwoodDiracScheme` are *definitionally
equal* — each unfolds to `∀ β, IsCrooksRatio (MS.forward β) (MS.reverse β) β`.
The four named wrappers `linearResponseMeasurementScheme_is{Tasaki,...}`
in §3 above are kept as API shape for downstream consumers who want to
invoke a specific axiomatization by name, but they all reduce to the
single `linearResponseMeasurementScheme_isCrooksRatio` substantive
content.

The §6 master theorem `linearResponseMeasurementScheme_satisfiesAllStage1Axiomatizations`
consolidates this redundancy: ONE substantive Crooks-ratio theorem is
enough to imply all four axiomatization predicates simultaneously. The
closure summary then references the master rather than enumerating four
redundant conjuncts.

The semantic distinction between the four predicates emerges only at
Stage 2-3 (substrate-level density-matrix structure on `Matrix (Fin n)
(Fin n) ℂ`). The Perarnau-Llobet no-go theorem operates on that Stage
2-3 distinguishing content (`ReproducesAverageEnergy`,
`RecoversTPMOnDiagonal`), not on the Stage-1 predicate forms used
here, so simultaneous Stage-1 satisfiability is not in conflict with
the no-go. -/

/-- **Master theorem: the linear-response scheme satisfies all four
Stage-1 axiomatization predicates simultaneously.**

Direct consequence of the underlying `IsCrooksRatio` content + the fact
that all four Stage-1 predicates are definitionally equal to
`∀ β, IsCrooksRatio ...`. Replaces the four redundant wrappers with
one substantive consolidated statement. -/
theorem linearResponseMeasurementScheme_satisfiesAllStage1Axiomatizations
    (σ_sq : ℝ) (h_σ : σ_sq ≠ 0) :
    IsTasakiTPMScheme (linearResponseMeasurementScheme σ_sq) ∧
    IsAbergCoherentScheme (linearResponseMeasurementScheme σ_sq) ∧
    IsKafriDeffnerUnitalScheme (linearResponseMeasurementScheme σ_sq) ∧
    IsKirkwoodDiracScheme (linearResponseMeasurementScheme σ_sq) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro β
  all_goals exact linearResponseMeasurementScheme_isCrooksRatio σ_sq h_σ β

/-- **Wave 2b typeclass-connections closure (consolidated).**

The canonical first-order dissipative SK-EFT action
`firstOrderDissipativeAction(coeffs, β)` with `γ₂ > 0` and `β > 0` yields:

  1. A `c : FirstOrderCoeffs` with Lagrangian equality and `FirstOrderKMS c β`.
  2. `0 < c.i₂` (positive noise from positive dissipation).
  3. A `MeasurementScheme` equal to `linearResponseMeasurementScheme c.i₂`
     satisfying ALL FOUR Stage-1 axiomatization predicates simultaneously
     (consolidated via the §6 master theorem above).

The four-axiomatization simultaneous satisfiability is bundled as a
single conjunct via `linearResponseMeasurementScheme_satisfiesAllStage1Axiomatizations`,
eliminating the redundant per-axiomatization enumeration that the
preemptive-strengthening discipline flagged as a P2 antipattern. -/
theorem wave_2b_typeclass_connections_closure
    (coeffs : DissipativeCoeffs) (β : ℝ) (hβ : 0 < β)
    (h_gamma2 : 0 < coeffs.gamma_2) :
    ∃ c : FirstOrderCoeffs,
      (∀ f : SKFields,
        (firstOrderDissipativeAction coeffs β).lagrangian f
          = (firstOrderAction c).lagrangian f) ∧
      FirstOrderKMS c β ∧
      0 < c.i2 ∧
      (IsTasakiTPMScheme (linearResponseMeasurementScheme c.i2) ∧
       IsAbergCoherentScheme (linearResponseMeasurementScheme c.i2) ∧
       IsKafriDeffnerUnitalScheme (linearResponseMeasurementScheme c.i2) ∧
       IsKirkwoodDiracScheme (linearResponseMeasurementScheme c.i2)) := by
  obtain ⟨c, hL, hKMS, h_pos, _, _, _, _⟩ :=
    firstOrderDissipative_yields_TPM_scheme coeffs β hβ h_gamma2
  exact ⟨c, hL, hKMS, h_pos,
         linearResponseMeasurementScheme_satisfiesAllStage1Axiomatizations
           c.i2 h_pos.ne'⟩

end SKEFTHawking.QuantumCrooks
