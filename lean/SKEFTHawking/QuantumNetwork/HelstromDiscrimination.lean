import SKEFTHawking.QuantumNetwork.FidelityUpperBound
import SKEFTHawking.QuantumNetwork.DiamondSDPDuality

/-!
# Helstrom two-state discrimination and the fidelity floor `¼F² ≤ P_err` (Phase 6EA)

The missing consumer of the 6AF fidelity tower. `FidelityUpperBound.lean` shipped the Helstrom
*value* (`traceDist_eq_eigPosSum`) and the Fuchs–van de Graaf *upper* bound
(`traceDist_le_sqrt_one_sub_sqrtFidelity_sq`) in June 2026, but nothing ever turned them into a
statement about **measurement error**. This file does exactly that, and nothing else:

* two-outcome POVMs and their equiprobable average error (`IsBinaryPOVM`, `povmAvgError`);
* the **Holevo–Helstrom theorem** in `IsLeast` form — `½(1 − D(ρ,σ))` is the *minimum* average
  error over all two-outcome POVMs, attained at `posProj(ρ−σ)`
  (`helstrom_isLeast_povmAvgError`);
* the headline **`¼F(ρ,σ)² ≤ P_err`** (`quarter_sqrtFidelity_sq_le_povmAvgError`): no measurement
  whatsoever — projective or not — discriminates equiprobable `ρ` and `σ` with average error
  below a quarter of their squared root fidelity.

The last one is a genuine quantum bound: it quantifies over **every** POVM (`0 ⪯ E ⪯ 1`, not just
projections) and over **arbitrary** density operators (not just commuting/diagonal ones). Its
diagonal restriction is what `Detection/ShotNoise.lean` uses to earn the claim that the Wave-1
classical Poisson floor is the commutative shadow of a quantum discrimination bound.

## Route

`P_err(E) = ½(1 − Re tr(E(ρ−σ)))` is immediate from `tr ρ = 1`. The Helstrom step is the
measurement bound `Re tr(M·Q) ≤ tr(M₊)` for `0 ⪯ Q ⪯ 1` — shipped as
`DiamondSDPDuality.re_trace_mul_le_trace_posPart`, where it feeds the SDP-primal reduction — plus
`traceDist_eq_eigPosSum` and `eigPosSum_eq_re_trace_posPart` to read `tr(M₊)` as `D(ρ,σ)`.
Attainment is `eigPosSum_eq_re_trace_posProj`. Then FvdG gives `D ≤ √(1−F²)` and the elementary
`√(1−x) ≤ 1 − x/2` on `[0,1]` (`sqrt_one_sub_le_one_sub_half`) converts `½(1−D)` into `¼F²`.

**Layering note.** `re_trace_mul_le_trace_posPart` is a statement about density-matrix
measurement, not about the diamond SDP; it currently lives in `DiamondSDPDuality.lean` because
that is where it was first needed. Importing it here (rather than re-proving it) keeps a single
source of truth, at the cost of an arrow from this fidelity-layer file into the channel-layer SDP
tower. Relocating it down to `MixedState.lean`/`FidelityBounds.lean` would remove that arrow and
is the clean follow-up; it is deliberately not done here to keep this file additive.

Invariants (Phase 6EA): kernel-pure, zero sorry, no project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Two-outcome POVMs -/

/-- A **two-outcome POVM**, presented by the effect operator `E` of its first outcome: `E` and
its complement `1 − E` are both positive semidefinite, i.e. `0 ⪯ E ⪯ 1`. Completeness
`E + (1 − E) = 1` is definitional, so it is not a field.

This is the *general* measurement class, strictly larger than the projective one
(`isBinaryPOVM_of_projection` is the inclusion): nothing here forces `E² = E`. -/
def IsBinaryPOVM (E : Matrix ι ι ℂ) : Prop :=
  E.PosSemidef ∧ ((1 : Matrix ι ι ℂ) - E).PosSemidef

/-- Every projective binary measurement is a POVM — the inclusion witnessing that the Helstrom
bound below is not secretly a statement about projections only. -/
theorem isBinaryPOVM_of_projection {E : Matrix ι ι ℂ} (hEh : E.IsHermitian) (hEi : E * E = E) :
    IsBinaryPOVM E := by
  refine ⟨?_, one_sub_posSemidef_of_projection hEh hEi⟩
  rw [show E = Eᴴ * E by rw [hEh.eq, hEi]]
  exact Matrix.posSemidef_conjTranspose_mul_self E

/-- **Average error probability of the two-outcome test `{E, 1 − E}`** discriminating the
equiprobable hypotheses `ρ` (declared on outcome `E`) and `σ` (declared on outcome `1 − E`):
`½·(Pr[E | σ] + Pr[1−E | ρ])`.

Deliberately the *same* arithmetic shape as the classical `avgAssignmentError e₀ e₁ = (e₀+e₁)/2`
of the readout layer, with the two branch errors read off as Born probabilities. That is what
makes the classical/quantum comparison in `Detection/ShotNoise.lean` an equality of one
functional at two arguments rather than a comparison of two different functionals. -/
noncomputable def povmAvgError (ρ σ E : Matrix ι ι ℂ) : ℝ :=
  ((E * σ).trace.re + ((1 - E) * ρ).trace.re) / 2

/-- The error rewritten around the **discrimination operator** `ρ − σ`: on a unit-trace `ρ`,
`P_err(E) = ½(1 − Re tr(E(ρ−σ)))`. Every statement below is this identity plus a bound on
`Re tr(E(ρ−σ))`. Note only `tr ρ = 1` is used — `σ` need not be normalised, and `E` need not be
admissible. -/
theorem povmAvgError_eq_half_one_sub {ρ σ E : Matrix ι ι ℂ} (htρ : ρ.trace = 1) :
    povmAvgError ρ σ E = (1 - (E * (ρ - σ)).trace.re) / 2 := by
  unfold povmAvgError
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htρ, Complex.one_re,
    Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  ring

/-! ## The Holevo–Helstrom theorem -/

/-- **Holevo–Helstrom lower bound.** No two-outcome POVM discriminates the equiprobable density
operators `ρ` and `σ` with average error below `½(1 − D(ρ,σ))`, where `D` is the trace distance.

The measurement is *arbitrary*: `E` ranges over all effects `0 ⪯ E ⪯ 1`. The proof calls the
shipped Helstrom measurement bound `re_trace_mul_le_trace_posPart` (`Re tr(M·Q) ≤ tr(M₊)`) at
`M = ρ − σ`, `Q = E`, and reads `tr((ρ−σ)₊)` as the trace distance through
`traceDist_eq_eigPosSum` and `eigPosSum_eq_re_trace_posPart`. -/
theorem helstrom_le_povmAvgError {ρ σ E : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) (hE : IsBinaryPOVM E) :
    (1 - traceDist ρ σ) / 2 ≤ povmAvgError ρ σ E := by
  have hM : (ρ - σ).IsHermitian := hρ.1.isHermitian.sub hσ.1.isHermitian
  have hb := re_trace_mul_le_trace_posPart hM hE.1 hE.2
  have hcomm : (E * (ρ - σ)).trace = ((ρ - σ) * E).trace := Matrix.trace_mul_comm E (ρ - σ)
  have hD : traceDist ρ σ = (posPart hM).trace.re := by
    rw [traceDist_eq_eigPosSum hρ.1 hσ.1 hρ.2 hσ.2, eigPosSum_eq_re_trace_posPart]
  rw [povmAvgError_eq_half_one_sub hρ.2, hcomm, hD]
  linarith

/-- **Attainment at the Helstrom projector.** The positive-eigenvalue projection of `ρ − σ`
achieves the bound exactly, so `½(1 − D(ρ,σ))` is the discrimination *optimum* rather than a
merely valid floor. -/
theorem povmAvgError_posProj_eq {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) :
    povmAvgError ρ σ (posProj (hρ.1.isHermitian.sub hσ.1.isHermitian))
      = (1 - traceDist ρ σ) / 2 := by
  rw [povmAvgError_eq_half_one_sub hρ.2, traceDist_eq_eigPosSum hρ.1 hσ.1 hρ.2 hσ.2,
    eigPosSum_eq_re_trace_posProj]
  rfl

/-- **The Holevo–Helstrom theorem.** `½(1 − D(ρ,σ))` is the *least* average error achievable by
any two-outcome POVM on the equiprobable pair `(ρ, σ)` — a lower bound (`helstrom_le_povmAvgError`)
that is a member of the achievable set (`povmAvgError_posProj_eq`, at the projective measurement
`posProj(ρ−σ)`). Stating it as `IsLeast` is what rules out the bound being vacuous or loose. -/
theorem helstrom_isLeast_povmAvgError {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) :
    IsLeast {x : ℝ | ∃ E : Matrix ι ι ℂ, IsBinaryPOVM E ∧ povmAvgError ρ σ E = x}
      ((1 - traceDist ρ σ) / 2) := by
  refine ⟨⟨posProj (hρ.1.isHermitian.sub hσ.1.isHermitian), ?_, povmAvgError_posProj_eq hρ hσ⟩, ?_⟩
  · exact isBinaryPOVM_of_projection (posProj_isHermitian _) (posProj_idem _)
  · rintro x ⟨E, hE, rfl⟩
    exact helstrom_le_povmAvgError hρ hσ hE

/-! ## The fidelity floor -/

/-- `√(1 − x) ≤ 1 − x/2` on `[0,1]` — the elementary step converting the Fuchs–van de Graaf
trace-distance bound into a fidelity floor on the error. Both sides are nonnegative there and
squaring gives `1 − x ≤ 1 − x + x²/4`. -/
theorem sqrt_one_sub_le_one_sub_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sqrt (1 - x) ≤ 1 - x / 2 := by
  rw [show (1 : ℝ) - x / 2 = Real.sqrt ((1 - x / 2) ^ 2) from
    (Real.sqrt_sq (by linarith)).symm]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- **The quantum two-state discrimination floor: `¼F(ρ,σ)² ≤ P_err`.**

For equiprobable density operators `ρ, σ`, *no* two-outcome POVM — projective or not — attains
average error below a quarter of the squared root fidelity. Composed from the Holevo–Helstrom
optimum `½(1 − D)` (`helstrom_le_povmAvgError`, tight by `helstrom_isLeast_povmAvgError`), the
Fuchs–van de Graaf upper bound `D ≤ √(1 − F²)`
(`FidelityUpperBound.traceDist_le_sqrt_one_sub_sqrtFidelity_sq`) and `√(1−x) ≤ 1 − x/2`.

This is the statement whose *diagonal restriction* is the classical Bhattacharyya/Le Cam floor:
see `Detection/ShotNoise.lean`, where the classical two-outcome experiment is exhibited as one
particular POVM (`povmAvgError_diagonal_eq_avgAssignmentError`) and the Wave-1 Poisson floor is
then dominated by this bound rather than by a re-derived classical AM–GM step. -/
theorem quarter_sqrtFidelity_sq_le_povmAvgError {ρ σ E : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) (hE : IsBinaryPOVM E) :
    1 / 4 * sqrtFidelity hρ.1 hσ.1 ^ 2 ≤ povmAvgError ρ σ E := by
  have hF := sqrtFidelity_mem_Icc hρ hσ
  have hx1 : sqrtFidelity hρ.1 hσ.1 ^ 2 ≤ 1 := by nlinarith [hF.1, hF.2]
  have hs := sqrt_one_sub_le_one_sub_half (sq_nonneg (sqrtFidelity hρ.1 hσ.1)) hx1
  have hFvdG := traceDist_le_sqrt_one_sub_sqrtFidelity_sq hρ.1 hσ.1 hρ.2 hσ.2
  have hH := helstrom_le_povmAvgError hρ hσ hE
  linarith

end SKEFTHawking.QuantumNetwork
