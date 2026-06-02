import SKEFTHawking.QuantumNetwork.FidelityBounds
import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz

/-!
# Fuchs–van de Graaf upper bound `D ≤ √(1 − F²)` (Phase 6AF-10)

The companion to the lower bound `1 − F ≤ D` (in `FidelityBounds.lean`). The standard textbook
proofs route through Uhlmann's purification theorem (absent from Mathlib at pin); this file follows
the **purification-free Holevo–Helstrom + classical-Fuchs–van de Graaf** route (Watrous Thm 3.39 /
Ex. 3.6), reusing the shipped trace-distance / `eigPosSum` / `posProj` substrate.

Build order: (1) ✅ the Helstrom value `D(ρ,σ) = eigPosSum(ρ−σ)` (`traceDist_eq_eigPosSum`);
(2) ✅ the **classical** Fuchs–van de Graaf inequality on probability pairs (`classical_fvdg`,
pure ℝ); (3) the fidelity↔Bhattacharyya bound `F(ρ,σ) ≤ √(tr Pσ · tr Pρ) + √(tr P'σ · tr P'ρ)`
for the binary measurement `{P, 1−P}` (fidelity data-processing); (4) assembly.

**ALL FOUR STEPS COMPLETE (2026-06-02).** Step (3) reduces — via the shipped matrix-CS keystone
`re_trace_conjTranspose_mul_sq_le` — to the Schatten-2 bound `traceNorm(√σ·P·√ρ) ≤ √(tr Pσ)·√(tr Pρ)`
(`traceNorm_sqrtMul_proj_le`), itself a corollary of the general Schatten-2 CS `traceNorm_mul_le`
(`TraceNormCauchySchwarz.lean`): the trace-norm/polar layer Mathlib lacks was built from scratch via
a **determinant-based polar unitary** for invertible `M` (NO partial-isometry/SVD) plus a
**charpoly-roots perturbation** extending to all matrices by `continuous_traceNorm`. The headline
`traceDist_le_sqrt_one_sub_sqrtFidelity_sq` is PROVEN; the prior "needs trace-norm-dual / multi-week"
note was the over-wide fence, now discharged.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Helstrom value of the trace distance**: for density operators, `D(ρ,σ) = eigPosSum(ρ−σ)`
(the sum of the positive eigenvalues of `ρ−σ`). Since `ρ−σ` is traceless, `‖ρ−σ‖₁ = 2·eigPosSum`,
so `D = ½‖ρ−σ‖₁ = eigPosSum`. The optimal Helstrom measurement is `posProj(ρ−σ)`. -/
theorem traceDist_eq_eigPosSum {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htρ : ρ.trace = 1) (htσ : σ.trace = 1) :
    traceDist ρ σ = eigPosSum (hρ.isHermitian.sub hσ.isHermitian) := by
  have htr0 : (ρ - σ).trace.re = 0 := by
    rw [Matrix.trace_sub, htρ, htσ]; simp
  rw [traceDist, traceNorm_hermitian_eq (hρ.isHermitian.sub hσ.isHermitian), htr0]
  ring

/-- **Classical Fuchs–van de Graaf** on a probability pair: for `p₀,p₁,q₀,q₁ ≥ 0` with
`p₀+p₁ = 1 = q₀+q₁`, the total-variation distance and Bhattacharyya coefficient satisfy
`(½(|p₀−q₀|+|p₁−q₁|))² + (√(p₀q₀)+√(p₁q₁))² ≤ 1`. Pure-ℝ, via AM–GM `|a−b| ≥ (√a−√b)²` and
Cauchy–Schwarz. -/
theorem classical_fvdg {p0 p1 q0 q1 : ℝ} (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hq0 : 0 ≤ q0)
    (hq1 : 0 ≤ q1) (hp : p0 + p1 = 1) (hq : q0 + q1 = 1) :
    (2⁻¹ * (|p0 - q0| + |p1 - q1|)) ^ 2
      + (Real.sqrt (p0 * q0) + Real.sqrt (p1 * q1)) ^ 2 ≤ 1 := by
  -- total variation of a pair: ½(|p₀−q₀|+|p₁−q₁|) = |p₀−q₀| (since p₁−q₁ = −(p₀−q₀))
  have hsub : p1 - q1 = -(p0 - q0) := by linarith
  have htv : 2⁻¹ * (|p0 - q0| + |p1 - q1|) = |p0 - q0| := by
    rw [hsub, abs_neg]; ring
  rw [htv, sq_abs]
  set a := Real.sqrt (p0 * q0) with ha
  set b := Real.sqrt (p1 * q1) with hb
  have ha2 : a ^ 2 = p0 * q0 := Real.sq_sqrt (mul_nonneg hp0 hq0)
  have hb2 : b ^ 2 = p1 * q1 := Real.sq_sqrt (mul_nonneg hp1 hq1)
  -- key AM–GM: 2·√(p₀q₀)·√(p₁q₁) = 2√((p₀p₁)(q₀q₁)) ≤ p₀p₁ + q₀q₁
  have hab : a * b = Real.sqrt (p0 * p1) * Real.sqrt (q0 * q1) := by
    rw [ha, hb, ← Real.sqrt_mul (mul_nonneg hp0 hq0), ← Real.sqrt_mul (mul_nonneg hp0 hp1)]
    congr 1; ring
  have hkey : 2 * (a * b) ≤ p0 * p1 + q0 * q1 := by
    rw [hab]
    nlinarith [sq_nonneg (Real.sqrt (p0 * p1) - Real.sqrt (q0 * q1)),
      Real.sq_sqrt (mul_nonneg hp0 hp1), Real.sq_sqrt (mul_nonneg hq0 hq1)]
  nlinarith [ha2, hb2, hkey, hp, hq, mul_nonneg hp0 hq0, mul_nonneg hp1 hq1]

/-- **Projection-block Cauchy–Schwarz**: for density operators and a projection `P` (`Pᴴ=P`,
`P²=P`), `traceNorm(√σ·P·√ρ) ≤ √(tr(Pσ)) · √(tr(Pρ))`. From the Schatten-2 CS `traceNorm_mul_le`
applied to `(√σ·P)·(P·√ρ)`, with `((√σP)ᴴ(√σP)) = PσP` (trace `tr(Pσ)`) and `((P√ρ)ᴴ(P√ρ)) = √ρP√ρ`
(trace `tr(Pρ)`). -/
theorem traceNorm_sqrtMul_proj_le {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {P : Matrix ι ι ℂ} (hPh : P.IsHermitian) (hPi : P * P = P) :
    traceNorm (psdSqrt hσ * P * psdSqrt hρ)
      ≤ Real.sqrt ((P * σ).trace.re) * Real.sqrt ((P * ρ).trace.re) := by
  have hsplit : psdSqrt hσ * P * psdSqrt hρ = (psdSqrt hσ * P) * (P * psdSqrt hρ) := by
    rw [show psdSqrt hσ * P * (P * psdSqrt hρ) = psdSqrt hσ * (P * P) * psdSqrt hρ by noncomm_ring,
      hPi]
  have hX : ((psdSqrt hσ * P)ᴴ * (psdSqrt hσ * P)).trace.re = (P * σ).trace.re := by
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian hσ).eq, hPh.eq,
      show P * psdSqrt hσ * (psdSqrt hσ * P) = P * (psdSqrt hσ * psdSqrt hσ) * P by noncomm_ring,
      psdSqrt_mul_self hσ, Matrix.trace_mul_comm (P * σ) P, ← Matrix.mul_assoc, hPi]
  have hY : ((P * psdSqrt hρ)ᴴ * (P * psdSqrt hρ)).trace.re = (P * ρ).trace.re := by
    rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian hρ).eq, hPh.eq,
      show psdSqrt hρ * P * (P * psdSqrt hρ) = psdSqrt hρ * (P * P) * psdSqrt hρ by noncomm_ring,
      hPi, Matrix.trace_mul_comm (psdSqrt hρ * P) (psdSqrt hρ), ← Matrix.mul_assoc,
      psdSqrt_mul_self hρ, Matrix.trace_mul_comm ρ P]
  rw [hsplit]
  have := traceNorm_mul_le (psdSqrt hσ * P) (P * psdSqrt hρ)
  rwa [hX, hY] at this

/-- **`F ≤ BC` (fidelity ≤ measured Bhattacharyya)** for a projective measurement `{P, 1−P}`:
`F(ρ,σ) ≤ √(tr Pσ)·√(tr Pρ) + √(tr(1−P)σ)·√(tr(1−P)ρ)`. Split `√σ√ρ = √σP√ρ + √σ(1−P)√ρ`
(trace-norm triangle) and bound each block by `traceNorm_sqrtMul_proj_le`. -/
theorem sqrtFidelity_le_proj_bc {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {P : Matrix ι ι ℂ} (hPh : P.IsHermitian) (hPi : P * P = P) :
    sqrtFidelity hρ hσ
      ≤ Real.sqrt ((P * σ).trace.re) * Real.sqrt ((P * ρ).trace.re)
        + Real.sqrt (((1 - P) * σ).trace.re) * Real.sqrt (((1 - P) * ρ).trace.re) := by
  have hPh' : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hPh
  have hPi' : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPi]; abel
  rw [sqrtFidelity]
  have hsplit : psdSqrt hσ * psdSqrt hρ
      = psdSqrt hσ * P * psdSqrt hρ + psdSqrt hσ * (1 - P) * psdSqrt hρ := by
    rw [show psdSqrt hσ * P * psdSqrt hρ + psdSqrt hσ * (1 - P) * psdSqrt hρ
        = psdSqrt hσ * (P + (1 - P)) * psdSqrt hρ by noncomm_ring,
      show P + (1 - P) = (1 : Matrix ι ι ℂ) by abel, Matrix.mul_one]
  rw [hsplit]
  exact (traceNorm_triangle _ _).trans
    (add_le_add (traceNorm_sqrtMul_proj_le hρ hσ hPh hPi)
      (traceNorm_sqrtMul_proj_le hρ hσ hPh' hPi'))

/-- **Fuchs–van de Graaf UPPER bound `D(ρ,σ) ≤ √(1 − F(ρ,σ)²)`** for density operators —
purification-FREE, via Holevo–Helstrom + classical Fuchs–van de Graaf. At the optimal Helstrom
projector `P = posProj(ρ−σ)`, the trace distance is the total variation `D = p₀−q₀` of the
measured outcome distributions (`p₀=tr Pρ, q₀=tr Pσ`), the measured Bhattacharyya coefficient
dominates the fidelity (`F ≤ √(p₀q₀)+√(p₁q₁)`, `sqrtFidelity_le_proj_bc`), and the classical
inequality `D² + BC² ≤ 1` (`classical_fvdg`) closes `D² ≤ 1 − F²`. -/
theorem traceDist_le_sqrt_one_sub_sqrtFidelity_sq {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (htρ : ρ.trace = 1) (htσ : σ.trace = 1) :
    traceDist ρ σ ≤ Real.sqrt (1 - sqrtFidelity hρ hσ ^ 2) := by
  have hAB : (ρ - σ).IsHermitian := hρ.isHermitian.sub hσ.isHermitian
  set P := posProj hAB with hPdef
  have hPh : P.IsHermitian := posProj_isHermitian hAB
  have hPi : P * P = P := posProj_idem hAB
  have hPpsd : P.PosSemidef := by
    rw [show P = Pᴴ * P by rw [hPh.eq, hPi]]; exact Matrix.posSemidef_conjTranspose_mul_self P
  have hP'psd : (1 - P).PosSemidef := one_sub_posSemidef_of_projection hPh hPi
  set p0 := (P * ρ).trace.re with hp0def
  set q0 := (P * σ).trace.re with hq0def
  set p1 := ((1 - P) * ρ).trace.re with hp1def
  set q1 := ((1 - P) * σ).trace.re with hq1def
  have hp0 : 0 ≤ p0 := by
    have := (Complex.le_def.mp (trace_mul_nonneg hPpsd hρ)).1; simpa using this
  have hq0 : 0 ≤ q0 := by
    have := (Complex.le_def.mp (trace_mul_nonneg hPpsd hσ)).1; simpa using this
  have hp1 : 0 ≤ p1 := by
    have := (Complex.le_def.mp (trace_mul_nonneg hP'psd hρ)).1; simpa using this
  have hq1 : 0 ≤ q1 := by
    have := (Complex.le_def.mp (trace_mul_nonneg hP'psd hσ)).1; simpa using this
  have hsump : p0 + p1 = 1 := by
    rw [hp0def, hp1def, ← Complex.add_re, ← Matrix.trace_add,
      show P * ρ + (1 - P) * ρ = ρ by rw [← Matrix.add_mul]; rw [add_sub_cancel, Matrix.one_mul],
      htρ, Complex.one_re]
  have hsumq : q0 + q1 = 1 := by
    rw [hq0def, hq1def, ← Complex.add_re, ← Matrix.trace_add,
      show P * σ + (1 - P) * σ = σ by rw [← Matrix.add_mul]; rw [add_sub_cancel, Matrix.one_mul],
      htσ, Complex.one_re]
  -- Helstrom value: D = p0 - q0 ≥ 0
  have hD : traceDist ρ σ = p0 - q0 := by
    rw [traceDist_eq_eigPosSum hρ hσ htρ htσ, eigPosSum_eq_re_trace_posProj hAB]
    show (P * (ρ - σ)).trace.re = p0 - q0
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have hD0 : 0 ≤ traceDist ρ σ := traceDist_nonneg ρ σ
  have hD0' : 0 ≤ p0 - q0 := hD ▸ hD0
  -- F ≤ BC
  have hFBC : sqrtFidelity hρ hσ ≤ Real.sqrt (p0 * q0) + Real.sqrt (p1 * q1) := by
    have h := sqrtFidelity_le_proj_bc hρ hσ hPh hPi
    rw [← hp0def, ← hq0def, ← hp1def, ← hq1def, ← Real.sqrt_mul hq0, ← Real.sqrt_mul hq1,
      mul_comm q0 p0, mul_comm q1 p1] at h
    exact h
  -- classical FvdG + the TV identity 2⁻¹(|p0-q0|+|p1-q1|) = D
  have htv : 2⁻¹ * (|p0 - q0| + |p1 - q1|) = traceDist ρ σ := by
    have h1 : p1 - q1 = -(p0 - q0) := by linarith [hsump, hsumq]
    rw [h1, abs_neg, hD, abs_of_nonneg hD0']; ring
  have hcf := classical_fvdg hp0 hp1 hq0 hq1 hsump hsumq
  rw [htv] at hcf
  -- D² ≤ 1 − F²
  have hF0 : 0 ≤ sqrtFidelity hρ hσ := sqrtFidelity_nonneg hρ hσ
  have hbc0 : 0 ≤ Real.sqrt (p0 * q0) + Real.sqrt (p1 * q1) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hle : traceDist ρ σ ^ 2 ≤ 1 - sqrtFidelity hρ hσ ^ 2 := by nlinarith [hcf, hFBC, hF0, hbc0]
  calc traceDist ρ σ = Real.sqrt (traceDist ρ σ ^ 2) := (Real.sqrt_sq hD0).symm
    _ ≤ Real.sqrt (1 - sqrtFidelity hρ hσ ^ 2) := Real.sqrt_le_sqrt hle

end SKEFTHawking.QuantumNetwork
