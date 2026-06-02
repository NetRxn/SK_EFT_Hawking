import SKEFTHawking.QuantumNetwork.FidelityBounds

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

**Remaining-crux note (2026-06-02).** Step (3) reduces — via the shipped matrix-CS keystone
`re_trace_conjTranspose_mul_sq_le` — to the single Schatten-2 bound
`traceNorm(√σ · P · √ρ) ≤ √(tr Pσ) · √(tr Pρ)`. Through the keystone this needs the **trace-norm
dual characterization** `‖M‖₁ = sup_{U unitary} Re tr(U M)` (the EASY direction `Re tr(UM) ≤ ‖M‖₁`
follows from `re_trace_le_traceNorm` + trace-norm unitary-invariance; the HARD direction needs a
**polar unitary** `M = U|M|`). Mathlib at pin has NO trace-norm-dual / polar-decomposition lemma
(grep-verified, consistent with the Phase-6AF DR's absent-brick inventory), so this is a genuine
from-scratch ~6–8-lemma sub-build (eigendecomposition of `|M| = absOp M` → achieving unitary; the
singular-`M` partial-isometry→unitary extension is the delicate step, possibly via the shipped
`continuous_traceNorm` + an invertible-perturbation limit). Steps (1),(2) are shipped; (3),(4) are
the next increments.

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
`(½(|p₀−q₀|+|p₁−q₁|))² + (√(p₀q₀)+√(q₁q₁))² ≤ 1`. Pure-ℝ, via AM–GM `|a−b| ≥ (√a−√b)²` and
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

end SKEFTHawking.QuantumNetwork
