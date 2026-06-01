import SKEFTHawking.QuantumNetwork.MixedState

/-!
# CPTP channels and trace-distance contractivity (Phase 6AF-4)

A completely-positive trace-preserving (CPTP) quantum channel in concrete Kraus form
`Φ(ρ) = ∑ₖ Kₖ ρ Kₖᴴ` with `∑ₖ Kₖᴴ Kₖ = 1`, and the **data-processing inequality** for the
trace distance: `D(Φρ, Φσ) ≤ D(ρ, σ)`.

The contractivity is proven *without* the dual-norm characterization `‖A‖₁ = sup tr(PA)`
(which Mathlib lacks): for Hermitian `A = A⁺ − A⁻` (positive/negative parts, both PSD),
`‖Φ(A)‖₁ ≤ ‖Φ(A⁺)‖₁ + ‖Φ(A⁻)‖₁ = tr Φ(A⁺) + tr Φ(A⁻) = tr A⁺ + tr A⁻ = ‖A‖₁`,
using only the general trace-norm triangle (6AF-2), PSD-preservation, and trace-preservation.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A **Kraus channel** `Φ(ρ) = ∑ₖ Kₖ ρ Kₖᴴ`. Completely positive by construction. -/
noncomputable def krausMap (K : Fin m → Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ k, K k * ρ * (K k)ᴴ

/-- The **trace-preservation** condition `∑ₖ Kₖᴴ Kₖ = 1` (CPTP). -/
def IsKrausChannel (K : Fin m → Matrix ι ι ℂ) : Prop :=
  ∑ k, (K k)ᴴ * (K k) = 1

omit [DecidableEq ι] in
/-- The channel is additive (linear in the input state). -/
theorem krausMap_add (K : Fin m → Matrix ι ι ℂ) (ρ σ : Matrix ι ι ℂ) :
    krausMap K (ρ + σ) = krausMap K ρ + krausMap K σ := by
  unfold krausMap
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_add, Matrix.add_mul]

omit [DecidableEq ι] in
/-- The channel respects subtraction. -/
theorem krausMap_sub (K : Fin m → Matrix ι ι ℂ) (ρ σ : Matrix ι ι ℂ) :
    krausMap K (ρ - σ) = krausMap K ρ - krausMap K σ := by
  unfold krausMap
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] in
/-- The channel preserves positive semidefiniteness (each `Kₖ ρ Kₖᴴ` is PSD). -/
theorem krausMap_posSemidef (K : Fin m → Matrix ι ι ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) : (krausMap K ρ).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k _
  have h := hρ.conjTranspose_mul_mul_same ((K k)ᴴ)
  simpa [Matrix.conjTranspose_conjTranspose] using h

omit [DecidableEq ι] in
/-- The channel preserves Hermitian matrices. -/
theorem krausMap_isHermitian (K : Fin m → Matrix ι ι ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) : (krausMap K ρ).IsHermitian := by
  unfold krausMap Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun k _ => by
    simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hρ.eq, Matrix.mul_assoc]

/-- **Trace preservation**: `tr Φ(ρ) = tr ρ` for a Kraus channel (`∑ₖ Kₖᴴ Kₖ = 1`). -/
theorem trace_krausMap {K : Fin m → Matrix ι ι ℂ} (hK : IsKrausChannel K)
    (ρ : Matrix ι ι ℂ) : (krausMap K ρ).trace = ρ.trace := by
  unfold krausMap
  rw [Matrix.trace_sum]
  have hcyc : ∀ k, (K k * ρ * (K k)ᴴ).trace = ((K k)ᴴ * (K k) * ρ).trace :=
    fun k => Matrix.trace_mul_cycle _ _ _
  simp_rw [hcyc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

/-- A Kraus channel maps **density operators to density operators**. -/
theorem krausMap_isDensityOperator {K : Fin m → Matrix ι ι ℂ} (hK : IsKrausChannel K)
    {ρ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (krausMap K ρ) :=
  ⟨krausMap_posSemidef K hρ.1, by rw [trace_krausMap hK, hρ.2]⟩

/-- **`‖A‖₁ = tr A⁺ + tr A⁻`** for Hermitian `A` — the trace norm splits over the
positive/negative parts (`|x| = max(x,0) + max(−x,0)`). -/
theorem traceNorm_hermitian_eq_pos_add_neg {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    traceNorm A = (posPart hA).trace.re + (negPart hA).trace.re := by
  have hpos : (posPart hA).trace.re = ∑ i, max (hA.eigenvalues i) 0 :=
    (eigPosSum_eq_re_trace_posPart hA).symm
  have hneg : (negPart hA).trace.re = ∑ i, max (-(hA.eigenvalues i)) 0 := by
    rw [negPart, trace_cfc, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  rw [traceNorm_hermitian hA, hpos, hneg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_total 0 (hA.eigenvalues i) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add]

/-- **Trace-norm contractivity (data processing)**: `‖Φ(A)‖₁ ≤ ‖A‖₁` for a CPTP Kraus channel
`Φ` and Hermitian `A`. Proof via the positive/negative-part split — no dual-norm needed. -/
theorem traceNorm_krausMap_le {K : Fin m → Matrix ι ι ℂ} (hK : IsKrausChannel K)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    traceNorm (krausMap K A) ≤ traceNorm A := by
  have hsplit : krausMap K A = krausMap K (posPart hA) - krausMap K (negPart hA) := by
    conv_lhs => rw [self_eq_posPart_sub_negPart hA]
    rw [krausMap_sub]
  have htri : traceNorm (krausMap K (posPart hA) - krausMap K (negPart hA))
      ≤ traceNorm (krausMap K (posPart hA)) + traceNorm (krausMap K (negPart hA)) := by
    have h := traceNorm_triangle (krausMap K (posPart hA)) (-(krausMap K (negPart hA)))
    rwa [← sub_eq_add_neg, traceNorm_neg] at h
  have hP : traceNorm (krausMap K (posPart hA)) = (posPart hA).trace.re := by
    rw [traceNorm_posSemidef (krausMap_posSemidef K (posPart_posSemidef hA)), trace_krausMap hK]
  have hN : traceNorm (krausMap K (negPart hA)) = (negPart hA).trace.re := by
    rw [traceNorm_posSemidef (krausMap_posSemidef K (negPart_posSemidef hA)), trace_krausMap hK]
  rw [hsplit, traceNorm_hermitian_eq_pos_add_neg hA]
  calc traceNorm (krausMap K (posPart hA) - krausMap K (negPart hA))
      ≤ traceNorm (krausMap K (posPart hA)) + traceNorm (krausMap K (negPart hA)) := htri
    _ = (posPart hA).trace.re + (negPart hA).trace.re := by rw [hP, hN]

/-- **Trace-distance contractivity** `D(Φρ, Φσ) ≤ D(ρ, σ)` — the data-processing inequality for
the trace distance under any CPTP channel. -/
theorem traceDist_krausMap_le {K : Fin m → Matrix ι ι ℂ} (hK : IsKrausChannel K)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    traceDist (krausMap K ρ) (krausMap K σ) ≤ traceDist ρ σ := by
  unfold traceDist
  rw [← krausMap_sub]
  have h := traceNorm_krausMap_le hK (hρ.sub hσ)
  linarith

end SKEFTHawking.QuantumNetwork
