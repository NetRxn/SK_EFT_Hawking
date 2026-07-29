import SKEFTHawking.QuantumNetwork.TraceNormCauchySchwarz
import SKEFTHawking.QuantumNetwork.DiamondNormChoi

/-!
# Fidelity under reversible (unitary) channels (Phase 6AJ — fidelity-domain data processing)

The trace-distance data-processing inequality (`traceDist_krausMap_le`, CPTP contractivity) is the
"distinguishability decreases" half of the metric structure on quantum states. Its fidelity-domain
partner is Uhlmann's monotonicity `F((Φ⊗id)ρ, (Φ⊗id)σ) ≥ F(ρ, σ)` (fidelity *increases* under a
CPTP map). This module ships the **reversible (unitary) case as an equality** — fidelity is exactly
invariant under conjugation by a unitary, `F(UρUᴴ, UσUᴴ) = F(ρ, σ)` — the data-processing statement
for unitary channels (and a building block for any reversible network).

Everything routes through the PSD-square-root-uniqueness workhorse `posSemidef_eq_of_mul_self_eq`
(NO continuous-functional-calculus conjugation lemma is needed): `√(U M Uᴴ) = U (√M) Uᴴ` and
`|U A Uᴴ| = U |A| Uᴴ` both follow because both sides are PSD with equal squares, and the trace norm
is then unitarily invariant by trace cyclicity.

**Status of general CPTP monotonicity (route mapped — Wave 6AJ.0 scout + Explore fan-out; route
bricks RE-VERIFIED at Mathlib v4.32.0 `81a5d257`, 2026-07-29).** The *general* / mixed-unitary
Uhlmann monotonicity is the target of an in-progress continuation, NOT a permanent fence.

> ⚠ **Do NOT replace this route with PhysLib's `fidelity_channel_nondecreasing`.** That declaration
> exists (`QuantumInfo/States/Mixed/Fidelity.lean`) and states exactly the general monotonicity —
> but it is `@[sorryful]` with body `sorry`, at our pin `c4843367` **and** at the earlier
> `69197c54`. A 2026-06-08 assessment recorded it as discharging this fence and recommended
> stopping local work (`docs/assessments/UpstreamContributionDisposition.md`, §3.1 row 5 /
> Track R3); that recommendation is **withdrawn** — it confirmed the declaration existed without
> checking it was proved. This module never acted on it, and should not.
> See `docs/assessments/UpstreamDisposition_Revalidation_2026-07-29.md` §0.

Route bricks confirmed still present at v4.32.0: `fromBlocks₁₁` / `fromBlocks₂₂`
(`Mathlib/LinearAlgebra/Matrix/PosDef.lean`), `star_left_conjugate_le_conjugate`,
`conjugate_le_conjugate_of_nonneg`, `Matrix.PosSemidef.kronecker`, `CFC.monotone_sqrt`. The most reachable route is the **block-PSD / Alberti
SDP characterization** `F(ρ,σ) = max{ Re tr X : [[ρ, X],[Xᴴ, σ]] ⪰ 0 }`, for which Mathlib ships the
Schur-complement support (`Matrix.PosDef.fromBlocks₂₂` / `fromBlocks₁₁`,
`Matrix/LinearAlgebra/Matrix/PosDef.lean`) and the conjugation-monotonicity bricks
(`star_left_conjugate_le_conjugate`, `conjugate_le_conjugate_of_nonneg`, `Matrix.PosSemidef.kronecker`).
With the block characterization in hand, mixed-unitary monotonicity is immediate — the feasible `X` for
`(ρ,σ)`, conjugated by `∑ pᵢ Uᵢ`, is feasible for `(Φρ,Φσ)` with the same trace — and joint concavity
drops out as a corollary. The one genuinely new brick is a `traceNorm` Cauchy–Schwarz bound
`Re tr(√ρ · K · √σ) ≤ ‖√σ √ρ‖₁` (provable from the shipped `traceNorm_mul_le` + `psdSqrt` primitives).
Operator-monotone `CFC.monotone_sqrt` is present; Sion minimax / Lieb concavity / Stinespring are
absent but the block route does not need them. NO axiom is shipped; the reversible-channel equality
below is the in-hand deliverable.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation of a positive-semidefinite matrix by `U` on the left / `Uᴴ` on the right is PSD:
`U M Uᴴ ⪰ 0`. -/
theorem posSemidef_unitary_conj {M : Matrix ι ι ℂ} (U : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    (U * M * Uᴴ).PosSemidef := by
  have h := hM.conjTranspose_mul_mul_same Uᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- **`√(U M Uᴴ) = U (√M) Uᴴ`** for `U` unitary (`Uᴴ U = 1`): both sides are PSD and square to
`U M Uᴴ`, so they agree by PSD-square-root uniqueness. -/
theorem psdSqrt_unitary_conj {M U : Matrix ι ι ℂ} (hM : M.PosSemidef) (hU : Uᴴ * U = 1) :
    psdSqrt (posSemidef_unitary_conj U hM) = U * psdSqrt hM * Uᴴ := by
  refine posSemidef_eq_of_mul_self_eq (psdSqrt_posSemidef _)
    (posSemidef_unitary_conj U (psdSqrt_posSemidef hM)) ?_
  rw [psdSqrt_mul_self]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U (psdSqrt hM * Uᴴ), hU, Matrix.one_mul,
    ← Matrix.mul_assoc (psdSqrt hM) (psdSqrt hM) Uᴴ, psdSqrt_mul_self]

/-- **`|U A Uᴴ| = U |A| Uᴴ`** for `U` unitary: the operator modulus commutes with unitary
conjugation (same PSD-square-root-uniqueness argument applied to `(U A Uᴴ)ᴴ(U A Uᴴ) = U (AᴴA) Uᴴ`). -/
theorem absOp_unitary_conj {A U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) :
    absOp (U * A * Uᴴ) = U * absOp A * Uᴴ := by
  refine posSemidef_eq_of_mul_self_eq (absOp_posSemidef _)
    (posSemidef_unitary_conj U (absOp_posSemidef A)) ?_
  rw [absOp_mul_self]
  have hL : (U * A * Uᴴ)ᴴ * (U * A * Uᴴ) = U * (Aᴴ * A) * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U (A * Uᴴ), hU, Matrix.one_mul]
  have hR : (U * absOp A * Uᴴ) * (U * absOp A * Uᴴ) = U * (Aᴴ * A) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U (absOp A * Uᴴ), hU, Matrix.one_mul,
      ← Matrix.mul_assoc (absOp A) (absOp A) Uᴴ, absOp_mul_self, Matrix.mul_assoc Aᴴ A Uᴴ]
  rw [hL, hR]

/-- **The trace norm is unitarily invariant:** `‖U A Uᴴ‖₁ = ‖A‖₁` for `U` unitary. The modulus
conjugates (`absOp_unitary_conj`) and the trace is cyclic, so `tr(U |A| Uᴴ) = tr(|A| · Uᴴ U) =
tr|A|`. -/
theorem traceNorm_unitary_conj {A U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) :
    traceNorm (U * A * Uᴴ) = traceNorm A := by
  rw [traceNorm_eq_trace_absOp, absOp_unitary_conj hU, traceNorm_eq_trace_absOp]
  congr 1
  rw [Matrix.trace_mul_comm (U * absOp A) Uᴴ, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- **Fidelity is invariant under conjugation by a unitary — fidelity data processing for reversible
channels.** `F(UρUᴴ, UσUᴴ) = F(ρ, σ)` for `U` unitary (`Uᴴ U = 1`). This is the equality form of
Uhlmann monotonicity on the reversible (unitary-channel) subclass: a reversible channel neither
increases nor decreases fidelity. (The general CPTP monotonicity is fenced — see the module
docstring.) -/
theorem sqrtFidelity_unitary_conj {ρ σ U : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hU : Uᴴ * U = 1) :
    sqrtFidelity (posSemidef_unitary_conj U hρ) (posSemidef_unitary_conj U hσ)
      = sqrtFidelity hρ hσ := by
  rw [sqrtFidelity, psdSqrt_unitary_conj hρ hU, psdSqrt_unitary_conj hσ hU]
  have hmul : (U * psdSqrt hσ * Uᴴ) * (U * psdSqrt hρ * Uᴴ)
      = U * (psdSqrt hσ * psdSqrt hρ) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U (psdSqrt hρ * Uᴴ), hU, Matrix.one_mul]
  rw [hmul, traceNorm_unitary_conj hU, sqrtFidelity]

end SKEFTHawking.QuantumNetwork
