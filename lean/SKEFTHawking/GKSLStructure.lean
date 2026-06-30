import SKEFTHawking.LindbladGenerator

/-!
# GKSL structure theorem: canonical form + trace preservation (Phase 6BC, Wave 2)

The structural backbone of the GKSL generator `ℒ` defined in `LindbladGenerator.lean`:

* **Canonical form** (`gksl_canonical_form`) — the explicit pointwise action
  `ℒ(ρ) = −i[H,ρ] + Σ_k L_k ρ L_k† − ½{Σ_k L_k†L_k, ρ}`, assembling the three component
  apply-lemmas into the standard GKSL decomposition (Hamiltonian commutator + Kraus dissipator +
  anticommutator decay).
* **Trace preservation** (`gksl_trace_preserving`) — `Tr ℒ(ρ) = 0` for every `ρ`. The unitary part is
  traceless by cyclicity (`Tr(Hρ) = Tr(ρH)`); the dissipative gain `Σ_k Tr(L_k†L_k ρ)` (from
  `Tr(L_k ρ L_k†) = Tr(L_k†L_k ρ)`) exactly cancels the anticommutator loss `−Σ_k Tr(L_k†L_k ρ)`.
  Trace preservation is what makes `e^{tℒ}` map density matrices to density matrices (Wave 3).

Invariants (Phase 6BC): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new
project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.OpenSystems

open scoped Matrix
open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {κ : Type*} [Fintype κ]

/-- **GKSL canonical form.** The generator's explicit pointwise action: the Hamiltonian commutator
`−i[H,ρ]`, the Kraus dissipator `Σ_k L_k ρ L_k†`, and the anticommutator decay `−½{Σ_k L_k†L_k, ρ}`. -/
theorem gksl_canonical_form (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    lindbladGenerator H L ρ
      = -Complex.I • (H * ρ - ρ * H)
        + (∑ k, L k * ρ * (L k)ᴴ)
        + -(2⁻¹ : ℂ) • ((∑ k, (L k)ᴴ * L k) * ρ + ρ * (∑ k, (L k)ᴴ * L k)) := by
  simp only [lindbladGenerator, LinearMap.add_apply, lindbladHamPart_apply, lindbladJump_apply,
    lindbladAnticommPart_apply]

/-- **GKSL trace preservation.** `Tr ℒ(ρ) = 0` for every `ρ`: the unitary part is traceless by
cyclicity, and the Kraus gain `Σ_k Tr(L_k†L_k ρ)` exactly cancels the anticommutator loss. -/
theorem gksl_trace_preserving (H : Matrix d d ℂ) (L : κ → Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    (lindbladGenerator H L ρ).trace = 0 := by
  rw [gksl_canonical_form]
  have hgain : ∀ k, (L k * ρ * (L k)ᴴ).trace = ((L k)ᴴ * L k * ρ).trace := by
    intro k
    rw [Matrix.trace_mul_comm (L k * ρ) ((L k)ᴴ), ← mul_assoc]
  have hham : (-Complex.I • (H * ρ - ρ * H)).trace = 0 := by
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm ρ H, sub_self, smul_zero]
  have hjump : (∑ k, L k * ρ * (L k)ᴴ).trace = ∑ k, ((L k)ᴴ * L k * ρ).trace := by
    rw [Matrix.trace_sum]
    exact Finset.sum_congr rfl (fun k _ => hgain k)
  have hanti : (-(2⁻¹ : ℂ) • ((∑ k, (L k)ᴴ * L k) * ρ + ρ * (∑ k, (L k)ᴴ * L k))).trace
      = -(∑ k, ((L k)ᴴ * L k * ρ).trace) := by
    have hG : ((∑ k, (L k)ᴴ * L k) * ρ).trace = ∑ k, ((L k)ᴴ * L k * ρ).trace := by
      rw [Finset.sum_mul, Matrix.trace_sum]
    rw [Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_mul_comm ρ (∑ k, (L k)ᴴ * L k), hG, smul_eq_mul]
    ring
  rw [Matrix.trace_add, Matrix.trace_add, hham, hjump, hanti, zero_add, add_neg_cancel]

end SKEFTHawking.OpenSystems
