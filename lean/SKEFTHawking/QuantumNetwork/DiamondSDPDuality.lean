import SKEFTHawking.QuantumNetwork.DiamondSDPCone
import SKEFTHawking.QuantumNetwork.FidelityBounds
import Mathlib.Analysis.Convex.Cone.InnerDual

/-!
# PSD-cone self-duality on the diamond-SDP carrier (Phase 6AI — `≥` direction, Farkas brick A)

The conic Farkas lemma (`ProperCone.relative_hyperplane_separation`) expresses dual feasibility of
the diamond-SDP as membership of a target point in the (closed) image of the PSD product cone, and
its separating certificate lives in the **inner dual** of that cone. To decode both sides we need
the **self-duality of the PSD cone** under the real Frobenius inner product
`⟪A,B⟫ = Re tr(A·B)` on `HermCarrier ι`:

`Y ∈ innerDual psdProperCone ↔ Y.toSA.1.PosSemidef`.

* `←` (`le_innerDual`): for PSD `Y`, every PSD `X` has `0 ≤ Re tr(X·Y)` — this is `trace_mul_nonneg`.
* `→` (`innerDual_le`): if `0 ≤ Re tr(X·Y)` for every PSD `X`, then testing against the rank-one
  PSD matrices `X = v vᴴ` (`Matrix.posSemidef_vecMulVec_self_star`) gives `0 ≤ ⟪v, Y v⟫` for all `v`,
  which (with `Y` Hermitian) is the quadratic-form characterization of `Y ⪰ 0`
  (`Matrix.posSemidef_iff_dotProduct_mulVec`).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

namespace HermCarrier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Trace of a rank-one times `M`:** `tr(v vᴴ · M) = ⟨v, M v⟩ = star v ⬝ᵥ (M *ᵥ v)`. -/
theorem trace_vecMulVec_mul (v : ι → ℂ) (M : Matrix ι ι ℂ) :
    (vecMulVec v (star v) * M).trace = star v ⬝ᵥ (M *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

omit [DecidableEq ι] in
/-- **The imaginary part of the Hermitian quadratic form vanishes:** for `M` Hermitian,
`⟨v, M v⟩ = star v ⬝ᵥ (M *ᵥ v)` is real. -/
theorem im_dotProduct_mulVec_hermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (v : ι → ℂ) :
    (star v ⬝ᵥ (M *ᵥ v)).im = 0 :=
  hM.im_star_dotProduct_mulVec_self v

/-- **PSD-cone self-duality (membership form).** A carrier element lies in the inner dual of the PSD
cone exactly when it is positive semidefinite. -/
theorem mem_innerDual_psdProperCone {Y : HermCarrier ι} :
    Y ∈ ProperCone.innerDual ((psdProperCone : ProperCone ℝ (HermCarrier ι)) : Set (HermCarrier ι))
      ↔ Y.toSA.1.PosSemidef := by
  rw [ProperCone.mem_innerDual]
  constructor
  · intro h
    have hHerm : Y.toSA.1.IsHermitian := by
      have := Y.toSA.2; rwa [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose] at this
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hHerm, fun v => ?_⟩
    -- rank-one PSD test matrix X₀ = v vᴴ
    have hX0psd : (vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
    set X0 : HermCarrier ι := ⟨⟨vecMulVec v (star v), by
      rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]; exact hX0psd.isHermitian.eq⟩⟩ with hX0
    have hX0mem : X0 ∈ (psdProperCone : ProperCone ℝ (HermCarrier ι)) := hX0psd
    have hre := h hX0mem
    rw [inner_eq] at hre
    -- ⟪X0, Y⟫ = Re tr(v vᴴ · Y) = Re ⟨v, Y v⟩
    have hval : (X0.toSA.1 * Y.toSA.1).trace = star v ⬝ᵥ (Y.toSA.1 *ᵥ v) := by
      show (vecMulVec v (star v) * Y.toSA.1).trace = _
      exact trace_vecMulVec_mul v Y.toSA.1
    rw [hval] at hre
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · simpa using hre
    · simpa using (im_dotProduct_mulVec_hermitian hHerm v).symm
  · intro hY X hX
    rw [SetLike.mem_coe, mem_psdProperCone] at hX
    rw [inner_eq]
    exact (Complex.le_def.mp (trace_mul_nonneg hX hY)).1

end HermCarrier

end SKEFTHawking.QuantumNetwork
