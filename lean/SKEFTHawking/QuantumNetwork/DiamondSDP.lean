import SKEFTHawking.QuantumNetwork.DiamondNormWitness
import SKEFTHawking.QuantumNetwork.SelfAdjointInnerProduct

/-!
# The Choi-SDP dual value and weak duality (Phase 6AI — toward `diamondDist_eq_choiSDP`)

The dual semidefinite program for the diamond distance:
`choiDualValue Φ₁ Φ₂ = inf{ ‖Tr₂ W‖ : W ⪰ 0, W ⪰ J(Φ₁)−J(Φ₂) }`.

This file ships the **weak-duality `≤`** direction of the strong-duality equality
`diamondDist = choiDualValue`: every dual-feasible witness upper-bounds the diamond distance
(`diamondDist_le_dual_witness`), so the diamond distance is below the infimum. The matching `≥`
(zero duality gap / Watrous strong duality) uses the real-Frobenius `InnerProductSpace ℝ` on
self-adjoint matrices (`SelfAdjointInnerProduct.lean`) + `ProperCone.hyperplane_separation` —
the next brick.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {m n : ℕ}

/-- **The Choi-SDP dual value** `inf{ ‖Tr₂ W‖ : W ⪰ 0, W ⪰ J(Φ₁)−J(Φ₂) }`. -/
noncomputable def choiDualValue (K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {r | ∃ W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, W.PosSemidef ∧
    (W - (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).PosSemidef ∧ r = ‖ptrace2 W‖}

/-- The dual feasible-value set is nonempty — the positive part `C₊` of the Choi difference is a
feasible witness. -/
theorem choiDualValue_set_nonempty (K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    {r | ∃ W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, W.PosSemidef ∧
      (W - (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).PosSemidef
        ∧ r = ‖ptrace2 W‖}.Nonempty :=
  ⟨_, posPart (choiDiff_isHermitian K₁ K₂), posPart_posSemidef _,
    posPart_choiDiff_sub_posSemidef K₁ K₂, rfl⟩

/-- **Weak duality `diamondDist ≤ choiDualValue`.** Each dual-feasible witness upper-bounds the
diamond distance (`diamondDist_le_dual_witness`), so the diamond distance is at most the dual
infimum. The matching `≥` is the strong-duality (zero-gap) direction. -/
theorem diamondDist_le_choiDualValue [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    diamondDist K₁ K₂ ≤ choiDualValue K₁ K₂ := by
  refine le_csInf (choiDualValue_set_nonempty K₁ K₂) ?_
  rintro r ⟨W, hW, hWC, rfl⟩
  exact diamondDist_le_dual_witness hK₁ hK₂ hW hWC

end SKEFTHawking.QuantumNetwork
