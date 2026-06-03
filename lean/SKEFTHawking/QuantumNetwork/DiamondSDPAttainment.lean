import SKEFTHawking.QuantumNetwork.DiamondSDP
import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper

/-!
# Toward attainment of the Choi-SDP dual value (Phase 6AI — `≥` direction, foundational lemmas)

Two reusable facts feeding the dual-attainment / strong-duality `≥` argument for
`diamondDist_eq_choiSDP`:

* `trace_ptrace2` — the partial trace `Tr₂` preserves the trace (`tr(Tr₂ W) = tr W`); the
  entrywise identity `(Tr₂ W) a a = ∑_x W (a,x)(a,x)` summed over `a` is the full trace over
  `Fin n × Fin n`.
* `dualObjective_trace_bound` — for a PSD dual witness `W`, the trace is controlled by the dual
  objective: `tr W = tr(Tr₂ W) ≤ card · ‖Tr₂ W‖`. This is the seed of the boundedness half of
  dual-sublevel compactness (`‖Tr₂ W‖ ≤ B ⇒ tr W ≤ card · B`).

The remaining attainment bricks (the `opNorm ≤ traceNorm` Frobenius bridge bounding `‖W‖` itself,
closedness of the feasible cone, finite-dimensional compactness, and `IsCompact.exists_isMinOn`),
followed by the Hahn–Banach separation against the attained primal optimum, complete the
strong-duality `≥` direction `choiDualValue ≤ diamondDist`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {n : ℕ}

/-- **Partial trace preserves the trace:** `tr(Tr₂ W) = tr W`. The diagonal entry
`(Tr₂ W) a a = ∑_x W (a,x)(a,x)`, and summing over `a` re-assembles the trace over `Fin n × Fin n`
(`Fintype.sum_prod_type`). -/
theorem trace_ptrace2 (W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) :
    (ptrace2 W).trace = W.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, ptrace2, Fintype.sum_prod_type]

/-- **Trace control by the dual objective.** For a positive-semidefinite dual witness `W`, the
trace is bounded by the dual objective `‖Tr₂ W‖` up to the dimension factor:
`tr W = tr(Tr₂ W) ≤ card · ‖Tr₂ W‖` (real parts). Uses `traceNorm_posSemidef`
(PSD ⇒ `traceNorm = Re tr`) on both `W` and `Tr₂ W`, the partial-trace trace identity, and the
shipped `traceNorm_le_card_mul_l2opNorm`. -/
theorem dualObjective_trace_bound [NeZero n]
    {W : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hW : W.PosSemidef) :
    (W.trace).re ≤ (Fintype.card (Fin n) : ℝ) * ‖ptrace2 W‖ := by
  have hpt : (ptrace2 W).PosSemidef := ptrace2_posSemidef hW
  calc (W.trace).re = (ptrace2 W).trace.re := by rw [trace_ptrace2]
    _ = traceNorm (ptrace2 W) := (traceNorm_posSemidef hpt).symm
    _ ≤ (Fintype.card (Fin n) : ℝ) * ‖ptrace2 W‖ := traceNorm_le_card_mul_l2opNorm (ptrace2 W)

end SKEFTHawking.QuantumNetwork
