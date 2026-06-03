import SKEFTHawking.QuantumNetwork.DiamondNormDual

/-!
# The canonical positive-part dual witness (Phase 6AI — constructive optimal-witness extractor)

The arc's diamond-norm SDP work (Phases 6AE–6AH) proved both one-sided bounds of the Watrous Choi
sandwich, the weak-dual witness bound `diamondDist_le_dual_witness` (any feasible dual witness ⟹ an
upper bound), and per-channel EXACT strong duality (dephasing / depolarizing / amplitude-damping /
general Pauli) by exhibiting an optimal dual witness matching the primal lower bound.

This module supplies the **general constructive dual witness**: for *any* channel pair, the positive
part `C₊ = (J(Φ₁) − J(Φ₂))₊` of the Choi difference is always dual-feasible — it is PSD and it
dominates `C` in the Loewner order (because `C₊ − C = C₋`, the negative part, is PSD). Feeding it to
the weak-dual bound gives the explicit, fully general upper bound

  `diamondDist(Φ₁, Φ₂) ≤ ‖Tr₂ C₊‖`.

This is the canonical SDP dual witness and the "optimal-witness extractor" in the achievable sense:
the construction `W* = C₊` is explicit and general; it is OPTIMAL (closing the diamond distance
exactly) precisely for the channels whose worst-case input is the maximally-entangled state — the
Pauli / dephasing / depolarizing family, whose shipped exact witnesses *are* this `C₊` — and is
generally loose for non-Pauli-covariant channels (e.g. amplitude damping, whose worst-case input is
an unentangled product state, so its optimal witness is *not* `C₊`).

**Fence (verified, Wave 6AI.0 scout, interactive lean4 on Mathlib v4.29.1).** The fully-general
strong-duality EQUALITY `diamondDist = inf{ ‖Tr₂ W‖ : W ⪰ 0, W ⪰ C }` is NOT shipped: it requires
the *existence* of an optimal witness for every channel pair, i.e. SDP zero-gap. The pinned Mathlib
provides the separation substrate (`geometric_hahn_banach_compact_closed`, `ProperCone.hyperplane_separation`,
`ProperCone.innerDual` + bipolar `innerDual_innerDual`) and the order-theoretic saddle-point lemma
(`isSaddlePointOn_value`) with the easy minimax inequality (`iSup₂_iInf₂_le_iInf₂_iSup₂`), but it does
NOT provide an analytic Sion / von Neumann minimax for concave–convex real functions, Fenchel
conjugate biconjugate duality, or any conic / SDP / LP strong-duality (Slater zero-gap) theorem.
Assembling zero-gap for this operator-norm-objective LMI from raw Hahn–Banach separation is a genuine
multi-week formalization (re-deriving conic duality for this program). Per the project's no-axiom
policy this is FENCED, not axiomatized — the general constructive *upper* bound below is the shipped
deliverable, with per-channel exact strong duality already constructive elsewhere.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- **`C₊ − M = C₋`:** the positive part minus the matrix is the negative part (`max(x,0) − x =
max(−x,0)`). Proved without rewriting `M` (which appears inside the proof argument of `posPart`/
`negPart`), by abstracting the compound `posPart − negPart` via `sub_sub_cancel`. -/
theorem posPart_sub_self_eq_negPart {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) : posPart hM - M = negPart hM :=
  calc posPart hM - M
      = posPart hM - (posPart hM - negPart hM) := by rw [← self_eq_posPart_sub_negPart hM]
    _ = negPart hM := sub_sub_cancel _ _

variable {m n : ℕ}

/-- The Choi difference `C = J(Φ₁) − J(Φ₂)` is Hermitian (a difference of positive-semidefinite Choi
matrices). -/
theorem choiDiff_isHermitian (K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)).IsHermitian :=
  (choiMatrix_krausMap_posSemidef K₁).isHermitian.sub (choiMatrix_krausMap_posSemidef K₂).isHermitian

/-- **The positive part `C₊` of the Choi difference is dual-feasible:** it dominates `C` in the
Loewner order, `C₊ − C = C₋ ⪰ 0` (the negative part). -/
theorem posPart_choiDiff_sub_posSemidef (K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    (posPart (choiDiff_isHermitian K₁ K₂)
      - (choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂))).PosSemidef := by
  rw [posPart_sub_self_eq_negPart (choiDiff_isHermitian K₁ K₂)]
  exact negPart_posSemidef _

/-- **The canonical positive-part dual witness — general constructive diamond upper bound.** For any
two channels `Φ₁, Φ₂` the positive part `C₊ = (J(Φ₁) − J(Φ₂))₊` of the Choi difference is an explicit
dual-feasible witness, giving

  `diamondDist(Φ₁, Φ₂) ≤ ‖Tr₂ C₊‖`.

This generalizes both `diamondDist_le_choi_opNorm` (the cruder `W = ‖C‖·1` witness) and every shipped
per-channel optimal witness in one construction. It is tight (closes the diamond distance) exactly for
channels whose worst-case input is the maximally-entangled state (Pauli / dephasing / depolarizing),
and loose otherwise (e.g. amplitude damping). The fully-general strong-duality *equality* is fenced —
see the module docstring. -/
theorem diamondDist_le_ptrace2_posPart [NeZero n] {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    diamondDist K₁ K₂ ≤ ‖ptrace2 (posPart (choiDiff_isHermitian K₁ K₂))‖ :=
  diamondDist_le_dual_witness hK₁ hK₂ (posPart_posSemidef _)
    (posPart_choiDiff_sub_posSemidef K₁ K₂)

end SKEFTHawking.QuantumNetwork
