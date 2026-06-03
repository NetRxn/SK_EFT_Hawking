import SKEFTHawking.QuantumNetwork.CPTPChannel
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The diamond distance of quantum channels (Phase 6AF-6)

The operational **diamond distance** between two CPTP channels `Φ₁, Φ₂`,

  `diamondDist Φ₁ Φ₂ = sup_ρ D((Φ₁⊗id)ρ, (Φ₂⊗id)ρ)`   (`= ½‖Φ₁ − Φ₂‖_◇`),

the worst-case trace-distance distinguishability of the channels when they act on half of an
entangled state. This is the stabilized (tensor-with-identity) distinguishability that the
diamond norm measures.

The supremum is well-defined as a real number because the set is bounded above (every
`D ∈ [0,1]`, since each `(Φᵢ⊗id)ρ` is again a density operator) — Mathlib's `Real.sSup`
needs only boundedness, **not** attainment. The construction reuses the generalized trace-norm
/ CPTP layer instantiated at the doubled index `Fin n × Fin n`.

Proven: the tensor channel `Φ⊗id` is CPTP; `diamondDist` is nonnegative, bounded by `1`,
symmetric, and vanishes on the diagonal — a genuine `[0,1]`-valued distinguishability metric.
Deferred (documented): attainment of the sup (needs spectral-function continuity) and the
Choi-matrix SDP characterization.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

variable {m n : ℕ}

/-- The Kraus operators of the **stabilized channel `Φ ⊗ id`**: `Kₖ ↦ Kₖ ⊗ I`, acting on the
doubled space `Fin n × Fin n` (system ⊗ ancilla). -/
noncomputable def tensorKraus (K : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    Fin m → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun k => K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)

/-- Kronecker distributes over a finite sum in the left factor:
`∑ₖ (Aₖ ⊗ B) = (∑ₖ Aₖ) ⊗ B`. -/
theorem sum_kronecker_left (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) : (∑ k, A k ⊗ₖ B) = (∑ k, A k) ⊗ₖ B := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  simp only [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

/-- **`Φ ⊗ id` is again a CPTP (Kraus) channel**: `∑ₖ (Kₖ⊗I)ᴴ(Kₖ⊗I) = (∑ₖ KₖᴴKₖ)⊗I = 1⊗1 = 1`. -/
theorem isKrausChannel_tensorKraus {K : Fin m → Matrix (Fin n) (Fin n) ℂ}
    (hK : IsKrausChannel K) : IsKrausChannel (tensorKraus K) := by
  unfold IsKrausChannel tensorKraus
  have hstep : ∀ k, (K k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * (K k ⊗ₖ 1)
      = ((K k)ᴴ * K k) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro k
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
  simp_rw [hstep]
  rw [sum_kronecker_left, hK, Matrix.one_kronecker_one]

/-- The **diamond distance** `½‖Φ₁ − Φ₂‖_◇` between two channels (given as Kraus families):
the supremum over input density operators `ρ` on the doubled space of the trace distance of the
stabilized outputs. -/
noncomputable def diamondDist (K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {d | ∃ ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsDensityOperator ρ ∧
    d = traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ)}

variable {K₁ K₂ K₃ : Fin m → Matrix (Fin n) (Fin n) ℂ}

/-- The diamond distance is nonnegative. -/
theorem diamondDist_nonneg : 0 ≤ diamondDist K₁ K₂ := by
  apply Real.sSup_nonneg
  rintro d ⟨ρ, _, rfl⟩
  exact traceDist_nonneg _ _

/-- **`diamondDist ≤ 1`** — the stabilized outputs are density operators, so each trace distance
lies in `[0,1]` (the bound is uniform, hence bounds the supremum). -/
theorem diamondDist_le_one (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    diamondDist K₁ K₂ ≤ 1 := by
  apply Real.sSup_le _ zero_le_one
  rintro d ⟨ρ, hρ, rfl⟩
  exact (traceDist_mem_Icc (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₁) hρ)
    (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₂) hρ)).2

/-- The distinguishability set is bounded above by `1` (each stabilized output is a density
operator). -/
theorem diamondDist_bddAbove (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    BddAbove {d | ∃ ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsDensityOperator ρ ∧
      d = traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ)} := by
  refine ⟨1, ?_⟩
  rintro d ⟨ρ, hρ, rfl⟩
  exact (traceDist_mem_Icc (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₁) hρ)
    (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₂) hρ)).2

/-- **The diamond distance dominates every achievable distinguishability** — for any input
density operator `ρ`, `D((Φ₁⊗id)ρ, (Φ₂⊗id)ρ) ≤ diamondDist Φ₁ Φ₂`. This is the defining
upper-bound property: the sup is a genuine least upper bound over realized distinguishabilities,
not a vacuous constant. -/
theorem le_diamondDist (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hρ : IsDensityOperator ρ) :
    traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ)
      ≤ diamondDist K₁ K₂ :=
  le_csSup (diamondDist_bddAbove hK₁ hK₂) ⟨ρ, hρ, rfl⟩

/-- The diamond distance is symmetric. -/
theorem diamondDist_comm : diamondDist K₁ K₂ = diamondDist K₂ K₁ := by
  unfold diamondDist
  refine congrArg sSup (Set.ext fun d => ⟨?_, ?_⟩) <;>
    rintro ⟨ρ, hρ, hd⟩ <;> exact ⟨ρ, hρ, hd.trans (traceDist_comm _ _)⟩

/-- **`diamondDist Φ Φ = 0`** — a channel is at zero diamond distance from itself. -/
theorem diamondDist_self (K : Fin m → Matrix (Fin n) (Fin n) ℂ) : diamondDist K K = 0 := by
  unfold diamondDist
  apply le_antisymm
  · apply Real.sSup_le _ le_rfl
    rintro d ⟨ρ, _, rfl⟩
    rw [traceDist_self]
  · apply Real.sSup_nonneg
    rintro d ⟨ρ, _, rfl⟩
    rw [traceDist_self]

/-- **The diamond distance satisfies the triangle inequality** — so it is a genuine
`[0,1]`-valued metric on CPTP channels. Pointwise: for every input `ρ`, the trace-distance
triangle gives `D(Φ₁ρ̃,Φ₃ρ̃) ≤ D(Φ₁ρ̃,Φ₂ρ̃) + D(Φ₂ρ̃,Φ₃ρ̃) ≤ diamondDist Φ₁ Φ₂ + diamondDist Φ₂ Φ₃`
(via `le_diamondDist`), and taking the supremum preserves the bound. Notably this needs **no**
sup-attainment — only the pointwise `le_diamondDist` upper bound and `Real.sSup_le`. -/
theorem diamondDist_triangle (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    (hK₃ : IsKrausChannel K₃) :
    diamondDist K₁ K₃ ≤ diamondDist K₁ K₂ + diamondDist K₂ K₃ := by
  apply Real.sSup_le _ (add_nonneg diamondDist_nonneg diamondDist_nonneg)
  rintro d ⟨ρ, hρ, rfl⟩
  have h₁ := (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₁) hρ).1.isHermitian
  have h₂ := (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₂) hρ).1.isHermitian
  have h₃ := (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₃) hρ).1.isHermitian
  calc traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₃) ρ)
      ≤ traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ)
        + traceDist (krausMap (tensorKraus K₂) ρ) (krausMap (tensorKraus K₃) ρ) :=
        traceDist_triangle _ _ _ h₁ h₂ h₃
    _ ≤ diamondDist K₁ K₂ + diamondDist K₂ K₃ :=
        add_le_add (le_diamondDist hK₁ hK₂ hρ) (le_diamondDist hK₂ hK₃ hρ)

/-
## Status — metric, attainment, and the Choi characterization

The diamond distance is a genuine `[0,1]`-valued **metric** on CPTP channels — nonnegative,
symmetric, reflexive (`diamondDist_self`), and satisfying the triangle inequality
(`diamondDist_triangle`), with the least-upper-bound property `le_diamondDist` — all using only
boundedness of the supremum (`Real.sSup`), no attainment.

The two items previously deferred here are now PROVEN (this comment is kept as a pointer):

* **Attainment** — `exists_diamondDist_eq` in `DiamondNormAttainment.lean`: the supremum IS achieved
  by an optimal `ρ`. The earlier "binding gap" (continuity of the singular-value sum in the matrix
  entries, for which Mathlib has no eigenvalue-continuity substrate) was **sidestepped**: the
  objective `ρ ↦ ‖(Φ⊗id)ρ‖₁` is Lipschitz via the Frobenius bound `‖A‖₁ ≤ √card·‖A‖_F` (not
  per-eigenvalue continuity), and EVT closes it on the compact density set.
* **The Choi characterization.** Both one-sided bounds of the Watrous sandwich
  `(1/2n)‖J₁−J₂‖₁ ≤ diamondDist ≤ n‖J₁−J₂‖∞` are proven (`diamondDist_ge_choi_traceNorm`,
  `diamondDist_le_choi_opNorm`, `DiamondNormChoi{,Upper}.lean`), and the Watrous weak-dual witness
  bound `diamondDist_le_dual_witness` (`DiamondNormDual.lean`). The ONLY remaining frontier is the
  primal=dual SDP **equality** (conic strong duality — no Slater/minimax/Fenchel substrate at pin);
  it is the sole documented-deferred item, with no sorry and no axiom.
-/

end SKEFTHawking.QuantumNetwork
