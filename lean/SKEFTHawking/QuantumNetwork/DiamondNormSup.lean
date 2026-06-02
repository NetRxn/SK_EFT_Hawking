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

variable {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}

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

/-
## DEFERRED FRONTIER — attainment and the SDP characterization (6AF-6)

The diamond distance is now DEFINED and shown to be a `[0,1]`-valued, symmetric, reflexive
distinguishability measure, using only boundedness of the supremum (`Real.sSup`). What remains
documented-deferred (no sorry, no axiom):

* **Attainment** — that the supremum is achieved by some optimal `ρ`. The compactness half is
  available (finite-dim ⇒ `ProperSpace`; EVT via `IsCompact.exists_sSup_image_eq`), but the
  binding gap is **continuity of `ρ ↦ ‖(Φ⊗id)ρ‖₁` in the matrix entries** — i.e. continuity of
  the singular-value sum — for which Mathlib at pin has no concrete-matrix substrate (no
  continuity of eigenvalues/singular values as functions of the entries).
* **The triangle inequality** `diamondDist Φ₁ Φ₃ ≤ diamondDist Φ₁ Φ₂ + diamondDist Φ₂ Φ₃`
  (making it a genuine metric on channels) — would follow from the trace-distance triangle plus
  a supremum-subadditivity argument; deferred pending the attainment infrastructure.
* **The Choi-matrix SDP characterization** of the diamond norm (Watrous) — a deep theorem with
  no SDP substrate in Mathlib.
-/

end SKEFTHawking.QuantumNetwork
