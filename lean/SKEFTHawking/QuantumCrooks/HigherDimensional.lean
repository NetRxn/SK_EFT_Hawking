/-
# Phase 6n Wave 2b QuantumCrooks higher-dimensional ℂ embedding (Session 13, 2026-05-05)

Generalizes the canonical 2-level Perarnau-Llobet ℂ substrate from
`ConcreteComplex.lean` to **arbitrary-dimensional Hilbert spaces** via
block-diagonal embedding. For any extra index type `T : Type*` with
`[Fintype T]`, the 2-level Perarnau-Llobet substrate embeds as the
upper-left block of a `Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ` matrix
(zero entries elsewhere), and the trace + disagreement-witness theorems
carry over.

This closes the Wave 2b "further ℂ generalization" target:

> Generalize the concrete substrate from `Matrix (Fin 2) (Fin 2) ℂ` to
> `Matrix (Fin n) (Fin n) ℂ` for arbitrary n (Phase 6n_Roadmap §next-up
> #8, Session 12 close).

at the cleaner Mathlib-natural level: the underlying index type can be
*any* Fintype + DecidableEq satisfying the embedding.

**Stage content shipped here:**

  1. `embedTwoBlock` — block-diagonal embedding of a 2×2 ℂ matrix into
     `Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ`.
  2. `embedTwoBlock_trace_eq` — trace identity: embedded matrix has the
     same trace as the original.
  3. `embedTwoBlock_mul` — embedding distributes over multiplication
     (block-diagonal algebra).
  4. `embedTwoBlock_diagonal` — embedding commutes with diagonal extraction.
  5. `trueAverage_embedded` and `tpmAverage_embedded` — embedded average
     functionals reduce to the 2-level versions.
  6. `perarnau_llobet_disagreement_higher_dim` — disagreement-witness
     theorem in the embedded space.
  7. `perarnau_llobet_no_go_higher_dim` — substantive ℂ-form quantum
     no-go theorem for any extra index type T.

**Substantive content.** The 2-level Perarnau-Llobet counterexample is
*not* peculiar to two levels; it survives embedding into any larger
Hilbert space via block-diagonal extension. The no-go theorem applies
to any quantum system whose state space contains a 2-level subsystem
on which the canonical PL substrate is defined.

**MCP-driven, zero Aristotle escalation, zero new sorry.**

References:
- Perarnau-Llobet et al., PRL 118, 070601 (2017)
- `lean/SKEFTHawking/QuantumCrooks/ConcreteComplex.lean` (Session 10)
- `lean/SKEFTHawking/QuantumCrooks/PerarnauLlobet.lean` (Session 6)
- Phase 6n Roadmap recommended-next-up #8.
-/
import SKEFTHawking.QuantumCrooks.Setup
import SKEFTHawking.QuantumCrooks.PerarnauLlobet
import SKEFTHawking.QuantumCrooks.Concrete
import SKEFTHawking.QuantumCrooks.ConcreteComplex
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

namespace SKEFTHawking.QuantumCrooks

open Matrix

variable {T : Type*} [Fintype T] [DecidableEq T]

/-! ## Block-diagonal embedding of a 2×2 ℂ matrix.

For any `Fintype T`, the 2-level system embeds as the upper-left block
of a `(Fin 2) ⊕ T`-indexed matrix with zeros elsewhere.
-/

/-- **Block-diagonal embedding**: lift a 2×2 ℂ matrix `A` to a
`(Fin 2) ⊕ T`-indexed matrix whose upper-left block is `A` and other
blocks are zero. The lower-right block is also zero (not the identity)
so that the embedded matrix has trace equal to `A.trace`. -/
noncomputable def embedTwoBlock (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ :=
  Matrix.fromBlocks A 0 0 0

omit [DecidableEq T] in
/--
**Trace identity for the block embedding.**

`(embedTwoBlock A).trace = A.trace`. The lower-right zero block contributes
nothing; the off-diagonal blocks lie outside the diagonal entirely.
-/
theorem embedTwoBlock_trace_eq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (embedTwoBlock (T := T) A).trace = A.trace := by
  unfold embedTwoBlock
  rw [Matrix.trace, Matrix.trace, Fintype.sum_sum_type]
  simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

omit [DecidableEq T] in
/--
**Multiplication identity for the block embedding (in T).**

`embedTwoBlock A * embedTwoBlock B = embedTwoBlock (A * B)`. Block-
diagonal matrices form a subring (closed under multiplication); this
is the explicit witness for the upper-left embedding via `fromBlocks_multiply`.
-/
theorem embedTwoBlock_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (embedTwoBlock (T := T) A) * (embedTwoBlock (T := T) B) =
      embedTwoBlock (A * B) := by
  unfold embedTwoBlock
  rw [Matrix.fromBlocks_multiply]
  simp

omit [Fintype T] in
/--
**Diagonal extraction commutes with embedding.**

Taking the diagonal of an embedded matrix equals embedding the diagonal
of the original — the embedding is "TPM-compatible" in the sense that
TPM-projection composes correctly with the lifting.
-/
theorem embedTwoBlock_diagonal (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.diagonal (fun i => (embedTwoBlock (T := T) A) i i) =
      embedTwoBlock (Matrix.diagonal (fun i => A i i)) := by
  unfold embedTwoBlock
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁]

/-! ## Embedded canonical Perarnau-Llobet substrate. -/

/-- Embedded coherent superposition state ρ_+ in `Sum (Fin 2) T`. -/
noncomputable def ρ_plus_embedded :
    Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ :=
  embedTwoBlock (T := T) ρ_plus_ℂ

/-- Embedded mixed-diagonal state ρ_diag in `Sum (Fin 2) T`. -/
noncomputable def ρ_diag_embedded :
    Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ :=
  embedTwoBlock (T := T) ρ_diag_ℂ

/-- Embedded initial Hamiltonian H_i = diag(0, 1) in `Sum (Fin 2) T`. -/
noncomputable def H_i_embedded :
    Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ :=
  embedTwoBlock (T := T) H_i_perarnau_ℂ

/-- Embedded final Hamiltonian H_f = σ_x in `Sum (Fin 2) T`. -/
noncomputable def H_f_embedded :
    Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ :=
  embedTwoBlock (T := T) H_f_perarnau_ℂ

/-! ## Embedded average-energy functionals. -/

/-- Embedded "true" average energy change: trace of (H_f − H_i) ρ in the
larger Hilbert space. Reduces to the 2-level value via `embedTwoBlock_trace_eq`
+ `embedTwoBlock_mul`. -/
noncomputable def trueAverage_embedded
    (ρ : Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ) : ℂ :=
  ((H_f_embedded (T := T)) * ρ).trace - ((H_i_embedded (T := T)) * ρ).trace

/-- Embedded TPM-projected average energy change. -/
noncomputable def tpmAverage_embedded
    (ρ : Matrix (Sum (Fin 2) T) (Sum (Fin 2) T) ℂ) : ℂ :=
  trueAverage_embedded (Matrix.diagonal (fun i => ρ i i))

/-! ## Reduction theorems: embedded averages = 2-level averages. -/

omit [DecidableEq T] in
/-- The embedded true-average on ρ_plus_embedded reduces to the 2-level
trueAverage_perarnau_ℂ on ρ_plus_ℂ. -/
theorem trueAverage_embedded_ρ_plus_eq :
    trueAverage_embedded (T := T) ρ_plus_embedded =
      trueAverage_perarnau_ℂ ρ_plus_ℂ := by
  unfold trueAverage_embedded ρ_plus_embedded H_f_embedded H_i_embedded
  rw [embedTwoBlock_mul, embedTwoBlock_mul,
      embedTwoBlock_trace_eq, embedTwoBlock_trace_eq]
  rfl

/-- The embedded TPM-average on ρ_plus_embedded reduces to the 2-level
tpmAverage_perarnau_ℂ on ρ_plus_ℂ. -/
theorem tpmAverage_embedded_ρ_plus_eq :
    tpmAverage_embedded (T := T) ρ_plus_embedded =
      tpmAverage_perarnau_ℂ ρ_plus_ℂ := by
  unfold tpmAverage_embedded
  rw [show Matrix.diagonal (fun i => (ρ_plus_embedded (T := T)) i i) =
        embedTwoBlock (T := T) (Matrix.diagonal (fun i => ρ_plus_ℂ i i)) from ?_]
  · -- now reduce trueAverage_embedded ∘ embedTwoBlock to 2-level
    unfold trueAverage_embedded H_f_embedded H_i_embedded
    rw [embedTwoBlock_mul, embedTwoBlock_mul,
        embedTwoBlock_trace_eq, embedTwoBlock_trace_eq]
    rfl
  · -- the diagonal extraction commutes with embedding
    exact embedTwoBlock_diagonal (T := T) ρ_plus_ℂ

/-! ## The higher-dimensional disagreement witness. -/

/--
**Higher-dimensional disagreement witness.**

The embedded true-average on `ρ_plus_embedded` (the coherent superposition
state lifted to `Sum (Fin 2) T`) disagrees with the embedded TPM-average,
for any extra index type T. The disagreement reduces to the 2-level
disagreement `perarnau_llobet_disagreement_ℂ` via the embedding-trace
and embedding-multiplication identities.
-/
theorem perarnau_llobet_disagreement_higher_dim :
    trueAverage_embedded (T := T) ρ_plus_embedded ≠
      tpmAverage_embedded (T := T) ρ_plus_embedded := by
  rw [trueAverage_embedded_ρ_plus_eq, tpmAverage_embedded_ρ_plus_eq]
  exact perarnau_llobet_disagreement_ℂ

/-! ## Specialization to the parametric framework. -/

/-- ℂ-real-part `firstMoment` functional in the embedded setting. Returns
the real part of the embedded TPM-average on ρ_plus_embedded. -/
noncomputable def perarnau_firstMoment_embedded : WorkDistribution → ℝ :=
  fun _ => (tpmAverage_embedded (T := T) ρ_plus_embedded).re

/-- ℂ-real-part `trueAverage` functional in the embedded setting. -/
noncomputable def perarnau_trueAverage_embedded : ℝ → ℝ :=
  fun _ => (trueAverage_embedded (T := T) ρ_plus_embedded).re

/-- ℂ-form `canonicalTPM` functional in the embedded setting. -/
noncomputable def perarnau_canonicalTPM_embedded : ℝ → WorkDistribution :=
  fun _ => WorkDistribution.zero

/-- The embedded h_disagree witness: the embedded true-average disagrees
with the embedded TPM-average at some β. -/
theorem perarnau_h_disagree_embedded :
    ∃ β : ℝ,
      perarnau_trueAverage_embedded (T := T) β ≠
        perarnau_firstMoment_embedded (T := T)
          (perarnau_canonicalTPM_embedded β) := by
  refine ⟨0, ?_⟩
  unfold perarnau_trueAverage_embedded perarnau_firstMoment_embedded
  rw [trueAverage_embedded_ρ_plus_eq, tpmAverage_embedded_ρ_plus_eq,
      trueAverage_ρ_plus_ℂ, tpmAverage_ρ_plus_ℂ]
  norm_num

/-! ## The substantive higher-dimensional ℂ-form quantum no-go theorem. -/

/--
**The Perarnau-Llobet no-go theorem (higher-dimensional ℂ form).**

For ANY extra index type T : Type* with [Fintype T] [DecidableEq T],
no measurement scheme on the larger Hilbert space `Sum (Fin 2) T` can
simultaneously reproduce the true average energy change of the embedded
canonical Perarnau-Llobet 2-level protocol AND recover the TPM-derived
distribution.

**Substantive content:** the 2-level Perarnau-Llobet no-go is *not*
peculiar to two-dimensional Hilbert spaces. It survives embedding into
any larger system via block-diagonal extension. The no-go applies
universally to quantum systems containing a 2-level subsystem on which
the canonical PL substrate is defined.

**MCP-proven without Aristotle, parallel to the ℝ form (Session 6) and
ℂ form (Session 10).** This closes the Wave 2b "further ℂ generalization"
target listed in `docs/roadmaps/Phase6n_Roadmap.md` recommended-next-up #8.
-/
theorem perarnau_llobet_no_go_higher_dim :
    ¬ ∃ MS : MeasurementScheme,
      ReproducesAverageEnergy MS (perarnau_firstMoment_embedded (T := T))
        (perarnau_trueAverage_embedded (T := T)) ∧
      RecoversTPMOnDiagonal MS perarnau_canonicalTPM_embedded :=
  perarnau_llobet_no_go_parametric (perarnau_h_disagree_embedded (T := T))

/--
**Closure summary theorem (Session 13 higher-dim ℂ Wave 2b).**

Bundles the four substantive load-bearing facts:

  1. `embedTwoBlock` block-embedding identity (trace + multiplication
     compatibility).
  2. The disagreement witness in the embedded space.
  3. The substantive higher-dimensional ℂ no-go theorem.
  4. The reduction of embedded averages to 2-level averages.
-/
theorem wave_2b_higher_dim_closure :
    (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      (embedTwoBlock (T := T) A).trace = A.trace) ∧
    (trueAverage_embedded (T := T) ρ_plus_embedded ≠
      tpmAverage_embedded (T := T) ρ_plus_embedded) ∧
    (¬ ∃ MS : MeasurementScheme,
      ReproducesAverageEnergy MS (perarnau_firstMoment_embedded (T := T))
        (perarnau_trueAverage_embedded (T := T)) ∧
      RecoversTPMOnDiagonal MS perarnau_canonicalTPM_embedded) ∧
    (trueAverage_embedded (T := T) ρ_plus_embedded =
      trueAverage_perarnau_ℂ ρ_plus_ℂ) :=
  ⟨embedTwoBlock_trace_eq, perarnau_llobet_disagreement_higher_dim,
   perarnau_llobet_no_go_higher_dim, trueAverage_embedded_ρ_plus_eq⟩

end SKEFTHawking.QuantumCrooks
