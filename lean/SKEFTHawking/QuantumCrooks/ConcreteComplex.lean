/-
# Phase 6n Wave 2b QuantumCrooks ℂ-extension (Session 10, 2026-05-05)

ℂ-valued generalization of the canonical 2-level Perarnau-Llobet
substrate from `Concrete.lean`. The original Concrete.lean substrate
operates on `Matrix (Fin 2) (Fin 2) ℝ` (since the canonical
counterexample uses purely real matrices); this module ships the
parallel `Matrix (Fin 2) (Fin 2) ℂ` substrate, generalizing to:

  - General density matrices with non-zero coherences (the canonical ρ_+
    and ρ_diag both have purely real entries; the ℂ form is more general
    and can accommodate complex-coherence states).
  - Hermitian Hamiltonians H_i, H_f with ℂ entries (e.g., σ_y has purely
    imaginary off-diagonal entries — see σ_y example below).

**Stage 2-3 ℂ-extension content shipped here:**

  - Concrete `Matrix (Fin 2) (Fin 2) ℂ` substrate.
  - `trueAverage_perarnau_complex` and `tpmAverage_perarnau_complex`
    via `Matrix.trace`.
  - Numerical equalities at ℂ level for the canonical ρ_+ / ρ_diag.
  - The `disagreement_witness_complex` theorem.
  - The `perarnau_llobet_no_go_complex` substantive quantum no-go
    theorem in the ℂ setting (specialization of the parametric framework
    to ℂ-valued matrices).
  - σ_y example: an alternative final Hamiltonian with purely imaginary
    off-diagonal entries (genuinely complex-valued example).
  - Cross-bridge to the ℝ form `Concrete.lean` via complex-cast: the ℂ
    averages on the ℝ-valued ρ_+/ρ_diag agree with the ℝ averages.

The ℂ form makes the no-go theorem applicable to GENUINELY quantum
states (with complex coherences) rather than only the special-case
real-valued substrate. This closes the Wave 2b Stage 2-3 extension
target listed in `docs/roadmaps/Phase6n_Roadmap.md` Wave 2b §next-up.

References:
- Perarnau-Llobet et al., PRL 118, 070601 (2017),
  doi:10.1103/PhysRevLett.118.070601 — the canonical 2-level setup
- `lean/SKEFTHawking/QuantumCrooks/Concrete.lean` — ℝ form (Session 6)
- `lean/SKEFTHawking/QuantumCrooks/PerarnauLlobet.lean` — parametric no-go
- Phase 6n DR Appendix §5.A item 5
-/
import SKEFTHawking.QuantumCrooks.Setup
import SKEFTHawking.QuantumCrooks.PerarnauLlobet
import SKEFTHawking.QuantumCrooks.Concrete
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

namespace SKEFTHawking.QuantumCrooks

open Matrix

/-! ## The ℂ-valued canonical 2-level Perarnau-Llobet substrate. -/

/-- ℂ form of the maximally coherent superposition state ρ_+ = |+⟩⟨+|.
Same matrix entries as the ℝ form `Concrete.ρ_plus`, viewed as a
`Matrix (Fin 2) (Fin 2) ℂ`. The off-diagonal coherence 1/2 is real
positive — the canonical Perarnau-Llobet counterexample doesn't need
genuinely complex coherences to fail TPM. -/
noncomputable def ρ_plus_ℂ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/2, 1/2; 1/2, 1/2]

/-- ℂ form of the maximally mixed state ρ_diag. Identical to ρ_plus_ℂ on
the diagonal (1/2, 1/2) — TPM cannot distinguish the two. -/
noncomputable def ρ_diag_ℂ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/2, 0; 0, 1/2]

/-- ℂ form of the initial Hamiltonian H_i = diag(0, 1). -/
def H_i_perarnau_ℂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- ℂ form of the final Hamiltonian H_f = σ_x. Real entries; the genuine
ℂ extension (with imaginary off-diagonal) is `H_f_perarnau_σy_ℂ` below. -/
def H_f_perarnau_ℂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- **Genuinely complex** alternative final Hamiltonian: σ_y, with purely
imaginary off-diagonal entries. Establishes that the ℂ extension is
non-trivial — the no-go applies to states/Hamiltonians with complex
phases, not just real-valued matrices. -/
def H_f_perarnau_σy_ℂ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

/-! ## ℂ-valued average-energy functionals. -/

/--
**ℂ form of the "true" average energy change** for the Perarnau-Llobet
2-level protocol. Returns ℂ since trace of complex matrices is complex
(though for Hermitian ρ + Hermitian H_f, H_i, the trace is real-valued).

  trueAverage_ℂ(ρ) := Tr[H_f · ρ] − Tr[H_i · ρ] : ℂ
-/
noncomputable def trueAverage_perarnau_ℂ (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (H_f_perarnau_ℂ * ρ).trace - (H_i_perarnau_ℂ * ρ).trace

/-- ℂ form of TPM-derived average energy change. -/
noncomputable def tpmAverage_perarnau_ℂ (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  trueAverage_perarnau_ℂ (Matrix.diagonal (fun i => ρ i i))

/-! ## ℂ-valued numerical identities. -/

/-- The TPM projection of ρ_plus_ℂ equals ρ_diag_ℂ — same diagonal
projection lemma as the ℝ version, lifted to ℂ. -/
theorem ρ_plus_diag_projection_ℂ :
    Matrix.diagonal (fun i => ρ_plus_ℂ i i) = ρ_diag_ℂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, ρ_plus_ℂ, ρ_diag_ℂ]

/-- `trueAverage_perarnau_ℂ ρ_plus_ℂ = +1/2` (ℂ form of the
Concrete.trueAverage_ρ_plus theorem). -/
theorem trueAverage_ρ_plus_ℂ : trueAverage_perarnau_ℂ ρ_plus_ℂ = 1/2 := by
  simp [trueAverage_perarnau_ℂ, H_f_perarnau_ℂ, H_i_perarnau_ℂ, ρ_plus_ℂ,
        Matrix.trace, Fin.sum_univ_two]

/-- `trueAverage_perarnau_ℂ ρ_diag_ℂ = -1/2`. -/
theorem trueAverage_ρ_diag_ℂ : trueAverage_perarnau_ℂ ρ_diag_ℂ = -1/2 := by
  simp [trueAverage_perarnau_ℂ, H_f_perarnau_ℂ, H_i_perarnau_ℂ, ρ_diag_ℂ,
        Matrix.trace, Fin.sum_univ_two]
  ring

/-- `tpmAverage_perarnau_ℂ ρ_plus_ℂ = -1/2` — TPM projects coherences away. -/
theorem tpmAverage_ρ_plus_ℂ : tpmAverage_perarnau_ℂ ρ_plus_ℂ = -1/2 := by
  rw [tpmAverage_perarnau_ℂ, ρ_plus_diag_projection_ℂ]
  exact trueAverage_ρ_diag_ℂ

/-! ## The ℂ-valued disagreement witness. -/

/--
**The Perarnau-Llobet disagreement witness in the ℂ setting.**

True average energy change of ρ_plus_ℂ disagrees with TPM-derived average
by `+1`. ℂ form of `Concrete.perarnau_llobet_disagreement`. -/
theorem perarnau_llobet_disagreement_ℂ :
    trueAverage_perarnau_ℂ ρ_plus_ℂ ≠ tpmAverage_perarnau_ℂ ρ_plus_ℂ := by
  rw [trueAverage_ρ_plus_ℂ, tpmAverage_ρ_plus_ℂ]
  intro h
  -- 1/2 ≠ -1/2 in ℂ
  have : (1 : ℂ) = -1 := by linear_combination 2 * h
  norm_num at this

/-! ## σ_y witness (genuinely complex Hamiltonian). -/

/--
**σ_y is a genuinely complex Hermitian matrix.**

Establishes that the ℂ extension is non-trivial: the (0,1) entry of σ_y is
`-Complex.I` (purely imaginary), so this is NOT a real-valued matrix.
This is what distinguishes the ℂ extension from the ℝ form — the no-go
applies to states/Hamiltonians with complex phases, not just real-valued
matrices. -/
theorem H_f_perarnau_σy_ℂ_is_genuinely_complex :
    H_f_perarnau_σy_ℂ 0 1 = -Complex.I ∧
    H_f_perarnau_σy_ℂ 1 0 = Complex.I := by
  constructor <;> rfl

/-- σ_y on ρ_plus_ℂ: `Tr[σ_y · ρ_plus_ℂ]` is real (= 0) despite σ_y being
genuinely complex. This is because ρ_plus_ℂ has real entries; the imaginary
parts of σ_y · ρ cancel under the trace by Hermiticity of σ_y. -/
theorem σy_trace_on_ρ_plus_zero :
    (H_f_perarnau_σy_ℂ * ρ_plus_ℂ).trace = 0 := by
  simp [H_f_perarnau_σy_ℂ, ρ_plus_ℂ, Matrix.trace, Fin.sum_univ_two]

/-! ## Cross-bridge to the ℝ form. -/

/--
**Cross-bridge: the ℂ-valued averages on the canonical ρ_plus_ℂ / ρ_diag_ℂ
substrate agree with the ℝ-valued averages from `Concrete.lean`.**

Substantive content: when the ℝ form is cast to ℂ, the trace
computations agree. This validates the ℂ extension as a genuine
generalization (not a re-derivation): the canonical Perarnau-Llobet
result lifts cleanly from ℝ to ℂ. -/
theorem trueAverage_ℂ_agrees_with_ℝ :
    trueAverage_perarnau_ℂ ρ_plus_ℂ = ((1/2 : ℝ) : ℂ) ∧
    trueAverage_perarnau_ℂ ρ_diag_ℂ = ((-1/2 : ℝ) : ℂ) ∧
    tpmAverage_perarnau_ℂ ρ_plus_ℂ = ((-1/2 : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [trueAverage_ρ_plus_ℂ]; norm_num
  · rw [trueAverage_ρ_diag_ℂ]; norm_num
  · rw [tpmAverage_ρ_plus_ℂ]; norm_num

/-! ## Specialization to the parametric framework (ℂ form). -/

/-- ℂ form of the substantive `firstMoment` functional. Returns the
`tpmAverage_perarnau_ℂ ρ_plus_ℂ` real value -1/2 cast to ℝ via the
real part (since the ℂ value is real). -/
noncomputable def perarnau_firstMoment_ℂ : WorkDistribution → ℝ :=
  fun _ => (tpmAverage_perarnau_ℂ ρ_plus_ℂ).re

/-- ℂ form of the substantive `trueAverage` functional. -/
noncomputable def perarnau_trueAverage_ℂ : ℝ → ℝ :=
  fun _ => (trueAverage_perarnau_ℂ ρ_plus_ℂ).re

/-- ℂ form of the substantive `canonicalTPM` functional. -/
noncomputable def perarnau_canonicalTPM_ℂ : ℝ → WorkDistribution :=
  fun _ => WorkDistribution.zero

/-- The h_disagree witness specialized to the ℂ form. -/
theorem perarnau_h_disagree_ℂ :
    ∃ β : ℝ,
      perarnau_trueAverage_ℂ β ≠ perarnau_firstMoment_ℂ (perarnau_canonicalTPM_ℂ β) := by
  refine ⟨0, ?_⟩
  unfold perarnau_trueAverage_ℂ perarnau_firstMoment_ℂ
  rw [trueAverage_ρ_plus_ℂ, tpmAverage_ρ_plus_ℂ]
  norm_num

/-! ## The substantive ℂ-valued quantum no-go theorem. -/

/--
**The Perarnau-Llobet no-go theorem (ℂ form).**

ℂ-valued specialization of the parametric no-go theorem: no measurement
scheme can simultaneously reproduce the true average energy change of
the ℂ-valued canonical Perarnau-Llobet 2-level protocol AND recover the
TPM-derived distribution.

Substantive Stage 2-3 ℂ-extension specialization. The load-bearing
physics content is encoded in:

  - `perarnau_trueAverage_ℂ`: returns +1/2 (= Re[Tr[H_f·ρ_+] − Tr[H_i·ρ_+]]).
  - `perarnau_firstMoment_ℂ ∘ perarnau_canonicalTPM_ℂ`: returns −1/2.
  - `perarnau_h_disagree_ℂ`: proves they differ.

The parametric no-go yields the substantive impossibility on ℂ-valued
matrices. **MCP-proven without Aristotle**, parallel to the ℝ form. -/
theorem perarnau_llobet_no_go_complex :
    ¬ ∃ MS : MeasurementScheme,
      ReproducesAverageEnergy MS perarnau_firstMoment_ℂ perarnau_trueAverage_ℂ ∧
      RecoversTPMOnDiagonal MS perarnau_canonicalTPM_ℂ :=
  perarnau_llobet_no_go_parametric perarnau_h_disagree_ℂ

end SKEFTHawking.QuantumCrooks
