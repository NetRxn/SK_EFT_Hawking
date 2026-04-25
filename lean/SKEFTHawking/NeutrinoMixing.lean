import SKEFTHawking.Basic
import SKEFTHawking.MajoranaRung
import Mathlib

/-!
# Phase 5z Wave 2: PMNS Mixing — Structure Note

## Overview

A *structure note* (parallel to HepLean's `CKMMatrix` idiom) for the
Pontecorvo-Maki-Nakagawa-Sakata (PMNS) mixing matrix that connects flavor
eigenstates of charged leptons to mass eigenstates of light neutrinos.
Phenomenology (specific angles, fitting, full setoid quotient with Majorana
phases) is intentionally OUT of scope per the Phase 5z roadmap; the goal
here is the formal structure type and the bridge to `MajoranaRung.lean`.

The PMNS structure is *embedding-agnostic* — the same Lean signature
applies to Embedding I, II, or III. The choice of embedding lives in
`MajoranaRung.lean` (the `H_MR_FromADWSubstrate` tracked hypothesis); only
its phenomenological *interpretation* of `[U_PMNS]_αi` differs.

Numerical NuFit-6.0 best-fit values (`MAJORANA.THETA_*_DEG`,
`MAJORANA.DELTA_CP_DEG`) live in `src/core/constants.py` and the
provenance registry; this Lean module records the algebraic
structure only.

## Open hypotheses (tracked, not derived)

- **WAVE2-OPEN-2**: PMNS angles (especially `θ₂₃ ≈ π/4`) from a putative
  substrate μ-τ exchange symmetry. No primary source closes the derivation.
  Encoded as the `H_PMNSAnglesFromSubstrate` tracked hypothesis.

## References

- HepLean CKMMatrix module (Tooby-Smith, arXiv:2405.08863): the canonical
  structure-note pattern this module mirrors.
- `Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-Neutrino Embedding for
  the Majorana Rung.md` Block §3, §5.3.
- `src/core/formulas.py` `pmns_unitary_matrix` (PDG standard parameterization).
-/

noncomputable section

namespace SKEFTHawking.NeutrinoMixing

/-! ## 1. PMNS structure -/

/-- A PMNS matrix is a 3×3 complex unitary matrix encoding the rotation
between flavor and mass eigenstates of light neutrinos. Mirrors the HepLean
`CKMMatrix` idiom (Tooby-Smith, arXiv:2405.08863, §3).

The Majorana-vs-Dirac distinction is **not** encoded in the structure (a
Majorana neutrino's PMNS matrix is also a 3×3 unitary; the difference is
that two of the diagonal phases are physical for Majorana, unphysical for
Dirac). That distinction is exposed via separate `Prop`-level predicates
(`IsDiracPMNS` / `IsMajoranaPMNS`) below. -/
structure PMNSMatrix where
  /-- The underlying 3×3 complex unitary matrix. -/
  toMatrix : Matrix (Fin 3) (Fin 3) ℂ
  /-- Membership in Mathlib's unitary submonoid. -/
  isUnitary : toMatrix ∈ Matrix.unitaryGroup (Fin 3) ℂ

/-- Element accessor mirroring HepLean's `[V]αβ`. -/
def get (V : PMNSMatrix) (α β : Fin 3) : ℂ := V.toMatrix α β

/-- Unitarity unfolds to `Uᴴ · U = 1`. Direct rewrite of the unitary-group
membership characterization, packaged for downstream consumers. -/
theorem star_mul_self_eq_one (V : PMNSMatrix) :
    star V.toMatrix * V.toMatrix = 1 := by
  rcases (Matrix.mem_unitaryGroup_iff'.mp V.isUnitary) with h
  exact h

/-- Companion identity: `U · Uᴴ = 1`. -/
theorem mul_star_self_eq_one (V : PMNSMatrix) :
    V.toMatrix * star V.toMatrix = 1 := by
  rcases (Matrix.mem_unitaryGroup_iff.mp V.isUnitary) with h
  exact h

/-! ## 2. Non-emptiness witness — the identity matrix is a PMNS -/

/-- The 3×3 identity matrix is unitary; encoded as a `PMNSMatrix`. Exists
purely as a non-emptiness witness for the structure (the `Inhabited`
instance below derives from this). The "no mixing" PMNS — physical PMNS
matrices have non-trivial off-diagonals consistent with NuFit-6.0. -/
def PMNSMatrix.identity : PMNSMatrix where
  toMatrix := 1
  isUnitary := Submonoid.one_mem _

instance : Inhabited PMNSMatrix := ⟨PMNSMatrix.identity⟩

/-- The identity PMNS has identity entries: the diagonal is 1, off-diagonal
is 0. Marker theorem confirming the structure isn't vacuous. -/
@[simp] theorem identity_diagonal (α : Fin 3) :
    get PMNSMatrix.identity α α = 1 := by
  unfold get PMNSMatrix.identity
  simp

/-- Identity PMNS off-diagonal entries vanish. -/
theorem identity_offdiagonal {α β : Fin 3} (h : α ≠ β) :
    get PMNSMatrix.identity α β = 0 := by
  unfold get PMNSMatrix.identity
  simp [Matrix.one_apply_ne h]

/-! ## 3. Dirac vs Majorana PMNS (parametric distinction)

In the Dirac case, two extra diagonal phases on the right (acting on the
mass-eigenstate side) are unphysical (rephased away). In the Majorana case,
those phases are physical observables (`α₁`, `α₂` Majorana phases).

The structural `PMNSMatrix` is the same for both; the predicates below
mark the *physical role* of the right-hand diagonal phases. -/

/-- A PMNS matrix is *Dirac-realized* when there are no Majorana phases —
equivalently, the two right-hand mass-eigenstate phases are gauged away.
Operationally, Dirac realization is detected by the absence of physically-
meaningful Majorana phases; we expose it via a `Prop`-level marker. The
content of the predicate is *external* to the matrix structure: same
3×3 unitary, different physical interpretation. -/
def IsDiracPMNS (_V : PMNSMatrix) : Prop := True

/-- A PMNS matrix is *Majorana-realized* when both right-hand diagonal
phases are physical (corresponding to a Majorana mass term in
`MajoranaRung.lean`). Like `IsDiracPMNS`, the content is parametric — same
matrix, different physical interpretation. -/
def IsMajoranaPMNS (_V : PMNSMatrix) : Prop := True

/-- Bridge to `MajoranaRung.lean`: under Embedding III's positive heavy
Majorana mass `M_R i > 0`, a corresponding PMNS matrix is realized in the
Majorana sense. Trivially true at the structural level (both predicates
are markers); the predicate links the two modules formally and lets
downstream consumers state "Wave 2 chooses the Majorana realization". -/
theorem isMajoranaPMNS_of_majoranaRungData
    (m : SKEFTHawking.MajoranaRung.MajoranaRungData)
    (V : PMNSMatrix) (_h_pos : ∀ i, 0 < m.M_R i) :
    IsMajoranaPMNS V := trivial

/-! ## 4. WAVE2-OPEN-2: PMNS-from-substrate-overlaps tracked hypothesis

The deep research is explicit (Block §3.2): no primary source derives PMNS
mixing angles from an underlying substrate model. Closest is the texture-
level statement `θ₂₃ ≈ π/4 from substrate μ-τ symmetry`, which is motivated
by — but not derived from — composite-operator dynamics.

Encoded as a tracked hypothesis predicate parameterized over a substrate
scale; non-trivial, can fail for matrices with `[U]_μ3 ≠ [U]_τ3` (the
empirical near-maximal θ₂₃ has `≈ 49.1°`, very close to but not exactly
`π/4`).
-/

/-- **WAVE2-OPEN-2**: tracked hypothesis that the PMNS μ-τ exchange row is
substrate-symmetric (`‖[U]_μi‖ = ‖[U]_τi‖` for every mass eigenstate `i`).
Genuinely non-trivial: the empirical NuFit-6.0 best-fit `θ₂₃ ≈ 49.1°` is
close to but not exactly `π/4`, so a PMNS matrix with strictly maximal
`θ₂₃ = π/4` would satisfy the symmetry while the actual data has small
deviations. -/
def H_PMNSAnglesFromSubstrate (V : PMNSMatrix) : Prop :=
  ∀ i : Fin 3, ‖get V 1 i‖ = ‖get V 2 i‖

/-- Identity PMNS does NOT satisfy the substrate-overlap hypothesis. For
`i = 1`, the identity has `[I]_μμ = 1` and `[I]_τμ = 0`, so the predicate
forces `1 = 0` — false. Confirms `H_PMNSAnglesFromSubstrate` is non-vacuous
by exhibiting an explicit witness of failure. -/
theorem identity_does_not_satisfy_substrate_hypothesis :
    ¬ H_PMNSAnglesFromSubstrate PMNSMatrix.identity := by
  intro h
  have h1 : ‖get PMNSMatrix.identity 1 1‖ = ‖get PMNSMatrix.identity 2 1‖ := h 1
  -- |[I]_μμ| = 1 (diagonal), |[I]_τμ| = 0 (off-diagonal)
  have h_diag : get PMNSMatrix.identity 1 1 = 1 := identity_diagonal 1
  have h_off : get PMNSMatrix.identity 2 1 = 0 :=
    identity_offdiagonal (by decide : (2 : Fin 3) ≠ 1)
  rw [h_diag, h_off] at h1
  simp at h1

/-! ## 5. Module summary -/

/-- Wave-2 PMNS structure-note marker: the Lean infrastructure for the
PMNS mixing matrix is in place; full phenomenology + Setoid quotient under
charged-lepton phase rephasings is deferred to a follow-up wave. -/
theorem neutrino_mixing_structure_note_summary : True := trivial

end SKEFTHawking.NeutrinoMixing
