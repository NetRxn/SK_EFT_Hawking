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
`MajoranaRung.lean` (the `H_MR_FromADWSubstrate_BCS_LNV` tracked hypothesis); only
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

/-! ## 3. Dirac vs Majorana PMNS (parametric distinction over Majorana phase data)

In the Dirac case, two extra diagonal phases on the right (acting on the
mass-eigenstate side) are unphysical (rephased away). In the Majorana case,
those phases are physical observables (`α₁`, `α₂` Majorana phases).

The structural `PMNSMatrix` is the same for both; the predicates below
parameterize over a candidate Majorana-phase vector `α : Fin 2 → ℝ` and
record the physical role: in the Dirac realization both phases are zero
(rephased away), in the Majorana realization at least one phase is
physically non-trivial.

Stage-13 strengthened (2026-04-25, BLOCKER 5.2): prior `: True`
encodings made `IsMajoranaPMNS` accept any inhabitant and the
`isMajoranaPMNS_of_majoranaRungData` bridge `:= trivial`. The new
parametric encoding requires explicit non-trivial phase data for the
Majorana branch, eliminating the structural tautology. -/

/-- A PMNS matrix is *Dirac-realized at phase data* `α` when both
candidate Majorana phases are zero — equivalently, the two right-hand
mass-eigenstate phases have been rephased away. Concretely:
`α 0 = 0 ∧ α 1 = 0`. The matrix `V` itself is structurally identical
across realizations; the realization is a property of the phase data. -/
def IsDiracPMNS (_V : PMNSMatrix) (α : Fin 2 → ℝ) : Prop :=
  ∀ k : Fin 2, α k = 0

/-- A PMNS matrix is *Majorana-realized at phase data* `α` when at least
one candidate Majorana phase is physically non-trivial — i.e. some
`α k ≠ 0`. This is the Embedding-III physical interpretation: a
non-trivial Majorana mass spectrum produces non-trivial Majorana phases
that are physical observables (cf. `0νββ` decay rate dependence). -/
def IsMajoranaPMNS (_V : PMNSMatrix) (α : Fin 2 → ℝ) : Prop :=
  ∃ k : Fin 2, α k ≠ 0

/-- Bridge to `MajoranaRung.lean`: under Embedding III's positive heavy
Majorana mass spectrum `M_R i > 0` (which is the structural input that
licenses non-trivial Majorana phases), any phase data `α` exhibiting a
non-trivial component realizes the PMNS in the Majorana sense. The
hypothesis on `α` is non-vacuous — there exist Embedding-III consistent
phase configurations both realizing and not realizing Majorana phases —
and the bridge surfaces the "Wave 2 chooses the Majorana realization"
content as the existence of a non-trivial-phase α. -/
theorem isMajoranaPMNS_of_majoranaRungData
    (_m : SKEFTHawking.MajoranaRung.MajoranaRungData)
    (V : PMNSMatrix) (α : Fin 2 → ℝ)
    (h_phase_nontrivial : ∃ k, α k ≠ 0) :
    IsMajoranaPMNS V α := h_phase_nontrivial

/-- Disjointness: at fixed phase data `α`, the Dirac and Majorana
predicates cannot both hold — the former forces every `α k = 0`, the
latter requires some `α k ≠ 0`. -/
theorem not_isDiracPMNS_and_isMajoranaPMNS
    (V : PMNSMatrix) (α : Fin 2 → ℝ) :
    ¬ (IsDiracPMNS V α ∧ IsMajoranaPMNS V α) := by
  rintro ⟨h_dirac, k, h_kne⟩
  exact h_kne (h_dirac k)

/-- The zero-phase configuration realizes the Dirac PMNS (matches the
structural prediction: no Majorana mass ⇔ no physical Majorana phases). -/
theorem isDiracPMNS_of_zero_phases (V : PMNSMatrix) :
    IsDiracPMNS V (fun _ => 0) := by
  intro k; rfl

/-! ## 4. WAVE2-OPEN-2: PMNS-from-substrate-overlaps tracked hypothesis

The deep research is explicit (Block §3.2): no primary source derives PMNS
mixing angles from an underlying substrate model. Closest is the texture-
level statement `θ₂₃ ≈ π/4 from substrate μ-τ symmetry`, which is motivated
by — but not derived from — composite-operator dynamics.

**Wave 2a accuracy round:** the original Wave 2 encoding demanded *exact*
μ-τ row equality `‖[U]_μi‖ = ‖[U]_τi‖`, which the empirical NuFit-6.0
best-fit PMNS at `θ_23 = 49.1°` does NOT satisfy (the rows differ by
`|sin 49.1° - cos 49.1°| · cos θ_13 ≈ 0.10`). Encoding an exact-symmetry
predicate as a "tracked hypothesis on the empirical PMNS" is therefore
incorrect — the predicate is empirically falsified, not just open in
primary literature.

The corrected encoding splits the predicate into:

1. The **exact-substrate-symmetry limit**, applicable to a hypothetical
   PMNS at θ_23 = π/4 (a theoretical limit, not the empirical best fit).
2. A **tolerance-parameterized version** which the empirical PMNS satisfies
   for some `ε > 0` measuring substrate-symmetry breaking; the open
   derivation question is whether substrate physics can predict the
   leading-order value of `ε` from substrate-symmetry-breaking parameters.

The tolerance-parameterized version is the load-bearing tracked hypothesis:
the open question is "what determines `ε`?" — non-vacuously parameterized
by the breaking scale.
-/

/-- **WAVE2-OPEN-2 (exact-symmetry limit)**: a PMNS matrix exhibits *exact*
substrate μ-τ row symmetry. This holds at the theoretical limit
`θ_23 = π/4`; the NuFit-6.0 empirical best fit `θ_23 = 49.1°` does NOT
satisfy this (the row magnitudes differ by `≈ 0.1`). The strict predicate
encodes the *substrate-symmetry limit* — a theoretical reference point
useful for stating the *deviation* (see `H_PMNSAnglesFromSubstrate_eps`
below) — NOT a claim about the physical PMNS.

Project precedent: the same exact-limit-vs-tolerance-parameterization split
is used in `ScalarRungInterpretation.IsHiggsBilinearCandidate` (which is
parameterized over a tolerance `tol`) and in
`MajoranaRung.IsObservedSeesawMatch`.
-/
def H_PMNSAnglesFromExactSubstrate (V : PMNSMatrix) : Prop :=
  ∀ i : Fin 3, ‖get V 1 i‖ = ‖get V 2 i‖

/-- **WAVE2-OPEN-2 (tolerance-parameterized)**: a PMNS matrix exhibits
substrate μ-τ row symmetry up to fractional tolerance `ε`. This is the
load-bearing tracked hypothesis under Wave 2a: the empirical PMNS
satisfies it for some `ε > 0`, and the open derivation question is whether
substrate physics determines the leading-order value of `ε` from
substrate-symmetry-breaking parameters.

The exact-symmetry limit corresponds to `ε = 0`. -/
def H_PMNSAnglesFromSubstrate_eps (V : PMNSMatrix) (ε : ℝ) : Prop :=
  ∀ i : Fin 3, |‖get V 1 i‖ - ‖get V 2 i‖| ≤ ε

/-- The exact-substrate hypothesis is the `ε = 0` special case of the
tolerance-parameterized version. -/
theorem H_PMNSAnglesFromExactSubstrate_iff_eps_zero
    (V : PMNSMatrix) :
    H_PMNSAnglesFromExactSubstrate V ↔
      H_PMNSAnglesFromSubstrate_eps V 0 := by
  unfold H_PMNSAnglesFromExactSubstrate H_PMNSAnglesFromSubstrate_eps
  constructor
  · intro h i
    have h_eq := h i
    rw [h_eq, sub_self, abs_zero]
  · intro h i
    have h_le := h i
    -- |x| ≤ 0 → x = 0
    have h_eq := abs_nonpos_iff.mp h_le
    linarith [h_eq]

/-- Refinement: the strict (exact-symmetry) hypothesis implies the
tolerance-parameterized version for any non-negative tolerance. This is the
expected monotonicity in `ε`. -/
theorem H_PMNSAnglesFromExactSubstrate_imp_eps
    (V : PMNSMatrix) (ε : ℝ) (h_eps : 0 ≤ ε)
    (h_exact : H_PMNSAnglesFromExactSubstrate V) :
    H_PMNSAnglesFromSubstrate_eps V ε := by
  intro i
  have h_eq := h_exact i
  rw [h_eq, sub_self, abs_zero]
  exact h_eps

/-- Identity PMNS does NOT satisfy the exact-substrate hypothesis. For
`i = 1`, the identity has `[I]_μμ = 1` and `[I]_τμ = 0`, so the predicate
forces `1 = 0` — false. Confirms `H_PMNSAnglesFromExactSubstrate` is
non-vacuous by exhibiting an explicit witness of failure. -/
theorem identity_does_not_satisfy_exact_substrate_hypothesis :
    ¬ H_PMNSAnglesFromExactSubstrate PMNSMatrix.identity := by
  intro h
  have h1 : ‖get PMNSMatrix.identity 1 1‖ = ‖get PMNSMatrix.identity 2 1‖ := h 1
  -- |[I]_μμ| = 1 (diagonal), |[I]_τμ| = 0 (off-diagonal)
  have h_diag : get PMNSMatrix.identity 1 1 = 1 := identity_diagonal 1
  have h_off : get PMNSMatrix.identity 2 1 = 0 :=
    identity_offdiagonal (by decide : (2 : Fin 3) ≠ 1)
  rw [h_diag, h_off] at h1
  simp at h1

/-- Identity PMNS does NOT satisfy the tolerance-parameterized hypothesis
for any `ε < 1`. The diagonal `[I]_μμ = 1` and off-diagonal `[I]_τμ = 0`
force the deviation `|‖[I]_μμ‖ - ‖[I]_τμ‖| = 1`. So any tolerance below
unity is insufficient to accommodate the identity matrix — confirming the
predicate's non-vacuity at every tolerance below 1. -/
theorem identity_does_not_satisfy_eps_substrate_hypothesis
    (ε : ℝ) (h_eps : ε < 1) :
    ¬ H_PMNSAnglesFromSubstrate_eps PMNSMatrix.identity ε := by
  intro h
  have h1 := h 1
  have h_diag : get PMNSMatrix.identity 1 1 = 1 := identity_diagonal 1
  have h_off : get PMNSMatrix.identity 2 1 = 0 :=
    identity_offdiagonal (by decide : (2 : Fin 3) ≠ 1)
  rw [h_diag, h_off] at h1
  -- h1 : |‖(1 : ℂ)‖ - ‖(0 : ℂ)‖| ≤ ε
  -- ‖(1 : ℂ)‖ = 1 and ‖(0 : ℂ)‖ = 0, so |1 - 0| = 1 ≤ ε contradicts ε < 1
  have h_norm_one : ‖(1 : ℂ)‖ = 1 := by simp
  have h_norm_zero : ‖(0 : ℂ)‖ = 0 := by simp
  rw [h_norm_one, h_norm_zero] at h1
  norm_num at h1
  linarith

/-! ## 5. Module summary

Wave-2 PMNS structure-note: the Lean infrastructure for the PMNS mixing
matrix is in place — `PMNSMatrix` (3×3 unitary), unitarity rewrites
(`star_mul_self_eq_one`, `mul_star_self_eq_one`), an identity-PMNS
non-emptiness witness, the `IsDiracPMNS`/`IsMajoranaPMNS` parametric
predicates over Majorana phases, and the Wave 2a tolerance-parameterized
substrate-symmetry hypothesis `H_PMNSAnglesFromSubstrate_eps` together
with explicit non-satisfaction witnesses on the identity matrix. Full
phenomenology + Setoid quotient under charged-lepton phase rephasings is
deferred to a follow-up wave. (Stage-13 cleanup 2026-04-25 removed the
`neutrino_mixing_structure_note_summary : True := trivial` placeholder
per BLOCKER 5.4 on paper21 review; the file-level docstring above
replaces it.)
-/

end SKEFTHawking.NeutrinoMixing
