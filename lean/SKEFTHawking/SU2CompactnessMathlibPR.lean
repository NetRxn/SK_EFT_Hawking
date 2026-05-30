/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-1 residual Item C — Mathlib-PR-quality presentation of SU(d) compactness

Ships the **upstream-submission-ready presentation** of the special-unitary
group compactness substrate. The substantive proofs are already in
`SKEFTHawking.FKLW.SpecialUnitaryTopology` (Phase 6p Wave 2c.4a-substrate,
2026-05-12); this file re-presents them with worked examples and the
Mathlib4 target-filename annotation needed for upstream submission.

## What ships here (re-presentation of Phase 6p substrate)

For every `d : ℕ`:

  * `Matrix.specialUnitaryGroup_isClosed` — SU(d) is a closed subset of
    `Matrix (Fin d) (Fin d) ℂ`.
  * `Matrix.specialUnitaryGroup_isCompact` — SU(d) carrier set is compact.
  * `Matrix.instCompactSpaceSpecialUnitaryGroup` — `CompactSpace`
    typeclass instance at the subtype level.

(The corresponding U(d) versions live in the same predecessor file.)

These were authored under the in-tree-build authorization of Phase 6p
(amended 2026-05-12 PM axiom-sign-off policy). The naming conventions
already follow Mathlib's `Matrix.*` snake_case / `inst*` typeclass
patterns; this file is the explicit upstream-ready packaging.

**HONEST SCOPE (M-track, per 2026-05-30 adversarial review).** This file is an **alias /
re-presentation** layer: the canonical-named declarations below are thin wrappers around the
*already-proved* `SpecialUnitaryTopology` substrate (no new mathematical content is created here —
the value is the Mathlib-name packaging + worked examples for upstream submission). Contrast with
M.1 (`MatrixBCHCubicMathlibPR`, `bchOrder2Cubic_Fin`), which is a genuine **new Fin-`d` generalization**
(substantive extraction, not an alias). When citing the M-track as "Mathlib-PR-ready," distinguish the
genuine-extraction PRs (M.1) from the alias/packaging PRs (this file): both are submission-shaped, but
only the former adds a theorem not already in-tree.

## Mathlib4 target

Recommended target file under Mathlib4:
  `Mathlib/LinearAlgebra/UnitaryGroup/Topology.lean`

(or extending the existing `Mathlib/LinearAlgebra/UnitaryGroup.lean`, which
already defines `Matrix.unitaryGroup` and `Matrix.specialUnitaryGroup` but
does not yet provide their topological-group structure).

Mathlib4 v4.29.1 has:
  * `Matrix.unitaryGroup` and `Matrix.specialUnitaryGroup` definitions
    (`Mathlib.LinearAlgebra.UnitaryGroup`)
  * `Matrix.mem_unitaryGroup_iff`,
    `Matrix.mem_specialUnitaryGroup_iff` (same file)
  * `IsCompact.of_isClosed_subset`, `isCompact_pi_infinite`
    (`Mathlib.Topology.MetricSpace`, `Mathlib.Topology.Compactness.Constructions`)

Mathlib4 v4.29.1 lacks:
  * Compactness of `Matrix.unitaryGroup` or `Matrix.specialUnitaryGroup`.

Adding both compactness lemmas + the `CompactSpace` typeclass instances
is a natural Mathlib upstream contribution. The PR would unlock downstream
Lie-theory and quantum-compilation formalizations (the present project
being one such consumer; the Mathlib-quantum-computing community a more
general consumer).

## Worked examples (downstream consumer demonstrations)

Below the lemma re-exports, this file includes:
  * SU(2) explicit instantiation: `IsCompact (specialUnitaryGroup (Fin 2) ℂ : Set _)`.
  * SU(3) explicit instantiation: `IsCompact (specialUnitaryGroup (Fin 3) ℂ : Set _)`.
  * Subtype-level usage of the `CompactSpace` instance via `isCompact_univ`.

## Consumer relationship

The Phase 6x Track T-S′ chain
(`SKEFTHawking.FKLW.RossSelingerLightweight`) consumes the SU(2)
compactness via the typeclass instance — concretely, it derives the
explicit `IsCompact (Set.univ : Set ↥(SU(2)))` hypothesis required by
`finite_epsilon_net_of_compact_dense` from `isCompact_univ` applied to
the `[CompactSpace ↥(SU(2))]` instance shipped by the substrate. After
this Item-C ship, the explicit-hypothesis discharge in T-S′ remains
correct (because `isCompact_univ` continues to route through the same
typeclass instance) and additionally the new file makes the substrate
documentation explicit for upstream submission.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Honest status

The four substantive lemmas were SHIPPED in
`SKEFTHawking.FKLW.SpecialUnitaryTopology` on 2026-05-12 (Phase 6p Wave
2c.4a-substrate); this file is the **Mathlib-PR-quality re-presentation**
with worked examples and submission-target annotation. No new
substantive content; the upstream PR step is the natural follow-on.

-/

import SKEFTHawking.FKLW.SpecialUnitaryTopology

set_option autoImplicit false

namespace Matrix

open scoped Matrix

/-! ## 1. Re-export of compactness lemmas (Mathlib-PR-quality aliases)

The following four declarations re-export the Phase 6p Wave 2c.4a-substrate
ships at canonical Mathlib-style names. Each is a direct alias of the
substantive proof in `SKEFTHawking.FKLW.SpecialUnitaryTopology`. -/

/-- **U(d) is a closed subset of `Matrix (Fin d) (Fin d) ℂ`** (Mathlib-PR alias).

Preimage of `{1}` under the continuous map `M ↦ M * Mᴴ`. Substantive proof
in `SKEFTHawking.FKLW.SpecialUnitaryTopology.Matrix.unitaryGroup_isClosed`. -/
theorem unitaryGroup_isClosed_PR (d : ℕ) :
    IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
  Matrix.unitaryGroup_isClosed d

/-- **SU(d) is a closed subset of `Matrix (Fin d) (Fin d) ℂ`** (Mathlib-PR alias).

Intersection of `unitaryGroup` (closed) with the preimage of `{1}` under
the continuous `det`. Substantive proof in
`SKEFTHawking.FKLW.SpecialUnitaryTopology.Matrix.specialUnitaryGroup_isClosed`. -/
theorem specialUnitaryGroup_isClosed_PR (d : ℕ) :
    IsClosed (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
  Matrix.specialUnitaryGroup_isClosed d

/-- **U(d) carrier set is compact** (Mathlib-PR alias).

Closed subset of a compact bounding box (the d×d product of
`Metric.closedBall (0 : ℂ) 1`, via `unitaryGroup_entry_norm_le_one`).
Substantive proof in
`SKEFTHawking.FKLW.SpecialUnitaryTopology.Matrix.unitaryGroup_isCompact`. -/
theorem unitaryGroup_isCompact_PR (d : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
  Matrix.unitaryGroup_isCompact d

/-- **SU(d) carrier set is compact** (Mathlib-PR alias).

Closed subset of the compact U(d). Substantive proof in
`SKEFTHawking.FKLW.SpecialUnitaryTopology.Matrix.specialUnitaryGroup_isCompact`. -/
theorem specialUnitaryGroup_isCompact_PR (d : ℕ) :
    IsCompact (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) :=
  Matrix.specialUnitaryGroup_isCompact d

end Matrix

/-! ## 2. Worked examples — SU(2) and SU(3)

These demonstrate the canonical downstream-consumer pattern: deriving
the subtype-level `IsCompact (Set.univ)` from the typeclass-coerced
compactness instance. The pattern matches what the Phase 6x Track T-S′
chain (`RossSelingerLightweight.lean`) uses. -/

namespace Matrix.SU2CompactnessMathlibPR.Examples

open Matrix

/-- **Worked example, SU(2) carrier set**: directly from the alias. -/
example : IsCompact (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Matrix.specialUnitaryGroup_isCompact_PR 2

/-- **Worked example, SU(3) carrier set**: directly from the alias. -/
example : IsCompact (Matrix.specialUnitaryGroup (Fin 3) ℂ : Set (Matrix (Fin 3) (Fin 3) ℂ)) :=
  Matrix.specialUnitaryGroup_isCompact_PR 3

/-- **Worked example, subtype-level**: SU(2) is a compact space, hence its
`Set.univ` is compact. This is the form consumed by
`finite_epsilon_net_of_compact_dense` in
`SKEFTHawking.FKLW.ConstructiveEpsilonNet`. -/
example : IsCompact (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
  isCompact_univ

/-- **Worked example, subtype-level SU(3)**: same pattern at d = 3. -/
example : IsCompact (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 3) ℂ)) :=
  isCompact_univ

/-- **Worked example, `CompactSpace` typeclass usage**: the instance is
auto-derived by typeclass synthesis. -/
example : CompactSpace ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := inferInstance

end Matrix.SU2CompactnessMathlibPR.Examples
