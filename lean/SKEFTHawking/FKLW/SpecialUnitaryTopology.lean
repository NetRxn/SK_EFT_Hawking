/-
SK_EFT_Hawking Phase 6p Wave 2c.4a-substrate (2026-05-12):
Mathlib-grade topological substrate for the unitary and special unitary
matrix groups U(d) and SU(d).

This module ships the **`IsCompact` substrate** that the substantive
Aharonov-Arad Bridge Lemma 4.1 + Lemma 6.1/6.2 iteration proof (Wave
2c.4a.full follow-up) requires. The proofs are direct Mathlib-grade
linear algebra + general topology — no spectral theorem needed.

## What ships here

For every `d : ℕ`:

  * `Matrix.unitaryGroup_isCompact` — the carrier set
    `(Matrix.unitaryGroup (Fin d) ℂ : Set _)` is compact in
    `Matrix (Fin d) (Fin d) ℂ`.
  * `Matrix.specialUnitaryGroup_isCompact` — the carrier set
    `(Matrix.specialUnitaryGroup (Fin d) ℂ : Set _)` is compact.
  * `Matrix.instCompactSpaceUnitaryGroup` — `CompactSpace` instance on
    the `Submonoid`-coerced subtype (so that `IsCompact (Set.univ : Set
    (Matrix.unitaryGroup (Fin d) ℂ))` holds at the subtype level).
  * `Matrix.instCompactSpaceSpecialUnitaryGroup` — same for `SU(d)`.
  * Two helper lemmas:
      - `Matrix.unitaryGroup_isClosed` — U(d) is closed in
        `Matrix (Fin d) (Fin d) ℂ`.
      - `Matrix.specialUnitaryGroup_isClosed` — SU(d) is closed.
      - `Matrix.unitaryGroup_entry_norm_le_one` — for any unitary `M`
        and entry `(i, j)`, `‖M i j‖ ≤ 1`. (Used internally; also useful
        on its own.)

## Proof strategy (the textbook argument, made Lean-friendly)

  1. **Bound**: U(d) is contained in the closed `d × d`-product of
     `Metric.closedBall (0 : ℂ) 1` (since `M Mᴴ = 1` forces every row to
     have Euclidean norm 1, hence every entry has modulus at most 1).
  2. **Compact bounding box**: This product of closed unit balls is
     compact via `isCompact_pi_infinite` twice (once for each `Fin d`
     index of the matrix).
  3. **Closed**: U(d) is the preimage of the singleton `{1}` under the
     continuous map `M ↦ M * Mᴴ`. (`Matrix.mem_unitaryGroup_iff`.)
  4. **Heine-Borel-style closure**: closed subset of compact set is
     compact (`IsCompact.of_isClosed_subset`).
  5. **SU(d)**: closed subset of compact U(d) (det⁻¹ {1} ∩ U(d)).

This avoids any reliance on Mathlib's `Matrix.l2_opNorm_*`, on the
spectral theorem, or on matrix exp — all of which are powerful enough
for the path-connectedness side (deferred) but unnecessary here.

## What is shipped here vs. in the companion module

  * **Compactness** (this file): `IsCompact` on the carrier sets +
    `CompactSpace` instances on the Submonoid-coerced subtypes.
  * **Path-connectedness / Connectedness** (companion file
    `SpecialUnitaryPathConnected.lean`, also Wave 2c.4a-substrate
    2026-05-12): `PathConnectedSpace` + `ConnectedSpace` instances
    routing through Mathlib's `Unitary.instLocPathConnectedSpace`
    on `CStarMatrix` + phase-shift + finite-spectrum avoidance +
    det-correction for SU(d).

  * No `IsLieGroup` instance (Mathlib does not yet have one for U(d) /
    SU(d) in general; the Aharonov-Arad proof does not require it —
    only compactness + path-connectedness, both now shipped).

## Pipeline invariants

  * Pipeline Invariant #10: **No `set_option maxHeartbeats`.** All
    proofs decompose into ≤ 50 LoC sub-lemmas.
  * Pipeline Invariant #15: **ZERO new project-local axioms.**

## Mathlib alignment

The naming conventions follow Mathlib's: `Matrix.unitaryGroup_isCompact`
(snake_case, identifier-prefixed) rather than camelCase. The
`CompactSpace` instances use the standard `inst*` naming and are
registered via `instance`. This file is written so that, modulo
adjusting docstrings, the four substantive lemmas could be lifted into
Mathlib4 as an upstream PR.

Primary citation: Aharonov & Arad 2011, *New J. Phys.* 13 035019;
arXiv:quant-ph/0605181 §4 (Bridge Lemma 4.1) requires SU(d) compactness
as a non-negotiable analytical prerequisite.
-/

import Mathlib

set_option autoImplicit false

namespace Matrix

open scoped Matrix

/-! ## 1. Entry-wise bound for unitary matrices

The key analytic content: if `M` is unitary then every entry has
modulus at most 1. This is the bound that establishes containment in
the compact bounding box. -/

/-- **Entry-wise bound for unitary matrices.** Every entry `M i j` of a
unitary matrix `M : Matrix.unitaryGroup (Fin d) ℂ` satisfies
`‖M i j‖ ≤ 1`.

Proof: `M * Mᴴ = 1` implies `(M * Mᴴ) i i = ∑ k, ‖M i k‖² = 1`, so
each `‖M i k‖² ≤ 1` (non-negative summands summing to 1), in particular
`‖M i j‖² ≤ 1`, hence `‖M i j‖ ≤ 1`. -/
theorem unitaryGroup_entry_norm_le_one {d : ℕ}
    (M : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) :
    ‖(M : Matrix (Fin d) (Fin d) ℂ) i j‖ ≤ 1 := by
  obtain ⟨M, hM⟩ := M
  simp only
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hM
  -- (M * Mᴴ) i i = 1
  have h_diag : (M * Mᴴ) i i = 1 := by rw [hM]; simp
  -- Expand the diagonal entry as a sum of |M i k|² (viewed as ℂ then ℝ).
  have h_sum : ∑ k, M i k * star (M i k) = 1 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h_diag
    convert h_diag using 1
  have h_term : ∀ k, M i k * star (M i k) = ((‖M i k‖^2 : ℝ) : ℂ) := by
    intro k
    rw [show (star (M i k) : ℂ) = (starRingEnd ℂ) (M i k) from rfl]
    rw [Complex.mul_conj, ← Complex.sq_norm]
  rw [Finset.sum_congr rfl (fun k _ => h_term k)] at h_sum
  rw [← Complex.ofReal_sum] at h_sum
  have h_sum_re : ∑ k, ‖M i k‖^2 = (1 : ℝ) := by exact_mod_cast h_sum
  -- Now bound: ‖M i j‖² ≤ ∑ k, ‖M i k‖² = 1.
  have h_sub : ‖M i j‖^2 ≤ ∑ k, ‖M i k‖^2 := by
    refine Finset.single_le_sum (f := fun k => ‖M i k‖^2) ?_ (Finset.mem_univ j)
    intros; exact sq_nonneg _
  rw [h_sum_re] at h_sub
  have h_norm_nn : (0 : ℝ) ≤ ‖M i j‖ := norm_nonneg _
  nlinarith

/-! ## 2. Closedness of the unitary and special unitary groups -/

/-- **The unitary group is closed.** As a subset of
`Matrix (Fin d) (Fin d) ℂ`, the carrier of `Matrix.unitaryGroup (Fin d) ℂ`
is closed.

Proof: it is the preimage of the singleton `{1}` under the continuous
map `M ↦ M * Mᴴ`. -/
theorem unitaryGroup_isClosed (d : ℕ) :
    IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  have h_eq :
      (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) =
        (fun M => M * Mᴴ) ⁻¹' {1} := by
    ext M
    simp [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [h_eq]
  refine IsClosed.preimage ?_ isClosed_singleton
  exact continuous_id.mul continuous_id.matrix_conjTranspose

/-- **The special unitary group is closed.** As a subset of
`Matrix (Fin d) (Fin d) ℂ`, the carrier of
`Matrix.specialUnitaryGroup (Fin d) ℂ` is closed.

Proof: it is the intersection of `unitaryGroup` (closed) with the
preimage of `{1}` under the continuous `det`. -/
theorem specialUnitaryGroup_isClosed (d : ℕ) :
    IsClosed (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  have h_eq :
      (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) =
        (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) ∩
          (Matrix.det ⁻¹' {1}) := by
    ext M
    simp [Matrix.mem_specialUnitaryGroup_iff, Set.mem_inter_iff]
  rw [h_eq]
  refine (unitaryGroup_isClosed d).inter ?_
  exact IsClosed.preimage (Continuous.matrix_det continuous_id) isClosed_singleton

/-! ## 3. Compactness of the unitary and special unitary groups -/

/-- **Auxiliary: the d×d-bounding-box is compact.** The set of matrices
whose every entry lies in the closed unit ball `Metric.closedBall 0 1` is
compact, by iterated application of `isCompact_pi_infinite` (twice — once
per matrix index). -/
private theorem boundingBox_isCompact (d : ℕ) :
    IsCompact
      {M : Matrix (Fin d) (Fin d) ℂ | ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) 1} := by
  have h1 : ∀ _ : Fin d, IsCompact (Metric.closedBall (0 : ℂ) 1) := fun _ =>
    isCompact_closedBall _ _
  have h2 : ∀ _ : Fin d,
      IsCompact {g : Fin d → ℂ | ∀ j, g j ∈ Metric.closedBall (0 : ℂ) 1} :=
    fun _ => isCompact_pi_infinite h1
  exact isCompact_pi_infinite h2

/-- **The unitary group is compact.** The carrier of
`Matrix.unitaryGroup (Fin d) ℂ` is a compact subset of
`Matrix (Fin d) (Fin d) ℂ`.

Proof: it is closed (`unitaryGroup_isClosed`) and contained in the
compact bounding box `{M | ∀ i j, ‖M i j‖ ≤ 1}`
(`boundingBox_isCompact`, witnessed by `unitaryGroup_entry_norm_le_one`).
A closed subset of a compact set is compact
(`IsCompact.of_isClosed_subset`). -/
theorem unitaryGroup_isCompact (d : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  have h_subset :
      (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) ⊆
        {M : Matrix (Fin d) (Fin d) ℂ | ∀ i j, M i j ∈ Metric.closedBall (0 : ℂ) 1} := by
    intro M hM i j
    rw [Metric.mem_closedBall, dist_zero_right]
    exact unitaryGroup_entry_norm_le_one ⟨M, hM⟩ i j
  exact (boundingBox_isCompact d).of_isClosed_subset (unitaryGroup_isClosed d) h_subset

/-- **The special unitary group is compact.** The carrier of
`Matrix.specialUnitaryGroup (Fin d) ℂ` is a compact subset of
`Matrix (Fin d) (Fin d) ℂ`.

Proof: SU(d) is a closed subset (`specialUnitaryGroup_isClosed`) of the
compact U(d) (`unitaryGroup_isCompact`). -/
theorem specialUnitaryGroup_isCompact (d : ℕ) :
    IsCompact (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  refine (unitaryGroup_isCompact d).of_isClosed_subset (specialUnitaryGroup_isClosed d) ?_
  intro M hM
  rw [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff] at hM
  exact hM.1

/-! ## 4. `CompactSpace` instances on the subtypes

Mathlib uses two equivalent encodings of "compact":
  - `IsCompact (S : Set X)` — a property of a subset.
  - `CompactSpace ↥S` — a typeclass on the subtype.
These are linked by `isCompact_iff_compactSpace`. We register the
`CompactSpace` form as instance so that downstream consumers
(`Submonoid` coercions, the `BridgeProof` iteration scaffold) can use
typeclass resolution. -/

/-- **`CompactSpace` instance on the unitary group subtype.** -/
noncomputable instance instCompactSpaceUnitaryGroup (d : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin d) ℂ) :=
  isCompact_iff_compactSpace.mp (unitaryGroup_isCompact d)

/-- **`CompactSpace` instance on the special unitary group subtype.** -/
noncomputable instance instCompactSpaceSpecialUnitaryGroup (d : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin d) ℂ) :=
  isCompact_iff_compactSpace.mp (specialUnitaryGroup_isCompact d)

end Matrix

/-! ## 5. Module summary

SKEFTHawking.FKLW.SpecialUnitaryTopology (Wave 2c.4a-substrate ship,
2026-05-12):

  * **`Matrix.unitaryGroup_entry_norm_le_one`** (substantive): the
    entry-wise modulus bound. Pure linear algebra, ~20 LoC.
  * **`Matrix.unitaryGroup_isClosed`** (substantive): U(d) is closed
    as preimage of `{1}` under continuous `M ↦ M Mᴴ`.
  * **`Matrix.specialUnitaryGroup_isClosed`** (substantive): SU(d) is
    closed as intersection of U(d) with `det⁻¹ {1}`.
  * **`Matrix.unitaryGroup_isCompact`** (HEADLINE): U(d) is compact.
  * **`Matrix.specialUnitaryGroup_isCompact`** (HEADLINE): SU(d) is
    compact.
  * **`Matrix.instCompactSpaceUnitaryGroup`** (instance): subtype-level
    `CompactSpace`.
  * **`Matrix.instCompactSpaceSpecialUnitaryGroup`** (instance):
    subtype-level `CompactSpace`.

## Honest status

**Compactness — SHIPPED.** Both U(d) and SU(d) are compact and registered
as `CompactSpace` instances for any `d : ℕ`. The proofs are Mathlib-grade
linear-algebra-and-topology, axiom-free, ~150 LoC total. They could be
lifted to a Mathlib4 upstream PR with minor docstring polish (contingent
on separate user sign-off; the in-tree-build authorization is implicit
per the amended Phase 6p axiom-sign-off policy of 2026-05-12 PM).

**Path-connectedness — SHIPPED** in the companion module
`SpecialUnitaryPathConnected.lean` (Wave 2c.4a-substrate-PathConnected,
2026-05-12). The strategy used there avoids the matrix spectral theorem
entirely by routing through Mathlib's `Unitary.instLocPathConnectedSpace`
(C⋆-algebra unitary local-path-connectedness applied to `CStarMatrix`)
+ a direct phase-shift / finite-spectrum-avoidance argument + a
determinant-correction for SU(d). This is the substantive analytical
content that Aharonov-Arad's Lemma 6.1 explicitly needs (vector
transport across continuous SU(d) paths).

**Where this fits into the Aharonov-Arad discharge chain:**

  1. ✅ Wave 2c.4 (already shipped): predicate substrate + bridge axiom.
  2. ✅ Wave 2c.4c (already shipped): `LieSpan ⟹ bridge_exists`
        (axiom-free linear-algebra bridging lemma).
  3. ✅ Wave 2c.4a-substrate (THIS SHIP — compactness): SU(d)/U(d).
  4. ✅ Wave 2c.4a-substrate-PathConnected (companion ship): SU(d)/U(d)
        path-connectedness + connectedness.
  5. ⏳ Wave 2c.4a.full (residual): Bridge Lemma 4.1 iteration proof +
        Lemma 6.1 vector transport + Lemma 6.2 basis-rotation iteration.

Primary citations:
  - Aharonov & Arad 2011, *New J. Phys.* 13 035019;
    arXiv:quant-ph/0605181 §4 (Bridge Lemma 4.1 — requires SU(d) compact).
  - Standard linear algebra: any reference, e.g. Hall, *Lie Groups, Lie
    Algebras, and Representations* §1.2 (compactness of unitary groups).

Zero sorry. Zero new project-local axioms. -/
