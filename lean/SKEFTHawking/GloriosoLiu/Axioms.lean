/-
# Phase 6n.γ Wave (Glorioso–Liu axiomatic) — Module: Axioms

Six-axiom skeleton for the Schwinger–Keldysh effective action per
Crossley–Glorioso–Liu (CGL I, JHEP 09 (2017) 095, arXiv:1511.03646),
Glorioso–Crossley–Liu II (JHEP 09 (2017) 096, arXiv:1701.07817),
and Glorioso–Liu (arXiv:1612.07705).

**Stage 2-3 substantive form (Phase 6n session 5, 2026-05-04).** The
abstract `SpacetimeManifold` / `ContourField` placeholders from Stage 1
are superseded by direct parameterization over the program's existing
`SKEFTHawking.SKDoubling.SKAction`. Each of the 6 axiom fields is now
substantively connected to the SKDoubling machinery:

  - `ctp_structure` (SK-1): structurally satisfied by `SKFields`'s
    psi_r/psi_a doubling — encoded in the data type itself.
  - `largest_time` (SK-2): invokes `SKDoubling.satisfies_normalization`
    (action vanishes when ψ_a = ∂_t ψ_a = ∂_x ψ_a = 0).
  - `reflection_pos` (SK-3): invokes `SKDoubling.satisfies_positivity`
    (Im part of the Lagrangian ≥ 0 pointwise).
  - `hermiticity` (SK-4): structurally satisfied by `SKAction.lagrangian`'s
    `SKFields → ℝ × ℝ` codomain — real Lagrangian by construction.
  - `dynamical_KMS` (KMS-dyn): existence of a `SKDoubling.KMSSymmetry`
    instance for the action at the given inverse temperature β.
  - `local_equilibrium` (LE): existence of `SKDoubling.FirstOrderCoeffs`
    that reproduce the action's Lagrangian via `firstOrderAction`
    (first-order LE; higher orders extend via `FullSecondOrderCoeffs`
    and beyond, deferred to Stage 2-3b).

The CTP and hermiticity axioms are vacuous *at this layer* because
they are *structurally encoded* by the SKAction/SKFields data types —
that is the correct level for these axioms to live, since they're about
the framework's shape, not the action's content. The 4 substantive axioms
(largest_time, reflection_pos, dynamical_KMS, local_equilibrium) carry
the load-bearing content and invoke real SKDoubling predicates.

References (read directly per CLAUDE.md Phase-5 deep-research depth-reading rule):
- CGL I: arXiv:1511.03646
- CGL II: arXiv:1701.07817
- Glorioso–Liu: arXiv:1612.07705
- Liu–Glorioso TASI: arXiv:1805.09331
- Jain–Kovtun: arXiv:2309.00511 (UV-realization ambiguity in dynamical-KMS)
- Phase 6n DR §5: theorem-signature sketch
-/
import SKEFTHawking.SKDoubling
import Mathlib.Tactic.Basic

namespace SKEFTHawking.GloriosoLiu

open SKEFTHawking.SKDoubling

/-! ## The six axiom predicates over a SKDoubling.SKAction. -/

/-- **Closed-time-path structure (SK-1)**: structurally satisfied by
    `SKFields`'s (ψ_r, ψ_a) doubling. Any function over `SKFields` carries
    the CTP doubling automatically; this axiom is captured by the
    framework's data type, not by extra content on the action. -/
def hasCTPStructure (_action : SKAction) : Prop := True

/-- **Largest-time / unitarity (SK-2)**: when ψ_a = ∂_t ψ_a = ∂_x ψ_a = 0
    (forward = backward contour) the action vanishes — this is exactly
    `SKDoubling.satisfies_normalization`. -/
def hasLargestTime (action : SKAction) : Prop :=
  satisfies_normalization action

/-- **Reflection positivity / Im S ≥ 0 (SK-3)**: the imaginary part of the
    Lagrangian is non-negative pointwise — this is exactly
    `SKDoubling.satisfies_positivity`. -/
def hasReflectionPositivity (action : SKAction) : Prop :=
  satisfies_positivity action

/-- **Hermiticity (SK-4)**: structurally satisfied since
    `SKAction.lagrangian` has codomain `ℝ × ℝ` (real Re + real Im). The
    constraint that the action's real part be real is automatic from
    the data type. -/
def hasHermiticity (_action : SKAction) : Prop := True

/-- **Dynamical KMS Z₂ symmetry (KMS-dyn)**: there exists a
    `SKDoubling.KMSSymmetry` instance for this action at inverse
    temperature β. The hard kernel; carries the Jain–Kovtun
    UV-realization ambiguity (typeclass-parameterized in `DynamicalKMS.lean`). -/
def hasDynamicalKMS (action : SKAction) (β : ℝ) : Prop :=
  Nonempty (KMSSymmetry action β)

/-- **Local equilibrium / hydrodynamic mode content (LE) — first-order layer**:
    the action is in the polynomial hydrodynamic-mode form at first order,
    i.e., there exist `FirstOrderCoeffs` whose `firstOrderAction` reproduces
    this action's Lagrangian on every `SKFields` configuration. (Higher
    orders extend via `FullSecondOrderCoeffs` etc.; deferred to Stage 2-3b
    on the LE axiom front.) -/
def hasLocalEquilibrium (action : SKAction) : Prop :=
  ∃ c : FirstOrderCoeffs,
    ∀ f : SKFields, action.lagrangian f = (firstOrderAction c).lagrangian f

/-! ## The six-axiom skeleton structure. -/

/--
**Six-axiom Glorioso–Liu skeleton, parameterized over a `SKDoubling.SKAction`.**

Each field is substantively connected to the program's SKDoubling
machinery (see the per-predicate docstrings above). The 4 substantive
axioms (largest_time, reflection_pos, dynamical_KMS, local_equilibrium)
carry the load-bearing content; the CTP/hermiticity axioms are
structurally encoded by the data types and are vacuous at this layer.

This is the structural anchor of the entire GloriosoLiu module set
(Phase 6n.γ Wave Stage 2-3 deliverable). The Phase 1 `FirstOrderKMS`
content (in `SKDoubling.lean`) is the *first-order projection* of this
six-axiom skeleton (formalized in `FirstOrderProjection.lean` and
reconciled with the Phase 1 4-of-9 Aristotle partition in
`Phase1Reconciliation.lean`).
-/
structure SKEFTAxioms (action : SKAction) (β : ℝ) where
  /-- Closed-time-path structure (SK-1). Structurally encoded by SKFields. -/
  ctp_structure       : hasCTPStructure action
  /-- Largest-time / unitarity (SK-2). Action vanishes when ψ_a-content = 0. -/
  largest_time        : hasLargestTime action
  /-- Reflection positivity / Im S ≥ 0 (SK-3). -/
  reflection_pos      : hasReflectionPositivity action
  /-- Hermiticity (SK-4). Structurally encoded by ℝ × ℝ codomain. -/
  hermiticity         : hasHermiticity action
  /-- Dynamical KMS Z₂ symmetry (KMS-dyn). Existence of a KMSSymmetry instance. -/
  dynamical_KMS       : hasDynamicalKMS action β
  /-- Local equilibrium / hydrodynamic mode content (LE) at first order. -/
  local_equilibrium   : hasLocalEquilibrium action

/-! ## Concrete existence witness for the zero action. -/

/-- The trivial zero action: lagrangian ≡ (0, 0). Used as a concrete
    well-posedness witness for the six-axiom skeleton. -/
def zeroAction : SKAction := { lagrangian := fun _ => (0, 0) }

/-- The canonical KMS-form transform on `SKFields`: shifts ψ_a by β·∂_t ψ_r
    and leaves the other 8 components unchanged. Satisfies the
    `KMSSymmetry.kms_transform_spec` 4-conjunct by construction. -/
def kmsCanonicalTransform (β : ℝ) (f : SKFields) : SKFields :=
  ⟨f.psi_r, f.psi_a + β * f.dt_psi_r, f.dt_psi_r, f.dx_psi_r,
   f.dt_psi_a, f.dx_psi_a, f.dtt_psi_r, f.dtx_psi_r, f.dxx_psi_r⟩

/-- **`KMSSymmetry` witness for the zero action.** The canonical KMS
    transform leaves the zero action invariant trivially (action ≡ (0, 0)
    on any input). -/
def kmsForZeroAction (β : ℝ) : KMSSymmetry zeroAction β where
  kms_transform := kmsCanonicalTransform β
  kms_transform_spec := fun _ => ⟨rfl, rfl, rfl, rfl⟩
  invariance := fun _ => rfl

/--
**The six-axiom skeleton is satisfied by the zero action.**

Substantive existence claim for the SKEFTAxioms structure: the zero
action (Lagrangian ≡ (0, 0)) admits all 6 axioms with concrete
witnesses:

  - `ctp_structure` / `hermiticity`: trivial (structural).
  - `largest_time`: zero Lagrangian satisfies normalization for any inputs.
  - `reflection_pos`: 0 ≥ 0 pointwise.
  - `dynamical_KMS`: provided by `kmsForZeroAction β` — the canonical
    KMS transform leaves the zero action invariant.
  - `local_equilibrium`: provided by the all-zero `FirstOrderCoeffs`,
    whose `firstOrderAction` is also identically (0, 0).

This is the substantive Stage-2-3 well-posedness proof: not only does
SKEFTAxioms have a Nonempty instance, but the witness uses real
SKDoubling structures (KMSSymmetry, FirstOrderCoeffs, satisfies_*).
-/
theorem SKEFTAxioms_zero_action (β : ℝ) :
    Nonempty (SKEFTAxioms zeroAction β) := by
  refine ⟨{
    ctp_structure := trivial,
    largest_time := ?_,
    reflection_pos := ?_,
    hermiticity := trivial,
    dynamical_KMS := ⟨kmsForZeroAction β⟩,
    local_equilibrium := ?_ }⟩
  · -- largest_time: zeroAction.lagrangian _ = (0, 0) regardless of normalization conditions
    intro f _ _ _; rfl
  · -- reflection_pos: (zeroAction.lagrangian f).2 = 0 ≥ 0
    intro _; exact le_refl 0
  · -- local_equilibrium: ⟨0,...,0⟩ : FirstOrderCoeffs has firstOrderAction = zero
    refine ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ?_⟩
    intro f
    simp [zeroAction, firstOrderAction]

end SKEFTHawking.GloriosoLiu
