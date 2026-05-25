/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.2 — Clifford+T closure-density witness (conditional framework)

Ships the closure-density witness for `cliffordTGeneratingSet` (Track T-S.1)
conditional on a single tracked Prop `cliffordT_v4_witness_tracked`, which
captures the load-bearing Lie-theoretic content of BMPRV 1999 in the
v4-witness shape already used by Phase 5 Step 13.

## Headline definitions

  * `cliffordT_v4_witness_tracked : Prop` — the tracked closure-density
    hypothesis at `H_of_G cliffordTGeneratingSet`. Has the same shape as
    `H_Fib_v4_witness` (Phase 5 Step 13): two ℝ-LI traceless skew-Hermitian
    flow-line tangents in 𝔰𝔲(2), with 1-parameter-subgroup flow lines
    contained in `H_of_G cliffordTGeneratingSet`.

  * `cliffordTClosureDenseWitness_of_tracked` — given the tracked Prop,
    builds `ClosureDenseWitness cliffordTGeneratingSet` (via Type-extraction
    from the Prop existential, using `Classical.choice` through
    `Nonempty.some`).

  * `cliffordT_density_of_tracked` — conditional density at Clifford+T,
    via Wave 2's `densityFromWitness`.

  * `cliffordT_H_of_G_eq_top_of_tracked` — `H_of_G cliffordTGeneratingSet =
    ⊤` conditional on the tracked Prop, via Wave 2's
    `H_of_G_eq_top_of_witness`.

## Substantive discharge of `cliffordT_v4_witness_tracked` (multi-session work)

The tracked Prop is the v4-witness predicate at `H_of_G cliffordTGeneratingSet`.
Discharging it unconditionally has two ingredients:

  1. **Accumulation at 1**: `AccPt 1 (Filter.principal (H_of_G
     cliffordTGeneratingSet : Set _))`. This is the load-bearing
     Lie-theoretic content of BMPRV 1999 in Lean: showing that
     `⟨H_SU, T_SU⟩` has a sequence approaching the identity. The standard
     argument: some element `M ∈ ⟨H_SU, T_SU⟩` has eigenvalue `exp(iθ)`
     with `θ/π ∉ ℚ`, then powers `M^n` form a dense subset of the
     U(1)-circle along M's eigenbasis, in particular approaching the
     identity for infinitely many n.

     The irrationality of θ/π for trace `2·cos(θ) = √2·sin(π/8)` (e.g.,
     the H_SU · T_SU product) requires a Niven-style algebraic-number-
     theoretic argument. Mathlib4 v4.29.1 does not have a usable
     Niven-style API; substantive discharge requires either substrate-
     PR-quality work or a direct case-by-case argument over the
     specific algebraic number `2·cos(θ) = √2·sin(π/8)`.

     Once accumulation at 1 is shown, Phase 5 Step 13's
     `vonNeumann_assemble_explicit_X_unconditional` (Phase 6p Wave
     2c.4a-R5.4-§9 substrate) directly produces the X₁ direction.

  2. **Second ℝ-LI direction** via Ad-conjugation: the standard pattern
     is to take X₂ := g.val · X₁ · star g.val for `g ∈ {H_SU, T_SU}`
     such that `g.val · X₁ ≠ X₁ · g.val` and `g.val · X₁ ≠ -(X₁ · g.val)`.
     Phase 5 Step 13's `ts_Ad_LI_of_not_commute_anticommute` then gives
     the ℝ-LI conclusion. The case analysis showing at least one of
     H_SU, T_SU satisfies these conditions for any non-zero X₁ ∈ ts
     is doable via 𝔰𝔲(2) Pauli decomposition (~150-300 LoC, mechanical
     case analysis).

The two ingredients above split the multi-session discharge of
`cliffordT_v4_witness_tracked` into: (a) accumulation-at-1 with
Niven-style irrationality, and (b) second-tangent case analysis.

**Pivot rule per Phase 6u roadmap (Pipeline Invariant #15):** the tracked
Prop is shipped *conditional* with explicit user sign-off requested for:
  - Using the tracked Prop in any external publication of Track T-S
    headlines (e.g., the Wave-6 Clifford+T strict headline becomes
    conditional on this Prop until substantive discharge ships).
  - Bundling/aggregating Track T-S into bundles D4 §9.8 (the bundle-lift
    procedure should reference `cliffordT_v4_witness_tracked` and its
    discharge status).

**Note on SU(2)-correction phase factors (CP1 RC5):** `H_SU` and `T_SU`
(see `CliffordTGeneratingSet.lean`) are the SU(2)-corrected forms of the
textbook Hadamard and T-gate (det = +1 lifts). BMPRV 1999 proves
closure-density of `⟨H, T⟩` in PU(2) for the textbook (U(2)) versions.
The SU(2) lift via global phase factors preserves the *projection* onto
PU(2), so the closure-density argument transfers: if `⟨H, T⟩` (textbook)
is dense in PU(2), then `⟨H_SU, T_SU⟩` (SU(2)-corrected) is dense in
SU(2) (or differs only by a discrete U(1) phase factor, which the v4
witness handles cleanly via 1-parameter-subgroup extraction). The
substantive discharge of `cliffordT_v4_witness_tracked` must explicitly
handle this phase-factor transport.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected (the tracked Prop is a `def`, not
  an `axiom`; it must be substantively discharged in a future wave OR
  shipped with explicit user sign-off as a permanent tracked hypothesis).
- **Strengthening discipline**: the conditional framework is non-trivial
  (the Type-extraction from the Prop is substantive via Nonempty.some);
  the headlines are load-bearing (they enable Track T-S.3–T-S.5 to
  proceed conditionally); the docstring is explicit about the
  substantive-discharge plan.

-/

import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.GenericClosureDenseWitness
import SKEFTHawking.FKLW.OneParameterSubgroupSU2

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix
open SKEFTHawking.FKLW
open SKEFTHawking.FKLW.SU2LieAlgebra
open SKEFTHawking.FKLW.SU2MatrixExp

/-! ## 1. The tracked closure-density hypothesis

Captures the v4-witness shape at `H_of_G cliffordTGeneratingSet`. -/

/-- **Tracked closure-density hypothesis for Clifford+T**.

The v4 witness predicate at `H_of_G cliffordTGeneratingSet`: two ℝ-LI
traceless skew-Hermitian flow-line tangents in 𝔰𝔲(2) with
1-parameter-subgroup flow lines `exp(ℝ • X_i) ⊆ H_of_G cliffordTGeneratingSet`.

Substantive discharge requires (a) accumulation at 1 via BMPRV 1999
Niven-style argument, and (b) second-tangent case analysis on the
H_SU/T_SU Pauli decomposition. Both are multi-session work; this Prop
is the tracked-Prop interface that downstream Track T-S work consumes. -/
def cliffordT_v4_witness_tracked : Prop :=
  ∃ X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ,
    X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) ∧
    X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2) ∧
    (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H_of_G cliffordTGeneratingSet ∧
        M.val = expAmbient (((t : ℝ) : ℂ) • X₁)) ∧
    (∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M ∈ H_of_G cliffordTGeneratingSet ∧
        M.val = expAmbient (((t : ℝ) : ℂ) • X₂)) ∧
    (∀ a b : ℝ, (a : ℂ) • X₁ + (b : ℂ) • X₂ = 0 → a = 0 ∧ b = 0)

/-! ## 2. Conditional ClosureDenseWitness construction

Given the tracked Prop, builds the `Type`-level `ClosureDenseWitness
cliffordTGeneratingSet` via Classical-choice extraction. -/

/-- **Conditional Clifford+T closure-density witness**.

Given the tracked v4-witness hypothesis at `H_of_G cliffordTGeneratingSet`,
extracts the explicit X₁, X₂ tangent data into the `ClosureDenseWitness`
structure (via `Nonempty.some + Classical.choice`).

The structure of the proof mirrors `fibonacciClosureDenseWitness` (Wave 2). -/
noncomputable def cliffordTClosureDenseWitness_of_tracked
    (h_tracked : cliffordT_v4_witness_tracked) :
    ClosureDenseWitness cliffordTGeneratingSet := by
  have h_ne : Nonempty (ClosureDenseWitness cliffordTGeneratingSet) := by
    obtain ⟨X₁, X₂, hX₁_ts, hX₂_ts, h_flow_X₁, h_flow_X₂, h_LI⟩ := h_tracked
    exact ⟨{ X₁ := X₁, X₂ := X₂
           , hX₁_ts := hX₁_ts, hX₂_ts := hX₂_ts
           , flow_X₁ := h_flow_X₁
           , flow_X₂ := h_flow_X₂
           , hLI := h_LI }⟩
  exact h_ne.some

/-! ## 3. Conditional density and `H_of_G = ⊤` for Clifford+T

Composes the conditional witness with the Wave 2 culmination theorems. -/

/-- **Conditional Clifford+T density (via tracked Prop)**.

Conditional on `cliffordT_v4_witness_tracked`, the Clifford+T
representation `ρ_CliffT` has dense range in SU(2). -/
theorem cliffordT_density_of_tracked
    (h_tracked : cliffordT_v4_witness_tracked) :
    IsDenseInSU2_gs cliffordTGeneratingSet :=
  densityFromWitness (cliffordTClosureDenseWitness_of_tracked h_tracked)

/-- **Conditional `H_of_G cliffordTGeneratingSet = ⊤`**.

Conditional on `cliffordT_v4_witness_tracked`, the closed subgroup
generated by `⟨H_SU, T_SU⟩` equals all of SU(2). -/
theorem cliffordT_H_of_G_eq_top_of_tracked
    (h_tracked : cliffordT_v4_witness_tracked) :
    H_of_G cliffordTGeneratingSet = ⊤ :=
  H_of_G_eq_top_of_witness (cliffordTClosureDenseWitness_of_tracked h_tracked)

end SKEFTHawking.FKLW.GenericSU2
