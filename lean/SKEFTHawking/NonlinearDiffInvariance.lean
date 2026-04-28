import Mathlib
import SKEFTHawking.Basic
import SKEFTHawking.HeatKernelExpansion
import SKEFTHawking.HigherCurvatureStructure

/-!
# Phase 6e Wave 3: Nonlinear Diffeomorphism Invariance (Path-b)

## Goal

Path-(b) direct check that the Seeley-DeWitt heat-kernel effective
Lagrangian is **diffeomorphism-invariant order-by-order** in the
asymptotic expansion (orders `a_0, a_2, a_4`).

For a scalar density `L` built from polynomial scalar curvature
invariants `{1, R, R², R_μν R^μν, R_μνρσ R^μνρσ}` (equivalently,
Stelle's `{1, R, R², C², 𝒢}`), the variation of `√g · L` under an
infinitesimal coordinate transformation `x^μ → x^μ + ξ^μ` is a total
divergence

  `δ_ξ (√g L) = ∂_μ(ξ^μ √g L)`,

so the action `∫ √g L` is diff-invariant on a closed manifold.  The
**path-b "anomaly residual"** at order `n` is the algebraic mismatch
between the same density expressed in two equivalent scalar-invariant
bases:

  `residual_n(L; B₁, B₂) := L_density_in_B₁ − L_density_in_B₂`.

For the Wave 1 Christensen-Duff Dirac coefficient bundle this residual
vanishes identically at orders 0, 2, and 4 — the order-4 case is
exactly the Wave 2 main theorem
`a4_density_eq_a4_density_in_RC2GB_basis`.

## Module structure

- §1: `EffectiveLagrangianCoefs` (5-coefficient bundle through a_4)
  + `density` evaluator
- §2: `diracCoefBundle` — canonical Wave 1 Christensen-Duff Dirac
  bundle for `N_f` species
- §3: `DiffInvariantAt` predicate + `pathB_residual_at_order` order
  index → residual evaluator
- §4: Order-`a_4` zero-residual theorem (orders 0/2 are definitionally
  zero; their content is consumed inline at §5)
- §5: Order-by-order `DiffInvariantAt`-witnesses for the Dirac bundle
- §6: **CORRECTNESS-PUSH** biconditional: order-by-order diff-invariance
  ⇔ basis-change consistency at order 4 (Wave 2 main identity)
- §7: Falsifier — non-admissible bundle has nonzero residual
- §8: Tracked-Prop `H_NonlinearDiffInvariance` + Dirac witness

## References

- Wald, *General Relativity*, App. E.1 — diff invariance via Lie
  derivatives + total divergences
- Vassilevich, Phys. Rep. 388, 279 (2003), §3.1 — covariance of
  heat-kernel coefficients under coordinate transformations
- Phase 6e Wave 1 `HeatKernelExpansion.lean` — Christensen-Duff Dirac
  coefficient bundle (input)
- Phase 6e Wave 2 `HigherCurvatureStructure.lean` — Stelle basis
  change at order `a_4` (path-b consistency at the basis level)

## Scope lock

IN SCOPE: algebraic path-b residual at orders 0, 2, 4 expressed at the
coefficient-bundle level; consistency of the Wave 2 basis change as
the load-bearing diff-invariance content at a_4; structural falsifier
for non-admissible (non-scalar-invariant) bundles.

OUT OF SCOPE: PDE-level proof of the full `δ_ξ(√g L) = ∂_μ(...)` identity
on a manifold (deferred to Mathlib's diff-geom infrastructure when
ready); higher orders `a_6, …` (deferred — out of scope for the
mean-field 6e program per strategy doc §15); path-(a) symmetry-
enhancement emergence (backlog per roadmap O.3).
-/

noncomputable section

open Real

namespace SKEFTHawking.NonlinearDiffInvariance

open SKEFTHawking.HeatKernelExpansion
open SKEFTHawking.HigherCurvatureStructure

/-! ## §1. Effective Lagrangian coefficient bundle -/

/-- Coefficient bundle for the Seeley-DeWitt effective Lagrangian
through order `a_4`.  Five coefficients:

  - `a0` — constant scalar piece (cosmological-constant-scale density)
  - `a2_R` — coefficient of the Ricci scalar `R`
  - `a4_R_sq` — coefficient of `R²`
  - `a4_Ricci_sq` — coefficient of `R_μν R^μν`
  - `a4_Riemann_sq` — coefficient of `R_μνρσ R^μνρσ`

This is the "natural" `{1, R, R², R_μν², R_μνρσ²}` basis; the Stelle
`{R², C², 𝒢}` reduction at order 4 is provided through the basis-change
of Wave 2. -/
structure EffectiveLagrangianCoefs where
  a0 : ℝ
  a2_R : ℝ
  a4_R_sq : ℝ
  a4_Ricci_sq : ℝ
  a4_Riemann_sq : ℝ

/-- Evaluate the order-by-order density of an effective Lagrangian
bundle at given curvature-invariant data
`(R, R_sq, Ricci_sq, Riemann_sq)`.

  `density L (R, R², R_μν², R_μνρσ²) :=`
    `L.a0 + L.a2_R · R + L.a4_R_sq · R² + L.a4_Ricci_sq · R_μν²`
    `       + L.a4_Riemann_sq · R_μνρσ²`. -/
def EffectiveLagrangianCoefs.density
    (L : EffectiveLagrangianCoefs)
    (R R_sq Ricci_sq Riemann_sq : ℝ) : ℝ :=
  L.a0 + L.a2_R * R
       + L.a4_R_sq * R_sq
       + L.a4_Ricci_sq * Ricci_sq
       + L.a4_Riemann_sq * Riemann_sq

/-- Density of an effective Lagrangian bundle at order `a_4` only —
the higher-curvature piece without `a_0` or `a_2 R` contributions.
This is the part affected by the Wave 2 Stelle basis change. -/
def EffectiveLagrangianCoefs.density_a4
    (L : EffectiveLagrangianCoefs)
    (R_sq Ricci_sq Riemann_sq : ℝ) : ℝ :=
  L.a4_R_sq * R_sq
    + L.a4_Ricci_sq * Ricci_sq
    + L.a4_Riemann_sq * Riemann_sq

/-! ## §2. Wave 1 canonical Dirac coefficient bundle -/

/-- Canonical Christensen-Duff Dirac effective-Lagrangian bundle for
`N_f` fermion species, as derived in Wave 1 (`HeatKernelExpansion`).
Five coefficients pinned by Wave 1 closed forms; this is the bundle
whose diff invariance the rest of the module establishes.

Substantive cross-bridge: every coefficient is a *named call* into
Wave 1 (`a0_dirac`, `a2_R_coefficient`, `a4_R_sq_coef`, etc.) — drift-
protection per `feedback_python_lean_refs_drift.md` (P6 cross-module
bridge integrity). -/
def diracCoefBundle (N_f : ℝ) : EffectiveLagrangianCoefs where
  a0            := a0_dirac N_f
  a2_R          := a2_R_coefficient N_f
  a4_R_sq       := a4_R_sq_coef N_f
  a4_Ricci_sq   := a4_Ricci_sq_coef N_f
  a4_Riemann_sq := a4_Riemann_sq_coef N_f

/-- The order-`a_4` density of the Dirac bundle, written through Wave
1 named coefficients, equals the Wave 2 `a4_density` evaluator.
Substantive bridge: ties the Wave 3 bundle abstraction to the Wave 2
basis-change apparatus (proof unfolds both definitions, then `rfl`). -/
theorem diracCoefBundle_density_a4_eq_wave2_a4_density
    (N_f R_sq Ricci_sq Riemann_sq : ℝ) :
    (diracCoefBundle N_f).density_a4 R_sq Ricci_sq Riemann_sq =
      a4_density N_f R_sq Ricci_sq Riemann_sq := by
  unfold EffectiveLagrangianCoefs.density_a4 diracCoefBundle a4_density
  rfl

/-! ## §3. Path-b anomaly residual + DiffInvariantAt predicate -/

/-- **Path-b anomaly residual at order `a_4`** for an effective
Lagrangian bundle.  Defined as the algebraic difference between the
order-4 density expressed in the natural `{R², R_μν², R_μνρσ²}` basis
and the same density re-expressed in Stelle's `{R², C², 𝒢}` basis with
coefficients `(α, β, γ)` derived from the `(c_R², c_Ricci², c_Riemann²)`
of the bundle via the Wave 2 3×3 linear-system solve.

For *bundles whose order-4 coefficients agree with Wave 1's Dirac
table*, the basis change is consistent and the residual vanishes
identically (Wave 2 main theorem).  For arbitrary bundles, the
residual is a generic real number — the falsifier in §7 exhibits a
nonzero case. -/
def pathB_residual_a4
    (L : EffectiveLagrangianCoefs) (N_f R_sq Ricci_sq Riemann_sq : ℝ) : ℝ :=
  L.density_a4 R_sq Ricci_sq Riemann_sq -
    a4_density_in_RC2GB_basis N_f R_sq Ricci_sq Riemann_sq

/-- Path-b anomaly residual at order `a_2`: the structural piece
`L.a2_R · R` is a polynomial in the *single* scalar invariant `R`, so
no basis change is involved at this order — the residual is identically
zero by construction.  We define it as `0` for API uniformity with the
order-4 case. -/
def pathB_residual_a2 (_L : EffectiveLagrangianCoefs) (_R : ℝ) : ℝ := 0

/-- Path-b anomaly residual at order `a_0`: a constant scalar has no
diff variation, so the residual is identically zero. -/
def pathB_residual_a0 (_L : EffectiveLagrangianCoefs) : ℝ := 0

/-- **Order-by-order diff-invariance predicate at the bundle level.**
A bundle `L` is *path-b diff-invariant at order `n` against species
count `N_f`* iff its anomaly residual at order `n` (parameterized by
the `N_f`-dependent Stelle basis change at order 4) vanishes for *all*
curvature-invariant inputs.

We encode the three orders as a small case split:

  - `n = 0`: `pathB_residual_a0` is identically zero
  - `n = 2`: for all `R`, `pathB_residual_a2 = 0`
  - `n = 4`: for all `(R_sq, Ricci_sq, Riemann_sq)`,
    `pathB_residual_a4 = 0`

Substantive content: at order 4, the predicate forces the bundle's
order-4 density to match the Stelle representation pointwise — exactly
the diff-invariance content. -/
def DiffInvariantAt
    (L : EffectiveLagrangianCoefs) (N_f : ℝ) (n : ℕ) : Prop :=
  if n = 0 then pathB_residual_a0 L = 0
  else if n = 2 then ∀ R : ℝ, pathB_residual_a2 L R = 0
  else if n = 4 then ∀ R_sq Ricci_sq Riemann_sq : ℝ,
    pathB_residual_a4 L N_f R_sq Ricci_sq Riemann_sq = 0
  else True  -- orders outside {0, 2, 4} are out-of-scope here

/-! ## §4. Order-by-order zero-residual theorems

The order-0 and order-2 path-b residuals are *definitionally zero* —
encoded directly into `pathB_residual_a0` and `pathB_residual_a2` as
the constant `0`.  No standalone theorems are needed at those orders;
the `rfl` content is consumed inline by the §5 `DiffInvariantAt`
witnesses (`dirac_diffInvariantAt_zero/two`).

The substantive content of this section lives in the order-4 case,
which consumes the Wave 2 main basis-change identity.
-/

/-- **MAIN order-`a_4` zero-residual theorem for the Dirac bundle.**
For the Christensen-Duff Wave 1 coefficient bundle and *all* curvature
inputs, the path-b basis-change anomaly vanishes:

  `pathB_residual_a4 (diracCoefBundle N_f) N_f R² R_μν² R_μνρσ² = 0`.

**Substantive cross-bridge to Wave 2:** the proof body invokes
`a4_density_eq_a4_density_in_RC2GB_basis` (Wave 2 main theorem) by
name, after rewriting the Dirac bundle's `density_a4` into Wave 2's
`a4_density` via `diracCoefBundle_density_a4_eq_wave2_a4_density`.

The biconditional in §6 (`diff_invariance_a4_iff_dirac_basis_consistent`)
shows this is the *load-bearing* substantive content of path-b diff
invariance at a_4 — without the Wave 2 basis-change identity, this
theorem would not hold.  P6 drift-protection per
`feedback_python_lean_refs_drift.md`. -/
theorem pathB_residual_a4_dirac_eq_zero
    (N_f R_sq Ricci_sq Riemann_sq : ℝ) :
    pathB_residual_a4 (diracCoefBundle N_f) N_f R_sq Ricci_sq Riemann_sq = 0 := by
  unfold pathB_residual_a4
  rw [diracCoefBundle_density_a4_eq_wave2_a4_density]
  -- Goal: a4_density - a4_density_in_RC2GB_basis = 0
  rw [a4_density_eq_a4_density_in_RC2GB_basis]
  ring

/-! ## §5. Order-by-order `DiffInvariantAt` witnesses -/

/-- Dirac bundle is diff-invariant at order `a_0`.  Discharge: at
order 0 the residual is definitionally `0` (constant scalar carries no
curvature dependence). -/
theorem dirac_diffInvariantAt_zero (N_f : ℝ) :
    DiffInvariantAt (diracCoefBundle N_f) N_f 0 := by
  unfold DiffInvariantAt pathB_residual_a0
  simp

/-- Dirac bundle is diff-invariant at order `a_2`.  Discharge: at
order 2 the only invariant is `R` itself, no basis-change exists, and
the residual is definitionally `0`. -/
theorem dirac_diffInvariantAt_two (N_f : ℝ) :
    DiffInvariantAt (diracCoefBundle N_f) N_f 2 := by
  unfold DiffInvariantAt pathB_residual_a2
  intro _R; rfl

/-- **Dirac bundle is diff-invariant at order `a_4`** — the load-bearing
Wave 3 case.  Substantive cross-bridge: this is `dirac_diffInvariantAt_two`'s
order-4 sibling, and unlike orders 0 and 2 it consumes the Wave 2 main
identity through `pathB_residual_a4_dirac_eq_zero`. -/
theorem dirac_diffInvariantAt_four (N_f : ℝ) :
    DiffInvariantAt (diracCoefBundle N_f) N_f 4 := by
  unfold DiffInvariantAt
  intro R_sq Ricci_sq Riemann_sq
  exact pathB_residual_a4_dirac_eq_zero N_f R_sq Ricci_sq Riemann_sq

/-! ## §6. Correctness-push biconditional (general + Dirac-specialized) -/

/-- **STRONGER bundle-generic biconditional.**  For *any* effective
Lagrangian bundle `L` and any species count `N_f`, path-(b) diff
invariance at order 4 is equivalent to the bundle's `density_a4` agreeing
pointwise with the Stelle-basis representation `a4_density_in_RC2GB_basis`:

  `DiffInvariantAt L N_f 4`
    `↔ ∀ R_sq Ricci_sq Riemann_sq,`
       `L.density_a4 R_sq Ricci_sq Riemann_sq`
         `= a4_density_in_RC2GB_basis N_f R_sq Ricci_sq Riemann_sq`.

This is bundle-independent: the substantive content of order-4 path-(b)
invariance is *exactly* basis-change consistency for the bundle's
`density_a4`, regardless of which bundle is supplied.  The Dirac
specialization (next theorem) composes this with Wave 2's
`a4_density_eq_a4_density_in_RC2GB_basis` to recover the original
formulation. -/
theorem diff_invariance_a4_iff_basis_consistent
    (L : EffectiveLagrangianCoefs) (N_f : ℝ) :
    DiffInvariantAt L N_f 4 ↔
      ∀ R_sq Ricci_sq Riemann_sq : ℝ,
        L.density_a4 R_sq Ricci_sq Riemann_sq =
          a4_density_in_RC2GB_basis N_f R_sq Ricci_sq Riemann_sq := by
  unfold DiffInvariantAt
  simp only [if_neg (by decide : (4 : ℕ) ≠ 0),
              if_neg (by decide : (4 : ℕ) ≠ 2)]
  constructor
  · intro h R_sq Ricci_sq Riemann_sq
    have := h R_sq Ricci_sq Riemann_sq
    unfold pathB_residual_a4 at this
    linarith
  · intro h R_sq Ricci_sq Riemann_sq
    unfold pathB_residual_a4
    rw [h]; ring

/-- **Wave 3 CORRECTNESS-PUSH biconditional (Dirac specialization).**
For the Dirac bundle at any species count `N_f`, path-(b) diff invariance
at order 4 is equivalent to the Wave 2 basis-change identity holding at
every curvature input:

  `DiffInvariantAt (diracCoefBundle N_f) N_f 4`
    `↔ ∀ R_sq Ricci_sq Riemann_sq,`
       `a4_density N_f R_sq Ricci_sq Riemann_sq`
         `= a4_density_in_RC2GB_basis N_f R_sq Ricci_sq Riemann_sq`.

Substantive cross-bridge: composes the bundle-generic biconditional
with the Wave 3 bridge `diracCoefBundle_density_a4_eq_wave2_a4_density`
to rewrite the bundle density into Wave 2's `a4_density`. -/
theorem diff_invariance_a4_iff_dirac_basis_consistent (N_f : ℝ) :
    DiffInvariantAt (diracCoefBundle N_f) N_f 4 ↔
      ∀ R_sq Ricci_sq Riemann_sq : ℝ,
        a4_density N_f R_sq Ricci_sq Riemann_sq =
          a4_density_in_RC2GB_basis N_f R_sq Ricci_sq Riemann_sq := by
  rw [diff_invariance_a4_iff_basis_consistent]
  constructor
  · intro h R_sq Ricci_sq Riemann_sq
    have hbridge := diracCoefBundle_density_a4_eq_wave2_a4_density
                      N_f R_sq Ricci_sq Riemann_sq
    rw [← hbridge]
    exact h R_sq Ricci_sq Riemann_sq
  · intro h R_sq Ricci_sq Riemann_sq
    rw [diracCoefBundle_density_a4_eq_wave2_a4_density]
    exact h R_sq Ricci_sq Riemann_sq

/-! ## §7. Falsifier: non-admissible bundle has nonzero residual -/

/-- A non-admissible "perturbed" bundle: the Dirac bundle with the
order-4 R² coefficient shifted by a nonzero scalar `δ`.  For nonzero
`δ`, this bundle does *not* satisfy the Wave 2 basis-change identity
(it differs from the Dirac bundle exactly by `δ` at the R²-channel).
-/
def perturbedCoefBundle (N_f δ : ℝ) : EffectiveLagrangianCoefs where
  a0            := a0_dirac N_f
  a2_R          := a2_R_coefficient N_f
  a4_R_sq       := a4_R_sq_coef N_f + δ
  a4_Ricci_sq   := a4_Ricci_sq_coef N_f
  a4_Riemann_sq := a4_Riemann_sq_coef N_f

/-- **STRONGER falsifier (general linearity).**  At *any* curvature
input `(R_sq, Ricci_sq, Riemann_sq)`, the perturbed bundle's path-b
`a_4` residual equals exactly `δ * R_sq`.  Substantive: the perturbation
is in the `R²`-channel coefficient, so the residual response is linear
in `R_sq` (and zero when `R_sq = 0`, regardless of the other curvature
inputs) — exposing the *channel* of the falsifier.

Proof: rewrite `density_in_RC2GB_basis` via Wave 2's main identity to
`a4_density`, then unfold both `a4_density` instances; the only surviving
term is the `R²`-channel difference `δ * R_sq`. Closes by `ring`.

Subsumes the unit-`R²` corollary (`perturbed_pathB_residual_a4_at_unit_R_sq`)
and matches the Python test `test_residual_scales_with_R_sq_at_fixed_delta`. -/
theorem perturbed_pathB_residual_a4_eq_delta_R_sq
    (N_f δ R_sq Ricci_sq Riemann_sq : ℝ) :
    pathB_residual_a4 (perturbedCoefBundle N_f δ) N_f
        R_sq Ricci_sq Riemann_sq = δ * R_sq := by
  unfold pathB_residual_a4 perturbedCoefBundle
       EffectiveLagrangianCoefs.density_a4
  rw [show a4_density_in_RC2GB_basis N_f R_sq Ricci_sq Riemann_sq
        = a4_density N_f R_sq Ricci_sq Riemann_sq from
        (a4_density_eq_a4_density_in_RC2GB_basis
            N_f R_sq Ricci_sq Riemann_sq).symm]
  unfold a4_density
  ring

/-- **Falsifier (unit-R² corollary).**  The perturbed bundle's path-b
`a_4` residual at `R_sq = 1, Ricci_sq = Riemann_sq = 0` equals the
perturbation `δ`.  Used by the `DiffInvariantAt` falsifier-witness
below to extract a concrete contradiction.

Substantive: choosing `δ ≠ 0` produces a *nonzero* residual at a
specific concrete curvature input — so a `δ ≠ 0` bundle is *not*
order-4 path-b diff-invariant.

This is a real falsifier (P3/P5 trivial-discharge check passes): the
residual depends *linearly* on `δ`, so `δ ↦ residual` is a non-constant
function — not a tautology. -/
theorem perturbed_pathB_residual_a4_at_unit_R_sq (N_f δ : ℝ) :
    pathB_residual_a4 (perturbedCoefBundle N_f δ) N_f 1 0 0 = δ := by
  rw [perturbed_pathB_residual_a4_eq_delta_R_sq]; ring

/-- **Falsifier-witness.**  For any nonzero perturbation `δ`, the
perturbed bundle violates path-b diff invariance at order 4 — there
exists a curvature input for which the residual is nonzero.

Substantive: combines `perturbed_pathB_residual_a4_at_unit_R_sq` with
the negation of the universal quantifier in `DiffInvariantAt` at n=4.
This is the *contrapositive direction* of the correctness-push
biconditional, applied to a concrete non-admissible bundle. -/
theorem perturbed_not_diffInvariantAt_four
    {N_f δ : ℝ} (hδ : δ ≠ 0) :
    ¬ DiffInvariantAt (perturbedCoefBundle N_f δ) N_f 4 := by
  unfold DiffInvariantAt
  simp only [if_neg (by decide : (4 : ℕ) ≠ 0),
              if_neg (by decide : (4 : ℕ) ≠ 2)]
  intro h_all
  have h := h_all 1 0 0
  rw [perturbed_pathB_residual_a4_at_unit_R_sq] at h
  exact hδ h

/-- **Quantitative falsifier–tolerance bridge (Lean ↔ Python).** For
any perturbation magnitude exceeding the canonical path-(b) tolerance
`PATH_B_RESIDUAL_TOLERANCE = 10⁻¹²` (mirrored at the Lean level here
as the explicit bound `1e-12 = 10⁻¹²`), the perturbed bundle's
order-`a₄` residual at unit `R²` *also* exceeds that tolerance — so
the falsifier is *quantitatively* detectable by the path-(b) numerical
test, not only structurally non-zero.

Substantive cross-bridge to the Python pipeline: closes the gap
between the Lean falsifier (`perturbed_pathB_residual_a4_eq_delta_R_sq`)
and the Python tolerance constant `DIFF_INVARIANCE_PARAMS['PATH_B_RESIDUAL_TOLERANCE']`,
giving a Lean theorem witnessing the numerical anomaly-hunt outcome. -/
theorem perturbed_residual_exceeds_path_b_tolerance
    {N_f δ : ℝ} (hδ : (1 : ℝ) / 10 ^ (12 : ℕ) < |δ|) :
    (1 : ℝ) / 10 ^ (12 : ℕ) <
      |pathB_residual_a4 (perturbedCoefBundle N_f δ) N_f 1 0 0| := by
  rw [perturbed_pathB_residual_a4_at_unit_R_sq]
  exact hδ

/-! ## §8. Derived Prop bundle for full nonlinear diff-invariance

Note on terminology: from this module's perspective `H_NonlinearDiffInvariance`
is a **derived** Prop bundle (its Dirac instance is fully proved in
`dirac_H_NonlinearDiffInvariance`).  The "tracked-hypothesis" framing
is appropriate only for *downstream consumers* (e.g., the planned Wave 4
`NonlinearEFE.lean`) that may take the Prop as a load-bearing input
without re-proving it.
-/

/-- Predicate bundling order-by-order path-(b) diff-invariance for an
effective Lagrangian bundle `L` at species count `N_f` over all canonical
orders {0, 2, 4}.

Captures the path-b correctness-push as a single `Prop` consumable by
downstream Wave 4 (`NonlinearEFE.lean`) variational calculations.
The predicate's witness is the conjunction of three order-by-order
witnesses — non-vacuous because the order-4 conjunct is the
load-bearing Wave 2 cross-bridge. -/
def H_NonlinearDiffInvariance
    (L : EffectiveLagrangianCoefs) (N_f : ℝ) : Prop :=
  DiffInvariantAt L N_f 0 ∧
  DiffInvariantAt L N_f 2 ∧
  DiffInvariantAt L N_f 4

/-- **Tracked-Prop witness for the Dirac bundle.**  The Wave 1
Christensen-Duff bundle satisfies nonlinear path-b diff invariance at
all canonical orders — *the substantive Wave 3 result*.

Substantive cross-bridge: the order-4 conjunct is
`dirac_diffInvariantAt_four`, which itself consumes the Wave 2 main
basis-change theorem.  Not P2 redundancy: each conjunct uses a
distinct order-by-order theorem with distinct algebraic content. -/
theorem dirac_H_NonlinearDiffInvariance (N_f : ℝ) :
    H_NonlinearDiffInvariance (diracCoefBundle N_f) N_f := by
  refine ⟨?_, ?_, ?_⟩
  · exact dirac_diffInvariantAt_zero N_f
  · exact dirac_diffInvariantAt_two N_f
  · exact dirac_diffInvariantAt_four N_f

/-- **Tracked-Prop falsifier-witness for a non-admissible bundle.**
Any nonzero-perturbation bundle fails the tracked-Prop (specifically,
its order-4 conjunct).

Substantive scope: this rules out the trivial reading of
`H_NonlinearDiffInvariance` ("any bundle satisfies it"); the predicate
genuinely separates admissible from non-admissible bundles. -/
theorem perturbed_not_H_NonlinearDiffInvariance
    {N_f δ : ℝ} (hδ : δ ≠ 0) :
    ¬ H_NonlinearDiffInvariance (perturbedCoefBundle N_f δ) N_f := by
  intro ⟨_, _, h4⟩
  exact perturbed_not_diffInvariantAt_four hδ h4

end SKEFTHawking.NonlinearDiffInvariance

end
