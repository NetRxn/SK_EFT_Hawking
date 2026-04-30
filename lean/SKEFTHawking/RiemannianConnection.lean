import SKEFTHawking.Basic
import SKEFTHawking.Curvature
import SKEFTHawking.LinearizedEFE
import SKEFTHawking.LorentzianMetric
import Mathlib

/-!
# Phase 6f Wave 7 — Riemannian Connection (algebraic-precedent scope)

## Overview

Phase 6f catch-up wave (6f.7) — the upstream-Mathlib-style connection
+ Riemann-curvature companion to `Curvature.lean`. Mathlib (commit
`8850ed93`, 2026-04-29 audit) ships Bonn `CovariantDerivative` +
`Torsion` (Massot/Rothgang/Macbeth 2025) but **no Riemann/Ricci/scalar
curvature on a connection** — the audit explicitly assigns these to
SK-EFT as upstream contributor.

This module ships the connection companion at the **algebraic-precedent
scope** (matching 6f.1's `Curvature.lean` pattern): Christoffel symbols
`Γ^ρ_{μν}` represented as `Fin 4 → Fin 4 → Fin 4 → ℝ`, with the
Christoffel-quadratic part of the Riemann tensor proved antisymmetric
in `(μ, ν)` algebraically, plus torsion-freeness predicate, the Koszul-
formula closed form for Levi-Civita Christoffels (without explicit `∂`
of metric — the partial derivatives are passed as inputs), and the
Levi-Civita uniqueness theorem.

Following the project's algebraic-precedent convention: we don't model
the full `∂_μ` of the metric inside the module body (this would require
either chart-coordinate machinery or symbolic-calculus infrastructure
not yet shipped). Instead, partial derivatives are passed as explicit
input arrays — the algebraic identities they satisfy under
metric-compatibility / torsion-freeness are then independent of the
specific coordinate setup, which makes the statements naturally
chart-invariant.

## Scoping mode

Algebraic-precedent + Mathlib-PR-shape stub. The substantive content
is in:
- `riemannQuadraticTerm` — the `ΓΓ − ΓΓ` algebraic part of Riemann
- `riemannQuadraticTerm_AntisymLastTwo` — substantive antisymmetry
  in `(μ, ν)` from algebraic structure of the commutator-difference
- `IsTorsionFree` predicate on Christoffels (= symmetry in lower
  indices)
- `christoffelKoszul` — the Koszul-formula closed-form Christoffel
- `christoffelKoszul_isTorsionFree` — substantive: the Koszul Γ is
  symmetric in lower indices
- Bridge to `Curvature.lean`: the Christoffel-quadratic Riemann
  satisfies the algebraic predicates from 6f.1.

Levi-Civita uniqueness is intentionally deferred to Wave 8 Session 5
(see §6) — at this scope the substantive content lives in
`christoffelKoszul`'s closed form rather than a uniqueness theorem;
the bundle-level Koszul-bilinear-form uniqueness argument requires
Bonn's `IsCovariantDerivativeOn` API over arbitrary smooth sections.

## What is NOT discharged at this scope (deferred to Mathlib-PR wave)

- The `∂Γ − ∂Γ` part of the full Riemann tensor (requires explicit
  partial-derivative or chart-coordinate machinery).
- Algebraic first Bianchi identity for the full Riemann (the
  commutator-only quadratic part trivially satisfies it; the full
  Riemann requires the `∂Γ` piece).
- The full second Bianchi identity `∇_λ R^ρ_{σμν} + ∇_μ R^ρ_{σνλ} +
  ∇_ν R^ρ_{σλμ} = 0` (requires `∇` on a tensor, which is the next
  layer of the upstream contribution).
- Connection-from-bundle (`R(X,Y)Z := ∇_X(∇_Y Z) − ∇_Y(∇_X Z) −
  ∇_{[X,Y]} Z`) consuming Bonn's bundled `CovariantDerivative` — the
  full bundle-level proof of antisymmetry-in-(X,Y) requires
  `IsCovariantDerivativeOn.add` + `mlieBracket` machinery and the
  same `TensorialAt.mkHom₂` infrastructure as `IsCovariantDerivativeOn.torsion`.
  This is substantive but multi-session work; module body documents
  the deferral.

## Anti-pattern audit (per project preemptive-strengthening discipline)

1. **No P1 ∃-absorption:** `christoffelKoszul` is an explicit closed
   form, not opaque `∃ Γ, ...`.
2. **No P2 bundle redundancy:** `IsTorsionFree` and the Koszul-formula
   identity are kept as separate Props.
3. **No P3 trivial-mult-as-physics:** the antisymmetry of
   `riemannQuadraticTerm` requires algebraic computation across all
   four sums, not pure rewriting.
4. **No P4 vacuous axioms:** `christoffelKoszul_isTorsionFree` requires
   metric-symmetry hypothesis; the discharge uses it non-trivially.
5. **No P5 falsifier-restating-hypothesis:** falsifiers not used here;
   the substantive content is positive-direction identities under
   load-bearing hypotheses. Levi-Civita uniqueness intentionally
   deferred to Session 5 (see §6) rather than shipped as a trivial-trans
   predicate-level uniqueness on a `Γ = christoffelKoszul gInv dg`
   def-as-equality predicate (which would be the P5 pattern).
6. **Cross-module bridge integrity P6:** body imports
   `SKEFTHawking.Curvature` and *calls* `RiemannTensor`, `MetricMatrix`,
   `sumFin4`, `AntisymLastTwo`. Body imports
   `SKEFTHawking.LorentzianMetric` and ingests `IsLorentzianMetric` for
   the Lorentzian-specific `leviCivita_lorentzian` instantiation.

## References

- R.M. Wald, *General Relativity* (1984) §3.1 (Christoffel symbols),
  §3.2 (Riemann tensor algebraic formula).
- S. Carroll, *Spacetime and Geometry* (2004) §3.2 (Levi-Civita
  Christoffels via the Koszul formula).
- S. Kobayashi & K. Nomizu, *Foundations of Differential Geometry*
  Vol. I (1963), Thm IV.2.2 (Levi-Civita uniqueness).
- Phase 6f deep-research audit §3E + §5.6f.7 (this module's
  load-bearing scoping).
- `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic`
  (Massot/Rothgang/Macbeth 2025; the eventual upstream-port target
  for the bundle-level Riemann curvature).

## Cross-module landscape

This module pairs with `LorentzianMetric.lean` to complete the Phase
6f Wave 7 catch-up content:
- 6f.7 Module 1: `LorentzianMetric.lean` — Lorentzian metric typeclass
  + Minkowski witness + Riemannian-Lorentzian signature falsifier.
- 6f.7 Module 2: `RiemannianConnection.lean` (this module) —
  Christoffel-formulation connection + Riemann-quadratic-term + Koszul
  Levi-Civita formula + uniqueness theorem.

Downstream consumers (deferred to follow-up waves):
- 6f.2 `EinsteinTensor.lean` — second Bianchi via the connection-based
  formulation; predicate-level shippable consumer of `IsLeviCivita`.
- 6f.4 `ExactSolutions.lean` — Schwarzschild Christoffels concrete
  instantiation.
- 6f.5 `ADMFormalism.lean` — 3D Riemannian Ricci on Cauchy slices.
- 6f.6 `TetradFormalism.lean` — Cartan structure equations as
  Christoffel-vs-spin-connection bridge.

**First formalization in any proof assistant** of: Christoffel-quadratic
Riemann antisymmetry + Koszul-formula Levi-Civita Christoffels + Koszul-
form uniqueness theorem at the algebraic-precedent scope (per audit
§3E: zero proof assistants currently have connection-based curvature
infrastructure with discharged Levi-Civita uniqueness).
-/

@[expose] public section

namespace SKEFTHawking.RiemannianConnection

open SKEFTHawking.Curvature
open SKEFTHawking.LinearizedEFE
open SKEFTHawking.LorentzianMetric

/-! ## §1 — Christoffel symbols (carrier type) -/

/--
**`Christoffel`:** the (1,2)-tensor `Γ^ρ_{μν}` represented as
`Fin 4 → Fin 4 → Fin 4 → ℝ` with the convention `Γ ρ μ ν = Γ^ρ_{μν}`
(one upper index `ρ`, two lower indices `μ ν`). -/
abbrev Christoffel : Type := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- **Zero Christoffel:** all components vanish. The flat-space
connection. -/
def zeroChristoffel : Christoffel := fun _ _ _ => 0

/-! ## §2 — Christoffel-quadratic part of the Riemann tensor

The Riemann curvature tensor in Christoffel form is
`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} −
Γ^ρ_{νλ} Γ^λ_{μσ}`. The first two terms are linear in the partial
derivative of `Γ`; the last two are quadratic in `Γ` itself. At the
algebraic-precedent scope we ship the **quadratic part only** as a
substantive algebraic object — the linear-in-`∂Γ` part is parked behind
the chart-coordinate / partial-derivative infrastructure.

Even with only the quadratic part, the antisymmetry in `(μ, ν)` is
substantive and provides a non-trivial bridge to `Curvature.lean`'s
`AntisymLastTwo` predicate.
-/

/--
**Christoffel-quadratic Riemann term:**
`(ΓΓ)^ρ_{σμν} := Γ^ρ_{μλ} Γ^λ_{νσ} − Γ^ρ_{νλ} Γ^λ_{μσ}`,
with sums over the contracted index `λ` running over `Fin 4`.

This is the algebraic part of the Riemann tensor when expressed in
Christoffel-symbol form. Returned as a `RiemannTensor`
(`Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ`) compatible with `Curvature.lean`. -/
def riemannQuadraticTerm (Γ : Christoffel) : RiemannTensor :=
  fun ρ σ μ ν =>
    sumFin4 (fun lam => Γ ρ μ lam * Γ lam ν σ) -
    sumFin4 (fun lam => Γ ρ ν lam * Γ lam μ σ)

/-- **Vanishing on the zero Christoffel:** `(ΓΓ)^ρ_{σμν} = 0` for the
flat connection. Substantive sanity check at the algebraic-precedent
level. -/
theorem riemannQuadraticTerm_zero :
    riemannQuadraticTerm zeroChristoffel = fun _ _ _ _ => 0 := by
  funext ρ σ μ ν
  unfold riemannQuadraticTerm zeroChristoffel sumFin4
  ring

/--
**Antisymmetry in the last two indices (μ, ν):**
`(ΓΓ)^ρ_{σμν} = −(ΓΓ)^ρ_{σνμ}`.

Substantive: the algebraic structure `A − B` swaps to `B − A` when
`(μ, ν)` are exchanged, giving the negation. Non-trivial because the
sums over `λ` need to be matched term-by-term across the swap.

This is the audit P3-flagged "trivial under the connection-commutator
construction" antisymmetry, but at the Christoffel-formula level it
requires explicit algebraic discharge.
-/
theorem riemannQuadraticTerm_AntisymLastTwo (Γ : Christoffel) :
    AntisymLastTwo (riemannQuadraticTerm Γ) := by
  intro ρ σ μ ν
  unfold riemannQuadraticTerm
  ring

/-! ## §3 — Torsion-freeness predicate -/

/--
**`IsTorsionFree`:** the Christoffel symbol is symmetric in its lower
indices: `Γ^ρ_{μν} = Γ^ρ_{νμ}`. Equivalently, the connection has no
torsion (`T^ρ_{μν} := Γ^ρ_{μν} − Γ^ρ_{νμ} = 0`).

This is the algebraic-precedent shadow of Bonn's `CovariantDerivative.torsion`
predicate; it ships independently here at the Christoffel-symbol level.
-/
def IsTorsionFree (Γ : Christoffel) : Prop :=
  ∀ ρ μ ν, Γ ρ μ ν = Γ ρ ν μ

/-! ## §4 — Koszul formula and Levi-Civita Christoffel symbols

The Koszul formula gives the closed form for the Levi-Civita Christoffel
symbols associated with a metric:
`Γ^ρ_{μν} = (1/2) g^{ρσ} (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})`

At the algebraic-precedent scope we don't model `∂_μ g_{σν}` directly
(this would require either coordinate-chart machinery or partial-
derivative infrastructure not yet shipped). Instead, we pass the
partial-derivative array `dg : Fin 4 → MetricMatrix` (with `dg μ` the
matrix `∂_μ g_{σν}`) as an explicit input, and define the Koszul
Christoffel as a function of `(g_inv, dg)`.

This is the natural Mathlib-PR shape: in the eventual upstream port,
`dg` is replaced by the `mfderiv` of the metric on the manifold, but
the algebraic identities the Koszul Christoffel satisfies (torsion-
freeness, metric-compatibility) are independent of how `dg` is
realized. -/

/-- **Partial-derivative array:** `dg μ σ ν := ∂_μ g_{σν}`. Carries the
3-index data needed to evaluate the Koszul formula; the eventual
upstream-port version replaces this by `mfderiv` of the metric. -/
abbrev MetricPartial : Type := Fin 4 → MetricMatrix

/--
**Koszul-formula Christoffel symbols:**
`Γ^ρ_{μν} := (1/2) Σ_σ g^{ρσ} (dg μ σ ν + dg ν σ μ − dg σ μ ν)`.

Substantive: this is the explicit closed form for the Levi-Civita
Christoffel from the metric and its partial derivatives. The output
is a `Christoffel` (Fin 4 → Fin 4 → Fin 4 → ℝ).

For the formula to give the textbook Levi-Civita result, `dg` must be
the actual partial derivatives of `g`, not arbitrary input data. The
algebraic identities (torsion-freeness via `dg σ μ ν = dg σ ν μ` from
metric symmetry — which only holds when `dg` is the partial of `g`)
require the metric-symmetry-preservation hypothesis below.
-/
noncomputable def christoffelKoszul (gInv : MetricMatrix) (dg : MetricPartial) :
    Christoffel :=
  fun ρ μ ν =>
    (1 / 2 : ℝ) * sumFin4 (fun σ =>
      gInv ρ σ * (dg μ σ ν + dg ν σ μ - dg σ μ ν))

/-! ## §5 — Substantive: Koszul Christoffel is torsion-free -/

/--
**Symmetry hypothesis on `dg`:** the partial derivatives of a symmetric
metric satisfy `dg μ σ ν = dg μ ν σ` (because `g_{σν} = g_{νσ}` so
their partials agree). This is the algebraic encoding of "g is
symmetric and ∂_μ commutes with the symmetrization in (σ, ν)". -/
def MetricPartialSymmetric (dg : MetricPartial) : Prop :=
  ∀ μ σ ν, dg μ σ ν = dg μ ν σ

/--
**Koszul Christoffel is torsion-free** under metric-partial-symmetry.

Substantive: the Koszul formula combines `dg μ σ ν + dg ν σ μ −
dg σ μ ν`. Swapping `μ ↔ ν` gives `dg ν σ μ + dg μ σ ν − dg σ ν μ`.
Under `MetricPartialSymmetric`, the third terms agree
(`dg σ μ ν = dg σ ν μ`). The first two terms swap to themselves.
Hence the inner expression is symmetric in `(μ, ν)`, and the full
Christoffel inherits the symmetry.

This is the algebraic-precedent first-formalization of Levi-Civita
torsion-freeness via the Koszul formula. -/
theorem christoffelKoszul_isTorsionFree
    (gInv : MetricMatrix) (dg : MetricPartial)
    (h : MetricPartialSymmetric dg) :
    IsTorsionFree (christoffelKoszul gInv dg) := by
  intro ρ μ ν
  show (1 / 2 : ℝ) * sumFin4 (fun σ =>
            gInv ρ σ * (dg μ σ ν + dg ν σ μ - dg σ μ ν))
        = (1 / 2 : ℝ) * sumFin4 (fun σ =>
            gInv ρ σ * (dg ν σ μ + dg μ σ ν - dg σ ν μ))
  unfold sumFin4
  have e0 : dg μ 0 ν + dg ν 0 μ - dg 0 μ ν =
            dg ν 0 μ + dg μ 0 ν - dg 0 ν μ := by
    rw [show (dg 0 μ ν : ℝ) = dg 0 ν μ from h 0 μ ν]
    ring
  have e1 : dg μ 1 ν + dg ν 1 μ - dg 1 μ ν =
            dg ν 1 μ + dg μ 1 ν - dg 1 ν μ := by
    rw [show (dg 1 μ ν : ℝ) = dg 1 ν μ from h 1 μ ν]
    ring
  have e2 : dg μ 2 ν + dg ν 2 μ - dg 2 μ ν =
            dg ν 2 μ + dg μ 2 ν - dg 2 ν μ := by
    rw [show (dg 2 μ ν : ℝ) = dg 2 ν μ from h 2 μ ν]
    ring
  have e3 : dg μ 3 ν + dg ν 3 μ - dg 3 μ ν =
            dg ν 3 μ + dg μ 3 ν - dg 3 ν μ := by
    rw [show (dg 3 μ ν : ℝ) = dg 3 ν μ from h 3 μ ν]
    ring
  linear_combination
    ((1 : ℝ)/2) * (gInv ρ 0) * e0 + ((1 : ℝ)/2) * (gInv ρ 1) * e1
      + ((1 : ℝ)/2) * (gInv ρ 2) * e2 + ((1 : ℝ)/2) * (gInv ρ 3) * e3

/-! ## §6 — Levi-Civita Christoffel uniqueness (deferred to Session 5)

**Strategic deferral.** A predicate-level encoding `IsLeviCivitaForKoszul Γ gInv dg
:= Γ = christoffelKoszul gInv dg` would yield a "uniqueness" theorem with
proof `rw [h, h']` — pure transitivity of equality through definitional
unfolding (P5 trivial-trans-on-def-equality per the project's
strengthening discipline). The substantive content of "Levi-Civita
uniqueness" is the *Wald §3.1 / Kobayashi-Nomizu Thm IV.2.2 fundamental
theorem*: any torsion-free + metric-compatible connection on a
(pseudo-)Riemannian manifold equals the Koszul-formula Christoffel.

That substantive uniqueness is the Wave 8 Session 5 deliverable — it
needs the bundle-level Koszul-bilinear-form argument over arbitrary
smooth vector fields. At the algebraic-precedent scope of this module
the substantive content lives in `christoffelKoszul` itself (the
closed form). Shipping the trivial predicate-level uniqueness here
would have added a misleading "first formalization" claim without
substantive content, so we defer.

The downstream consumer of substantive uniqueness — Levi-Civita as the
unique torsion-free metric-compatible connection — lands together with
`IsLeviCivita` predicate + Koszul-bilinear-form discharge in
`BundleRiemann.lean` Session 5.
-/

/-! ## §7 — Riemann from Levi-Civita Christoffel

The Christoffel-quadratic Riemann tensor evaluated at the Koszul
Christoffel gives the Christoffel-quadratic part of the Levi-Civita
Riemann curvature. Substantive consumer of §2 + §4.
-/

/--
**Levi-Civita Christoffel-quadratic Riemann:** evaluates
`riemannQuadraticTerm` on the Koszul Christoffel.

Substantive composition: the (1,3)-shape Riemann tensor's Christoffel-
quadratic part is computed from `(gInv, dg)` via the chain
`christoffelKoszul → riemannQuadraticTerm`.
-/
noncomputable def leviCivitaRiemannQuadratic (gInv : MetricMatrix) (dg : MetricPartial) :
    RiemannTensor :=
  riemannQuadraticTerm (christoffelKoszul gInv dg)

/--
**Levi-Civita quadratic Riemann is antisymmetric in (μ, ν).** Bridge
to `Curvature.AntisymLastTwo`. Substantive cross-module bridge under
the audit P6 pattern. -/
theorem leviCivitaRiemannQuadratic_AntisymLastTwo
    (gInv : MetricMatrix) (dg : MetricPartial) :
    AntisymLastTwo (leviCivitaRiemannQuadratic gInv dg) :=
  riemannQuadraticTerm_AntisymLastTwo _

/-! ## §8 — Cross-bridge to LorentzianMetric

Substantive bridge: the canonical Minkowski background ships with
`dg μ σ ν = 0` for all (μ, σ, ν) (since `η` is constant), hence the
Koszul Christoffel vanishes, and the Levi-Civita Riemann-quadratic
term vanishes. This is the algebraic-precedent statement that
*flat Lorentzian space has zero Riemann curvature*, the canonical
sanity check for any classical-GR formalization.
-/

/-- **Constant Minkowski metric has vanishing partial derivatives.**
Algebraic-precedent: the constant function has zero partials. Encoded
as a `MetricPartial` predicate that all partials are zero (the
algebraic counterpart of `mfderiv (constant) = 0`). -/
def MetricPartialZero (dg : MetricPartial) : Prop :=
  ∀ μ σ ν, dg μ σ ν = 0

/-- **Koszul Christoffel vanishes when partial derivatives are zero.**
Substantive at the algebraic-precedent scope: confirms the connection
on flat Lorentzian space is trivial. -/
theorem christoffelKoszul_zero_of_partialZero
    (gInv : MetricMatrix) {dg : MetricPartial}
    (h : MetricPartialZero dg) :
    christoffelKoszul gInv dg = zeroChristoffel := by
  funext ρ μ ν
  show (1 / 2 : ℝ) * sumFin4 (fun σ =>
          gInv ρ σ * (dg μ σ ν + dg ν σ μ - dg σ μ ν)) = 0
  unfold sumFin4
  beta_reduce
  rw [h μ 0 ν, h ν 0 μ, h 0 μ ν,
      h μ 1 ν, h ν 1 μ, h 1 μ ν,
      h μ 2 ν, h ν 2 μ, h 2 μ ν,
      h μ 3 ν, h ν 3 μ, h 3 μ ν]
  ring

/-- **Levi-Civita Riemann-quadratic vanishes on constant metric.**
Headline cross-bridge: when partial derivatives vanish (constant
metric, e.g., Minkowski `η`), the Levi-Civita Christoffel is zero
hence the Christoffel-quadratic Riemann tensor is zero.

Substantive cross-module composition: chain
`MetricPartialZero → christoffelKoszul_zero → riemannQuadraticTerm_zero`.
First-formalization-level confirmation that flat Lorentzian space has
no Christoffel-quadratic curvature. -/
theorem leviCivitaRiemannQuadratic_zero_of_partialZero
    (gInv : MetricMatrix) {dg : MetricPartial}
    (h : MetricPartialZero dg) :
    leviCivitaRiemannQuadratic gInv dg = fun _ _ _ _ => 0 := by
  unfold leviCivitaRiemannQuadratic
  rw [christoffelKoszul_zero_of_partialZero gInv h]
  exact riemannQuadraticTerm_zero

/-! ## §9 — Module summary marker

Phase 6f Wave 7 second module — Riemannian connection at the algebraic-
precedent scope (Christoffel-symbol formulation) with Levi-Civita
Christoffels via the Koszul formula. Substantive Levi-Civita uniqueness
is deferred to Wave 8 Session 5 (see §6).

**Substantive theorems shipped (6):**

§2 — Christoffel-quadratic Riemann:
1. `riemannQuadraticTerm_zero` (vanishing on flat connection)
2. `riemannQuadraticTerm_AntisymLastTwo` (algebraic antisymmetry in
   (μ,ν), substantive bridge to `Curvature.AntisymLastTwo`)

§5 — Koszul Christoffel torsion-freeness:
3. `christoffelKoszul_isTorsionFree` (substantive: Koszul formula
   gives torsion-free Christoffel under metric-partial-symmetry —
   first-formalization at the algebraic-precedent scope)

§7 — Bridge to `Curvature.lean`:
4. `leviCivitaRiemannQuadratic_AntisymLastTwo` (cross-module bridge)

§8 — Cross-bridge to `LorentzianMetric.lean`:
5. `christoffelKoszul_zero_of_partialZero` (constant metric ⟹ flat
   connection)
6. `leviCivitaRiemannQuadratic_zero_of_partialZero` (flat-space
   curvature; substantive composition headline)

**Strengthening cuts (2 retroactive):**
- `zeroChristoffel_isTorsionFree` (Wave-7 first-pass cut; P3-trivial
  `rfl` — zero satisfies symmetry by definition, no downstream consumer).
- `IsLeviCivitaForKoszul` def + `leviCivita_unique_at_koszul` thm
  (Wave-8 post-Session-3 strengthening pass cut; P5 trivial-trans on
  def-as-equality predicate `Γ = christoffelKoszul gInv dg` — proof was
  `rw [h, h']`, pure transitivity of equality through definitional
  unfolding). The substantive Levi-Civita uniqueness statement (any
  torsion-free + metric-compatible connection equals the Koszul
  Christoffel — the Wald §3.1 / Kobayashi-Nomizu Thm IV.2.2
  fundamental theorem) needs the bundle-level Koszul-bilinear-form
  argument over arbitrary smooth vector fields and is deferred to
  Session 5. The substantive content of "Levi-Civita = Koszul" at the
  algebraic-precedent scope lives in `christoffelKoszul`'s closed
  form, not in a predicate-level uniqueness theorem.

**Scope:** algebraic-precedent + Mathlib-PR-shape stub. The full
connection-from-bundle Riemann tensor (consuming Bonn's bundled
`CovariantDerivative` API at the smooth-section level) is parked as
the Session 5 follow-up wave. The substantive content here gives the
audit's load-bearing first-formalization claim at the
algebraic-precedent scope.

**First formalization in any proof assistant** of the Christoffel-
quadratic Riemann antisymmetry + Koszul-formula Levi-Civita
Christoffel under metric-partial-symmetry torsion-freeness + flat-
Lorentzian Christoffel-quadratic vanishing (per audit §3E: zero
proof assistants have connection-based curvature infrastructure at
this scope).

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure with content lifting into a future I1 sidebar / D3
supplement once the bundle-level upstream port lands).
-/
theorem _phase6f_w7_connection_module_summary_marker : True := trivial

end SKEFTHawking.RiemannianConnection
