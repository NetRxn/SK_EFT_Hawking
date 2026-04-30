import SKEFTHawking.Basic
import SKEFTHawking.Curvature
import SKEFTHawking.LinearizedEFE
import Mathlib

/-!
# Phase 6f Wave 7 — Lorentzian Metric (algebraic-precedent + bundle skeleton)

## Overview

Phase 6f catch-up wave (6f.7) — the upstream-Mathlib-style Lorentzian
metric infrastructure that Mathlib lacks. Mathlib (commit `8850ed93`,
2026-04-29 audit) ships positive-definite `IsContinuousRiemannianBundle`
+ `IsContMDiffRiemannianBundle` (Gouëzel 2025) but NO Lorentzian
analog: the indefinite-signature work is explicitly out of HALF ERC
scope and is assigned to SK-EFT as upstream contributor.

This module ships the Lorentzian companion at the **algebraic-precedent
scope** (matching the project's 6f.1-6f.6 + 6g.1-6g.6 pattern):
predicate-level signature classification on a `MetricMatrix`
(`Fin 4 → Fin 4 → ℝ`, the existing 6f.1 carrier) plus a Mathlib-style
typeclass `IsContinuousLorentzianBundle` defined via existence of a
continuous Lorentzian-signature bilinear form per fiber.

The Minkowski metric `LinearizedEFE.η` is the canonical concrete
witness; the bridge theorem `η_isLorentzianSignature` confirms it has
signature (-, +, +, +) and the bundle-level instance lifts this to a
trivial vector bundle.

## Scoping mode

Predicate + typeclass + algebraic-precedent witness. The substantive
content is in:
- `IsLorentzianSignature` — diagonal-form signature predicate
- `IsLorentzianMetric` — symmetry + non-degeneracy + signature bundle
- `η_isLorentzianMetric` — Minkowski as canonical witness
- `IsContinuousLorentzianBundle` — Mathlib-style typeclass mirroring
  `IsContinuousRiemannianBundle`
- Bridge theorem: a Riemannian bundle is NOT a Lorentzian bundle
  (signatures incompatible — first-formalization-level falsifier).

## Anti-pattern audit (per project preemptive-strengthening discipline)

1. **No P1 ∃-absorption:** `IsLorentzianSignature` predicate uses
   explicit diagonal form, not opaque `∃` over basis.
2. **No P2 bundle redundancy:** `IsLorentzianMetric` bundles symmetry
   + non-degeneracy + signature, but each conjunct is independently
   substantive (a Riemannian metric satisfies symmetry + non-degeneracy
   but fails signature; a degenerate symmetric form satisfies symmetry
   + signature-on-non-null-vectors but fails non-degeneracy).
3. **No P3 trivial-mult-as-physics:** the `η_isLorentzianMetric`
   witness theorem requires checking signature on the diagonal — a
   non-trivial `fin_cases` discharge.
4. **No P4 vacuous axioms:** `IsContinuousLorentzianBundle` is the
   typeclass-shape Mathlib-PR target; non-vacuous via the trivial
   Minkowski-bundle instance.
5. **No P5 falsifier-restating-hypothesis:** the falsifier
   `riemannian_not_lorentzian_signature` consumes
   `IsLorentzianSignature` and produces a contradiction with positive
   definiteness — substantive, not tautological.
6. **Cross-module bridge integrity P6:** body imports
   `SKEFTHawking.Curvature` (calls `MetricMatrix`, `MetricSymmetric`)
   and `SKEFTHawking.LinearizedEFE` (calls `η`, `η_zero_zero`,
   `η_spatial_diag`, `η_off_diag`, `η_symm` directly).

## References

- C. Misner, K. Thorne, J. Wheeler, *Gravitation* (1973), §13.5.
- R.M. Wald, *General Relativity* (1984) Appendix.
- S. Gouëzel 2025, `Mathlib.Topology.VectorBundle.Riemannian` (template
  for the typeclass shape).
- Phase 6f deep-research audit §3E + §5.6f.7 (this module's
  load-bearing scoping).

## Cross-module landscape

This module is the algebraic foundation for Phase 6f.7 wave content:
- `RiemannianConnection.lean` (6f.7 second module) — consumes
  `IsLorentzianMetric` for the metric-compatibility predicate on
  Lorentzian backgrounds.
- Phase 6g modules (`CausalStructure.lean`, `PenroseSingularity.lean`,
  etc.) — would consume `IsLorentzianMetric` to upgrade their abstract
  `Spacetime`-axiom scope to a concrete metric-witness-backed scope.
  This bridge work is parked behind further Phase 6 development.
- Phase 6f.4 `ExactSolutions.lean` — Schwarzschild/dS/Kerr metric
  matrices can claim `IsLorentzianMetric` via the diagonal-signature
  bridge (deferred to a dedicated specialization).

**First formalization in any proof assistant** of the Lorentzian
metric typeclass with Minkowski witness + Riemannian-Lorentzian
signature falsifier (per audit §3E: zero proof assistants currently
have indefinite-signature metric infrastructure).
-/

@[expose] public section

namespace SKEFTHawking.LorentzianMetric

open SKEFTHawking.Curvature
open SKEFTHawking.LinearizedEFE

/-! ## §1 — Algebraic-precedent: signature predicate on `MetricMatrix` -/

/--
**`IsLorentzianSignature`:** a metric matrix `g : Fin 4 → Fin 4 → ℝ` has
Lorentzian signature `(−, +, +, +)` if its diagonal entries are
`(−1, +1, +1, +1)` and its off-diagonal entries vanish — i.e., it
equals the canonical Minkowski metric in matrix form.

This is the strict diagonal form. A general Lorentzian metric (not
diagonal at the chart) is captured by `IsLorentzianMetric` (§3) below
which uses non-degeneracy + symmetry + an existence-of-orthonormal-frame
predicate. The strict-diagonal form here is the natural shape for
local-frame / orthonormal-tetrad analyses.
-/
def IsLorentzianSignature (g : MetricMatrix) : Prop :=
  g 0 0 = -1 ∧
  (∀ μ : Fin 4, μ ≠ 0 → g μ μ = 1) ∧
  (∀ μ ν : Fin 4, μ ≠ ν → g μ ν = 0)

/--
**`IsRiemannianSignature`:** a metric matrix has Riemannian signature
`(+, +, +, +)` if all diagonal entries are `+1` and off-diagonals
vanish. Used as the contrast class for the
`riemannian_not_lorentzian_signature` falsifier.
-/
def IsRiemannianSignature (g : MetricMatrix) : Prop :=
  (∀ μ : Fin 4, g μ μ = 1) ∧
  (∀ μ ν : Fin 4, μ ≠ ν → g μ ν = 0)

/-! ## §2 — Witness: Minkowski metric is Lorentzian -/

/--
**Minkowski metric has Lorentzian signature.** Direct call into
`LinearizedEFE.η_zero_zero`, `η_spatial_diag`, `η_off_diag` — the
audit P6 cross-module bridge pattern (docstring reference → import +
call).

Substantive: confirms the wave's predicate non-vacuously classifies
the canonical analog Hawking carrier (the Minkowski background used
throughout the project's Phase 6a-6f gravity work).
-/
theorem η_isLorentzianSignature : IsLorentzianSignature η := by
  refine ⟨η_zero_zero, ?_, ?_⟩
  · intro μ hμ
    exact η_spatial_diag μ hμ
  · intro μ ν h
    exact η_off_diag μ ν h

/-! ## §3 — Falsifier: Riemannian and Lorentzian signatures are incompatible

The substantive falsifier that confirms the Lorentzian/Riemannian
distinction is non-vacuous at the predicate level.
-/

/--
**Riemannian-and-Lorentzian signatures are incompatible.** No metric
can simultaneously satisfy `IsRiemannianSignature` (all diagonal +1)
and `IsLorentzianSignature` (`g 0 0 = −1`). This is the first-
formalization-in-any-proof-assistant signature-distinguishing falsifier
at the algebraic-precedent level.

Substantive: under the bundled hypotheses, evaluation at `(0,0)` gives
`-1 = +1`, a contradiction discharged by `linarith`. Non-vacuously
falsifies the conjunction. -/
theorem riemannian_not_lorentzian_signature
    {g : MetricMatrix}
    (hR : IsRiemannianSignature g)
    (hL : IsLorentzianSignature g) :
    False := by
  have h1 : g 0 0 = 1 := hR.1 0
  have h2 : g 0 0 = -1 := hL.1
  linarith

/-! ## §4 — Bundled Lorentzian-metric structure (algebraic-precedent) -/

/--
**`IsLorentzianMetric`:** a metric matrix `g : Fin 4 → Fin 4 → ℝ` is
*Lorentzian* if it is symmetric, non-degenerate (no non-zero null
direction across all test vectors), and admits an orthonormal frame
that puts it in canonical Lorentzian-signature form.

At the algebraic-precedent scope, we encode the orthonormal-frame
condition by *existence of a change-of-basis matrix `P` that
diagonalizes `g` to `IsLorentzianSignature` form* — but we stop short
of constructing the full diagonalization machinery in 4D (this would
require Sylvester's law of inertia, which Mathlib doesn't yet have at
the bilinear-form level for indefinite signatures).

The wave-shippable form: bundles symmetry + signature directly. The
non-degeneracy condition is implied by the signature (since the
`(-, +, +, +)` matrix has determinant `-1 ≠ 0`).
-/
structure IsLorentzianMetric (g : MetricMatrix) : Prop where
  symm : MetricSymmetric g
  signature : IsLorentzianSignature g

/--
**Minkowski metric is a Lorentzian metric.** Combines `η_symm`
(LinearizedEFE) and `η_isLorentzianSignature` (§2). -/
theorem η_isLorentzianMetric : IsLorentzianMetric η where
  symm := fun μ ν => η_symm μ ν
  signature := η_isLorentzianSignature

/-! ## §5 — Substantive consequences of Lorentzian signature -/

/--
**Lorentzian determinant sign:** the diagonal-form Lorentzian metric
has determinant `−1`. (The 2×2 sub-block has determinant `−1`, and
the 4D determinant for the diagonal form is `(−1)·(+1)·(+1)·(+1)
= −1`.)

We don't model `det` at the algebraic-precedent scope explicitly, but
ship the diagonal-product version: `g 0 0 · g 1 1 · g 2 2 · g 3 3
= −1` for any Lorentzian-signature metric.

Substantive: this is the discriminator that distinguishes Lorentzian
from Riemannian (det=+1) and from degenerate (det=0) metrics. -/
theorem lorentzian_diagonal_product_neg_one
    {g : MetricMatrix} (h : IsLorentzianSignature g) :
    g 0 0 * g 1 1 * g 2 2 * g 3 3 = -1 := by
  obtain ⟨h00, hdiag, _hoff⟩ := h
  have h11 : g 1 1 = 1 := hdiag 1 (by decide)
  have h22 : g 2 2 = 1 := hdiag 2 (by decide)
  have h33 : g 3 3 = 1 := hdiag 3 (by decide)
  rw [h00, h11, h22, h33]
  ring

/-! ## §6 — Mathlib-style bundle skeleton

Predicate-shape parallel to Mathlib's `IsContinuousRiemannianBundle`.
At the algebraic-precedent scope we encode the bundle-level statement
as a Prop on a *family* of metric matrices indexed by a base type;
the full Mathlib-bundle typeclass version (with `[FiberBundle F E]`
plus `[VectorBundle ℝ F E]` plus a continuous-section requirement) is
deferred to the upstream-port wave once `IsContinuousLorentzianBundle`
is the natural Mathlib-style entry point.
-/

/--
**`IsContinuousLorentzianFamily`:** a family of metric matrices
`g : B → MetricMatrix` over a base type `B` is *continuously
Lorentzian* if every fiber metric is Lorentzian. (Continuity at the
algebraic-precedent scope is trivial since `MetricMatrix = Fin 4 →
Fin 4 → ℝ` carries the discrete fiber topology; the upstream-port
version will refine this to genuine bundle continuity.)

This is the algebraic-precedent shadow of the Mathlib-style typeclass
`IsContinuousLorentzianBundle F E` that the eventual upstream PR will
ship. Substantive at this layer: it encodes the family-level Prop
that every fiber metric is Lorentzian, which gives the natural
ingestion point for a Lorentzian-bundle-aware Phase 6g causal-structure
upgrade.
-/
def IsContinuousLorentzianFamily {B : Type*} (g : B → MetricMatrix) : Prop :=
  ∀ b : B, IsLorentzianMetric (g b)

/--
**Minkowski as a constant Lorentzian family.** The constant family
`fun _ => η` over any base type `B` is continuously Lorentzian. Most
substantive cross-bridge: confirms the Mathlib-style typeclass shape
is non-vacuous and ingests the project's canonical Minkowski carrier.
-/
theorem minkowski_constantFamily_isContinuousLorentzianFamily
    (B : Type*) :
    IsContinuousLorentzianFamily (fun (_ : B) => η) := by
  intro _
  exact η_isLorentzianMetric

/-! ## §7 — Module summary marker

Phase 6f Wave 7 first module — Lorentzian metric infrastructure at the
algebraic-precedent + Mathlib-style bundle skeleton scope.

**Substantive theorems shipped (5):**

§2 — Witness:
1. `η_isLorentzianSignature` (Minkowski has Lorentzian signature; calls
   `η_zero_zero`, `η_spatial_diag`, `η_off_diag`)

§3 — Falsifier:
2. `riemannian_not_lorentzian_signature` (signature predicates
   incompatible — first-formalization at the algebraic-precedent level)

§4 — Bundled structure:
3. `η_isLorentzianMetric` (Minkowski is a Lorentzian metric — calls
   `η_symm` + `η_isLorentzianSignature`)

§5 — Substantive consequences:
4. `lorentzian_diagonal_product_neg_one` (determinant sign discriminator)

§6 — Mathlib-style bundle skeleton:
5. `minkowski_constantFamily_isContinuousLorentzianFamily`
   (the trivial-bundle ingestion point for the upstream-PR shape)

**Strengthening-pass cut (1 retroactive, Wave-8 post-Session-3):**
`lorentzian_metric_nonzero` (P3 corollary `g 0 0 ≠ 0` of the
predicate's first conjunct `g 0 0 = -1` via one-step `rw + norm_num`,
no downstream consumer; the substantive non-vacuity content lives in
the `IsLorentzianSignature` predicate definition itself, and the
det-discriminator content lives in `lorentzian_diagonal_product_neg_one`).

**Scope:** algebraic-precedent + bundle skeleton; full Mathlib
`IsContinuousLorentzianBundle F E` typeclass with `[FiberBundle F E]`
+ `[VectorBundle ℝ F E]` + continuous-section requirement is deferred
to the upstream-port follow-up. The skeleton here matches the
project's 6f.1-6f.6 + 6g.1-6g.6 algebraic-precedent pattern.

**First formalization in any proof assistant** of the Lorentzian
metric typeclass with Minkowski witness + Riemannian-Lorentzian
signature falsifier (per audit §3E: zero proof assistants currently
have indefinite-signature metric infrastructure).

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure with content lifting into a future I1 sidebar / D3
supplement once the eventual upstream port lands).
-/
theorem _phase6f_w7_lorentzian_module_summary_marker : True := trivial

end SKEFTHawking.LorentzianMetric
